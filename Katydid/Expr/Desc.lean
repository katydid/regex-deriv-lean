import Katydid.Std.Lists

/-
We want to represent some nested function calls for a very restricted language, for example:
  and(lt(3, 5), contains("abcd", "bc"))
We represent the description (including AST) of the expr, or as we call it the Descriptor here:
-/

namespace Desc

set_option linter.dupNamespace false
inductive Desc where
  | intro
    (name: String)
    (params: List Desc)
    (hash: UInt64)
    (reader: Bool)
  deriving Repr

def Desc.name (desc: Desc): String :=
  match desc with
  | ⟨ name, _, _, _ ⟩ => name

def Desc.params (desc: Desc): List Desc :=
  match desc with
  | ⟨ _, params, _, _⟩ => params

/-
The `hash` field is important, because it is used to efficiently compare functions calls, so that we can reorder and simplify.  For example:
  * and(lt(3, 5), contains("abcd", "bc")) => and(contains("abcd", "bc"), lt(3, 5))
  * and(lt(3, 5), lt(3, 5)) => lt(3, 5)
  * or(and(lt(3, 5), contains("abcd", "bc")), and(contains("abcd", "bc"), lt(3, 5))) => and(contains("abcd", "bc"), lt(3, 5))
-/
private def hash_list (innit: UInt64) (list: List UInt64): UInt64 :=
  List.foldl (fun acc h => 31 * acc + h) innit list

private def hash_string (s: String): UInt64 :=
  hash_list 0 (List.map (Nat.toUInt64 ∘ Char.toNat) (String.toList s))

private def hash_desc (desc: Desc): UInt64 :=
  match desc with
  | ⟨ name, params, _, _⟩ => hash_list (31 * 17 + hash_string name) (hash_params params)
where hash_params (params: List Desc): List UInt64 :=
  match params with
  | [] => []
  | param::params => hash_desc param :: hash_params params

def Desc.hash (desc: Desc): UInt64 :=
  hash_desc desc

private def any_reader (d: Desc): Bool :=
  match d with
  | ⟨ _, params, _, _⟩ => any_params params
where any_params (params: List Desc): Bool :=
  match params with
  | [] => false
  | param::params => any_reader param || any_params params

/- The reader field tells us whether the function has any variables or can be evaluated at compile time. -/
def Desc.reader (desc: Desc): Bool :=
  any_reader desc

inductive IsSmart : Desc → Prop
  | isSmart: ∀
    (name: String)
    (params: List Desc)
    (hash: UInt64)
    (reader: Bool),
    desc = Desc.intro name params hash reader
    → hash = desc.hash
    → reader = desc.reader
    → (∀ param, param ∈ params → IsSmart param)
    → IsSmart desc

structure SmartDesc where
  subtype: { desc: Desc // IsSmart desc }

def SmartDesc.name (d: SmartDesc): String :=
  d.subtype.val.name

def IsSmartParams (params: List Desc): Prop := ∀ param, param ∈ params → IsSmart param

def conj_is_smart_params {p: Desc} {ps: List Desc} (isSmart: IsSmartParams (p :: ps)):
  IsSmart p /\ IsSmartParams ps :=
  ⟨ isSmart p (List.mem_cons_self _ _), λ p' h => isSmart p' (List.mem_cons_of_mem _ h) ⟩

def cons_is_smart_params (sx: IsSmart x) (sxs: IsSmartParams xs): IsSmartParams (x :: xs) := by
  unfold IsSmartParams
  intro x' inxs
  cases inxs with
  | head => exact sx
  | tail _ inxs =>
    unfold IsSmartParams at sxs
    apply sxs
    exact inxs

def SmartParams := {params: List Desc // IsSmartParams params}

def empty_smart_params: SmartParams := ⟨[], λ p h => False.elim (List.not_mem_nil p h)⟩

def cons_smart_params (sx: SmartDesc) (sxs: SmartParams): SmartParams :=
  match sx.subtype with
  | ⟨ x, xIsSmart ⟩ =>
    match sxs with
    | ⟨ xs, xsIsSmart ⟩ =>
      ⟨ x :: xs , cons_is_smart_params xIsSmart xsIsSmart ⟩

def sparams_to_list (params: List Desc) (isSmartParams: IsSmartParams params): List SmartDesc := by
  cases params with
  | nil => exact []
  | cons p ps =>
    cases conj_is_smart_params isSmartParams with
    | intro pIsSmart psIsSmart =>
      exact ⟨p, pIsSmart⟩ :: sparams_to_list ps psIsSmart

def list_to_sparams (sdecs: List SmartDesc): SmartParams :=
  match sdecs with
  | [] => empty_smart_params
  | x::xs => cons_smart_params x (list_to_sparams xs)

def SmartDesc.params (s: SmartDesc): List SmartDesc := by
  cases s.subtype with
  | mk desc isSmart =>
    refine sparams_to_list desc.params ?_
    cases isSmart with
    | isSmart _ params _ _ descEq _ _ isSmartParams =>
      rw [descEq]
      exact isSmartParams

inductive Forall {α : Type u} (p : α → Prop) : List α → Prop
  | nil  : Forall p ([] : List α)
  | cons : ∀ {x xs}, p x → Forall p xs → Forall p (x :: xs)

def forall_sparams (params: List Desc) (sparams: IsSmartParams params): Forall IsSmart params :=
  match params with
  | [] => Forall.nil
  | _p::ps =>
    let sparams' := conj_is_smart_params sparams
    Forall.cons sparams'.left (forall_sparams ps sparams'.right)

def SmartDesc.hash (d: SmartDesc): UInt64 :=
  -- The hash has been precalculated, so we don't need to recompute it.
  match d.subtype.val with
  | ⟨ _, _, hash, _⟩ => hash

def SmartDesc.reader (d: SmartDesc): Bool :=
  -- The reader has been precalculated, so we don't need to recompute it.
  match d.subtype.val with
  | ⟨ _, _, _, reader⟩ => reader

def hash_with_sparams (name: String) (sparams: List SmartDesc): UInt64 :=
  hash_list (31 * 17 + hash_string name) (List.map SmartDesc.hash sparams)

private def cmp' (x y: Desc): Ordering :=
  match x with
  | ⟨xname, xparams, xhash, _⟩ =>
    match y with
    | ⟨yname, yparams, yhash, _⟩ =>
      let chash := compare xhash yhash
      if chash != Ordering.eq
      then chash
      else
        let cname := compare xname yname
        if cname != Ordering.eq
        then cname
        else cmps' xparams yparams
where cmps' (xs ys : List Desc) : Ordering :=
  match xs, ys with
  | x::xs, y::ys =>
    let r := cmp' x y
    if r != Ordering.eq
    then r
    else cmps' xs ys
  | _, _ => Ordering.eq

def cmp (x y: SmartDesc): Ordering :=
  match x with
  | ⟨xdesc, _ ⟩ =>
    match y with
    | ⟨ydesc, _ ⟩ =>
      cmp' xdesc ydesc

instance : Hashable SmartDesc where
  hash x := x.hash

def SmartDesc.compare := cmp

instance : Ord SmartDesc where
  compare x y := x.compare y

end Desc
