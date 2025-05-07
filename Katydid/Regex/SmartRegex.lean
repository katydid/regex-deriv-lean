import Katydid.Std.Linter.DetectClassical
import Katydid.Std.NonEmptyList

import Katydid.Regex.Language
import Katydid.Regex.Predicate

open List

namespace SmartRegex

inductive Regex (α: Type u) (φ: Type): Type (u + 1) where
  | emptyset : Regex α φ
  | emptystr : Regex α φ
  | any : Regex α φ -- We introduce any, so that we can apply smart constructor rules based on (star any)
  | pred : [Predicate.PredLib α φ] -> (p: φ) -> Regex α φ
  | or : Regex α φ → Regex α φ → Regex α φ
  | concat : Regex α φ → Regex α φ → Regex α φ
  | star : Regex α φ → Regex α φ

def Regex.compare (x y: Regex α φ): Ordering :=
  match x with
  | Regex.emptyset =>
    match y with
    | Regex.emptyset =>
      Ordering.eq
    | _ =>
      Ordering.lt
  | Regex.emptystr =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.eq
    | _ =>
      Ordering.lt
  | Regex.any =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.any =>
      Ordering.eq
    | _ =>
      Ordering.lt
  | Regex.pred p1 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred p2 =>
      Ord.compare p1 p2
    | _ =>
      Ordering.lt
  | Regex.or x1 x2 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred _ =>
      Ordering.gt
    | Regex.or y1 y2 =>
      match Regex.compare x1 y1 with
      | Ordering.eq =>
        Regex.compare x2 y2
      | o => o
    | _ =>
      Ordering.lt
  | Regex.concat x1 x2 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred _ =>
      Ordering.gt
    | Regex.or _ _ =>
      Ordering.gt
    | Regex.concat y1 y2 =>
      match Regex.compare x1 y1 with
      | Ordering.eq =>
        Regex.compare x2 y2
      | o => o
    | _ =>
      Ordering.lt
  | Regex.star x1 =>
    match y with
    | Regex.star y1 =>
      Regex.compare x1 y1
    | _ =>
      Ordering.lt

instance : Ord (Regex α φ) where
  compare (x y: Regex α φ): Ordering := Regex.compare x y

instance : LE (Regex α φ) where
  le x y := (Ord.compare x y).isLE

instance : BEq (Regex α φ) where
  beq x y := Ord.compare x y == Ordering.eq

-- `LawfulBEq α` is a typeclass which asserts that the `BEq α` implementation
-- (which supplies the `a == b` notation) coincides with logical equality `a = b`.
instance : LawfulBEq (Regex α φ) where
  -- {a b : α} → a == b → a = b
  eq_of_beq {x y} h := by
    induction x <;> induction y <;> (try (first | rfl | contradiction))
    case pred =>
      sorry
    case concat =>
      sorry
    case or =>
      sorry
    case star =>
      sorry
  -- {a : α} → a == a
  rfl {x} := by
    induction x <;> try rfl
    case pred =>
      sorry
    case concat =>
      sorry
    case or =>
      sorry
    case star =>
      sorry

def Regex.le (x y: Regex α φ): Bool :=
  x <= y

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α φ): Regex α φ :=
  if cond then r else Regex.emptyset

def onlyif' {cond: Prop} (dcond: Decidable cond) (r: Regex α φ): Regex α φ :=
  if cond then r else Regex.emptyset

def denote {α: Type} (r: Regex α φ): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.any => Language.any
  | Regex.pred p => Language.predicate (Predicate.PredLib.eval p)
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

def null (r: Regex α φ): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.any => false
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

-- copy of SimpleRegex.null_commutes
theorem null_commutes {α: Type} (r: Regex α φ):
  ((null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | any =>
    unfold denote
    rw [Language.null_any]
    unfold null
    simp only [Bool.false_eq_true]
  | pred p =>
    unfold denote
    rw [Language.null_predicate]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold null
    simp only

-- smartStar is a smart constructor for Regex.star which incorporates the following simplification rules:
-- 1. star (star x) = star x (Language.simp_star_star_is_star)
-- 2. star emptystr = emptystr (Language.simp_star_emptystr_is_emptystr)
-- 3. star emptyset = emptystr (Language.simp_star_emptyset_is_emptystr)
def smartStar (x: Regex α φ): Regex α φ :=
  match x with
  | Regex.emptyset => Regex.emptystr
  | Regex.emptystr => Regex.emptystr
  | Regex.star _ => x
  | _ => Regex.star x

theorem smartStar_is_star (x: Regex α φ):
  denote (Regex.star x) = denote (smartStar x) := by
  cases x with
  | emptyset =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptyset_is_emptystr]
  | emptystr =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptystr_is_emptystr]
  | any =>
    simp only [smartStar]
  | pred p =>
    simp only [smartStar]
  | concat x1 x2 =>
    simp only [smartStar]
  | or x1 x2 =>
    simp only [smartStar]
  | star x' =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_star_is_star]

-- smartConcat is a smart constructor for Regex.concat that includes the following simplification rules:
-- 1. If x or y is emptyset then return emptyset (Language.simp_concat_emptyset_l_is_emptyset and Language.simp_concat_emptyset_r_is_emptyset)
-- 2. If x or y is emptystr return the other (Language.simp_concat_emptystr_r_is_l and Language.simp_concat_emptystr_l_is_r)
-- 3. If x is a concat then `((concat x1 x2) y) = concat x1 (concat x2 y)` use associativity (Language.simp_concat_assoc).
def smartConcat (x y: Regex α φ): Regex α φ :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => y
  | Regex.concat x1 x2 =>
      -- smartConcat needs to be called again on the rigth hand side, since x2 might also be a Regex.concat.
      -- x1 is gauranteed to not be a Regex.concat if it has been constructed with smartConcat, so we do not called smartConcat again on the left hand side.
      Regex.concat x1 (smartConcat x2 y)
  | _otherwise =>
      match y with
      | Regex.emptyset => Regex.emptyset
      | Regex.emptystr => x
      | _otherwise => Regex.concat x y

theorem smartConcat_is_concat {α: Type} (x y: Regex α φ):
  denote (Regex.concat x y) = denote (smartConcat x y) := by
  cases x with
  | emptyset =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptyset_l_is_emptyset (denote y)
  | emptystr =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptystr_l_is_r (denote y)
  | any =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | pred p =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | or x1 x2 =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | concat x1 x2 =>
    unfold smartConcat
    simp only [denote]
    rw [<- smartConcat_is_concat x2 y]
    simp only [denote]
    rw [Language.simp_concat_assoc]
  | star x1 =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l

def orToList (x: Regex α φ): List (Regex α φ) :=
  match x with
  | Regex.or x1 x2 =>
    -- smartOr guarantees that left hand side will not be an Regex.or so a recursive call is only required on the right hand side.
    x1 :: (orToList x2)
  | _ =>
    [x]

def orFromList (xs: List (Regex α φ)): Regex α φ :=
  match xs with
  | [] => Regex.emptyset
  | [x1] => x1
  | (x1::xs') => Regex.or x1 (orFromList xs')

theorem orToList_is_orFromList (x: Regex α φ):
  orFromList (orToList x) = x := by
  induction x with
  | emptyset =>
    simp only [orToList, orFromList]
  | emptystr =>
    simp only [orToList, orFromList]
  | any =>
    simp only [orToList, orFromList]
  | pred _ =>
    simp only [orToList, orFromList]
  | or x1 x2 ih1 ih2 =>
    simp only [orToList, orFromList]
    cases x2 with
    | or x21 x22 =>
      simp only [orToList, orFromList]
      congr
    | _ =>
      simp only [orToList, orFromList]
  | concat x1 x2 =>
    simp only [orToList, orFromList]
  | star x1 =>
    simp only [orToList, orFromList]

def orToNonEmptyList (x: Regex α φ): NonEmptyList (Regex α φ) :=
  match x with
  | Regex.or x1 x2 =>
    -- smartOr guarantees that left hand side will not be an Regex.or so a recursive call is only required on the right hand side.
    NonEmptyList.cons x1 (orToNonEmptyList x2)
  | _ =>
    NonEmptyList.mk x []

private def orFromNonEmptyList' (x1: Regex α φ) (xs: List (Regex α φ)): Regex α φ :=
  match xs with
  | [] => x1
  | (x2::xs') => Regex.or x1 (orFromNonEmptyList' x2 xs')

def orFromNonEmptyList (xs: NonEmptyList (Regex α φ)): Regex α φ :=
  match xs with
  | NonEmptyList.mk x1 xs' => orFromNonEmptyList' x1 xs'

theorem orToNonEmptyList_is_orFromNonEmptyList (x: Regex α φ):
  orFromNonEmptyList (orToNonEmptyList x) = x := by
  induction x <;> (try simp only [orToNonEmptyList, orFromNonEmptyList, orFromNonEmptyList'])
  · case or x1 x2 ih1 ih2 =>
    rw [NonEmptyList.cons_head]
    congr

theorem simp_star_pred_any_is_universal {α: Type} {φ: Type}:
  denote (Regex.star (@Regex.any α φ)) = Language.universal := by
  unfold denote
  exact Language.simp_star_any_is_universal

theorem simp_or_universal_r_is_universal [Ord α] (x: Regex α φ):
  denote (Regex.or x (Regex.star Regex.any)) = Language.universal := by
  nth_rewrite 1 [denote]
  rw [simp_star_pred_any_is_universal]
  rw [Language.simp_or_universal_r_is_universal]

theorem simp_or_universal_l_is_universal [Ord α] (x: Regex α φ):
  denote (Regex.or (Regex.star Regex.any) x) = Language.universal := by
  nth_rewrite 1 [denote]
  rw [simp_star_pred_any_is_universal]
  rw [Language.simp_or_universal_l_is_universal]

-- 1. If x or y is emptyset then return the other (Language.simp_or_emptyset_r_is_l and Language.simp_or_emptyset_l_is_r)
-- 2. If x or y is star (any) then return star (any) (Language.simp_or_universal_r_is_universal and Language.simp_or_universal_l_is_universal)
-- 3. Get the lists of ors using orToNonEmptyList (Language.simp_or_assoc)
-- 4. Merge sort the sorrted lists (Language.simp_or_comm and Language.simp_or_assoc)
-- 5. Remove duplicates from the list (or create a set) (Language.simp_or_idemp)
-- 6. If at any following step the set is size one, simply return
-- TODO: 7. If any of the set is nullable, remove emptystr from the set (Language.simp_or_emptystr_null_r_is_r and Language.simp_or_null_l_emptystr_is_l)
-- 8. Reconstruct Regex.or from the list using orFromNonEmptyList (Language.simp_or_assoc)
def smartOr (x y: Regex α φ): Regex α φ :=
  match x with
  | Regex.emptyset => y
  | Regex.star Regex.any => x
  | _ =>
  match y with
  | Regex.emptyset => x
  | Regex.star Regex.any => y
  | _ =>
    let xs := orToList x
    let ys := orToList y
    -- It is implied that xs is sorted, given it was created using smartOr.
    -- Merge the sorted lists and remove duplicates, resulting in a sorted list of unique items.
    let ors := Lists.mergeReps xs ys
    orFromList ors

private lemma smartOr_emptyset_l_is_r (x: Regex α φ):
  denote (Regex.or Regex.emptyset x) = denote (smartOr Regex.emptyset x) := by
  simp only [smartOr]
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_l_is_r]

private lemma smartOr_emptyset_r_is_l':
  smartOr x Regex.emptyset = x := by
  simp only [smartOr]
  split <;> rfl

private lemma smartOr_emptyset_r_is_l (x: Regex α φ):
  denote (Regex.or x Regex.emptyset) = denote (smartOr x Regex.emptyset) := by
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_r_is_l]
  rw [smartOr_emptyset_r_is_l']

private lemma smartOr_orFromList_mergeReps_orToList_is_or'_nil:
  denote ((orFromList []).or (orFromList ys)) = denote (orFromList ys) := by
  nth_rewrite 1 [orFromList]
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_l_is_r]

private lemma smartOr_orFromList_mergeReps_orToList_is_or'_nil_r:
  denote ((orFromList xs).or (orFromList [])) = denote (orFromList xs) := by
  nth_rewrite 1 [orFromList]
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_r_is_l]

private lemma lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp (x: Regex α φ) (xs: List (Regex α φ)):
  denote (orFromList (x :: xs)) = Language.or (denote x) (denote (orFromList xs)) := by
  induction xs with
  | nil =>
    unfold orFromList
    rw [denote]
    rw [Language.simp_or_emptyset_r_is_l]
  | cons x' xs' ih =>
    nth_rewrite 1 [orFromList]
    rw [denote]
    intro h
    contradiction

private lemma smartOr_orFromList_mergeReps_orToList_is_or'_idemp_eraseReps (xs: List (Regex α φ)):
  denote (orFromList (Lists.eraseReps xs)) = denote (orFromList xs) := by
  induction xs with
  | nil =>
    unfold Lists.eraseReps
    rfl
  | cons x1 xs1 ih =>
    unfold Lists.eraseReps
    cases xs1 with
    | nil =>
      simp only
    | cons x2 xs2 =>
      simp only
      split_ifs
      case neg h =>
        rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
        rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
        rw [ih]
      case pos h =>
          rw [ih]
          rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
          rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
          rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
          simp only [beq_iff_eq] at h
          rw [h]
          ac_rfl

private lemma smartOr_orFromList_cons (x: Regex α φ) (xs ys: List (Regex α φ)):
  denote (Regex.or (orFromList (x :: xs)) (orFromList ys)) = Language.or (denote x) (denote (Regex.or (orFromList xs) (orFromList ys))) := by
  induction xs generalizing x with
  | nil =>
    repeat rw [orFromList]
    repeat rw [denote]
    rw [Language.simp_or_emptyset_l_is_r]
  | cons x1 xs1 ih =>
    rw [orFromList]
    rw [denote]
    rw [denote]
    rw [denote] at ih
    rw [Language.simp_or_assoc]
    rw [ih x1]
    apply congrArg
    rw [<- denote]
    rw [ih x1]
    intro h
    contradiction

private lemma smartOr_orFromList_mergeReps_orToList_is_or'_step (x': Regex α φ) (xs' ys: List (Regex α φ)):
  denote (orFromList (Lists.mergeReps (x' :: xs') ys)) =
    Language.or (denote x') (denote (orFromList (Lists.mergeReps xs' ys))) := by
  induction ys with
  | nil =>
    rw [list_mergeReps_nil_r]
    rw [smartOr_orFromList_mergeReps_orToList_is_or'_idemp_eraseReps]
    rw [list_mergeReps_nil_r]
    rw [lemmasmartOr_orFromList_mergeReps_orToList_is_or'_idemp]
    rw [smartOr_orFromList_mergeReps_orToList_is_or'_idemp_eraseReps]
  | cons y' ys' ih =>
    nth_rewrite 1 [Lists.mergeReps]
    nth_rewrite 1 [Lists.merge]
    nth_rewrite 1 [List.merge]
    split_ifs
    case pos leq =>
      unfold Lists.eraseReps


    case neg gt =>
      sorry


private lemma smartOr_orFromList_mergeReps_orToList_is_or' (xs ys: List (Regex α φ)):
  denote (orFromList (Lists.mergeReps xs ys)) = denote (Regex.or (orFromList xs) (orFromList ys)) := by
  induction xs with
  | nil =>
    rw [smartOr_orFromList_mergeReps_orToList_is_or'_nil]
    rw [list_mergeReps_nil_l]
    rw [smartOr_orFromList_mergeReps_orToList_is_or'_idemp_eraseReps]
  | cons x xs' ih =>
    rw [smartOr_orFromList_cons]
    rw [<- ih]
    rw [smartOr_orFromList_mergeReps_orToList_is_or'_step]

private lemma smartOr_orFromList_mergeReps_orToList_is_or (x y: Regex α φ):
  denote (orFromList (Lists.mergeReps (orToList x) (orToList y))) = denote (Regex.or x y) := by
  rw [smartOr_orFromList_mergeReps_orToList_is_or']
  rw [orToList_is_orFromList]
  rw [orToList_is_orFromList]

private lemma smartOr_orFromNonEmptyList_mergeReps_orToNonEmptyList_is_or' (xs ys: NonEmptyList (Regex α φ)):
  denote (orFromNonEmptyList (NonEmptyList.mergeReps xs ys)) = denote (Regex.or (orFromNonEmptyList xs) (orFromNonEmptyList ys)) := by
  sorry

private lemma smartOr_orFromNonEmptyList_mergeReps_orToNonEmptyList_is_or (x y: Regex α φ):
  denote (orFromNonEmptyList (NonEmptyList.mergeReps (orToNonEmptyList x) (orToNonEmptyList y))) = denote (Regex.or x y) := by
  rw [smartOr_orFromNonEmptyList_mergeReps_orToNonEmptyList_is_or']
  rw [orToNonEmptyList_is_orFromNonEmptyList]
  rw [orToNonEmptyList_is_orFromNonEmptyList]

lemma simp_or_x_star_any_is_star_any {x: Regex α φ}:
  denote (Regex.or x (Regex.star Regex.any)) = denote (Regex.star (@Regex.any α φ)) := by
  unfold denote
  unfold denote
  unfold denote
  rw [Language.simp_star_any_is_universal]
  rw [Language.simp_or_universal_r_is_universal]

lemma simp_or_star_any_x_is_star_any {x: Regex α φ}:
  denote (Regex.or (Regex.star Regex.any) x) = denote (Regex.star (@Regex.any α φ)) := by
  unfold denote
  unfold denote
  unfold denote
  rw [Language.simp_star_any_is_universal]
  rw [Language.simp_or_universal_l_is_universal]

private lemma smartOr_emptystr_is_or (y: Regex α φ):
  denote (Regex.or Regex.emptystr y) = denote (smartOr Regex.emptystr y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_any_is_or (y: Regex α φ):
  denote (Regex.or Regex.any y) = denote (smartOr Regex.any y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_pred_is_or [Predicate.PredLib α φ] (p: φ) (y: Regex α φ):
  denote (Regex.or (Regex.pred p) y) = denote (smartOr (Regex.pred p) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_star_is_or (x y: Regex α φ):
  denote (Regex.or (Regex.star x) y) = denote (smartOr (Regex.star x) y) := by
  cases x with
  | any =>
    simp only [smartOr]
    rw [simp_or_star_any_x_is_star_any]
  | _ =>
    cases y with
    | emptyset =>
      rw [smartOr_emptyset_r_is_l]
    | star y1 =>
      cases y1 with
      | any =>
        simp only [smartOr]
        rw [simp_or_x_star_any_is_star_any]
      | _ =>
        simp only [smartOr]
        rw [smartOr_orFromList_mergeReps_orToList_is_or]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_concat_is_or (x1 x2 y: Regex α φ):
  denote (Regex.or (Regex.concat x1 x2) y) = denote (smartOr (Regex.concat x1 x2) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_or_is_or (x1 x2 y: Regex α φ):
  denote (Regex.or (Regex.or x1 x2) y) = denote (smartOr (Regex.or x1 x2) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

theorem smartOr_is_or (x y: Regex α φ):
  denote (Regex.or x y) = denote (smartOr x y) := by
  induction x with
  | emptyset =>
    apply smartOr_emptyset_l_is_r
  | emptystr =>
    apply smartOr_emptystr_is_or
  | any =>
    apply smartOr_any_is_or
  | pred p =>
    apply smartOr_pred_is_or
  | or x1 x2 ih1 ih2 =>
    apply smartOr_or_is_or
  | concat x1 x2 =>
    apply smartOr_concat_is_or
  | star x1 =>
    apply smartOr_star_is_or

def derive (r: Regex α φ) (a: α): Regex α φ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.any => Regex.emptystr
  | Regex.pred (@Predicate.mk _ _ _ decfunc) => onlyif' (decfunc a) Regex.emptystr
  | Regex.or x y =>
      SmartRegex.smartOr (derive x a) (derive y a)
  | Regex.concat x y =>
      SmartRegex.smartOr
        (SmartRegex.smartConcat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      SmartRegex.smartConcat (derive x a) (Regex.star x)

lemma derive_commutes_emptyset {x: α}:
  denote (derive (@Regex.emptyset α φ) x) = Language.derive (denote (@Regex.emptyset α φ)) x := by
  funext xs
  simp only [denote, Language.emptyset, Language.derive, Language.derives]

lemma derive_commutes_emptystr {x: α}:
  denote (derive (@Regex.emptyset α φ) x) = Language.derive (denote (@Regex.emptyset α φ)) x := by
  funext xs
  simp only [
    denote,
    Language.emptyset, Language.derive, Language.derives, Language.emptystr,
    singleton_append,
    reduceCtorEq,
  ]

lemma derive_commutes_any {x: α}:
  denote (derive (@Regex.any α φ) x) = Language.derive (denote (@Regex.any α φ)) x := by
  funext xs
  unfold derive
  unfold denote
  unfold Language.any
  simp only [Language.emptystr, Language.derive, Language.derives, singleton_append, cons.injEq,
    exists_and_right, exists_eq', true_and]

lemma derive_commutes_pred [Predicate.PredLib α φ] {p: φ} {x: α}:
  denote (derive (Regex.pred p) x) = Language.derive (denote (Regex.pred p)) x := by
  funext xs
  cases p with
  | @mk _ pred decidablePred =>
    simp only [derive, Language.derive, Language.derives, denote, singleton_append, eq_iff_iff]
    rw [onlyif', Language.pred]
    split_ifs with h
    · rw [denote]
      simp only [Language.emptystr, cons.injEq]
      apply Iff.intro
      · intro hxs
        use x
      · intro ⟨w, hxs, hp⟩
        exact hxs.right
    · rw [denote]
      simp only [Language.emptyset, cons.injEq, false_iff, not_exists, not_and, and_imp, forall_eq']
      intro _ h'
      contradiction

lemma derive_commutes_or {r1 r2: Regex α φ} {x: α}
  (ih1: denote (derive r1 x) = Language.derive (denote r1) x)
  (ih2: denote (derive r2 x) = Language.derive (denote r2) x):
  denote (derive (Regex.or r1 r2) x) = Language.derive (denote (r1.or r2)) x := by
  funext xs
  simp only [derive, Language.derive, Language.derives, denote, Language.or, singleton_append,
    eq_iff_iff]
  rw [←smartOr_is_or, denote, Language.or]
  rw [ih1, ih2]
  rfl

lemma derive_commutes_concat {r1 r2: Regex α φ} {x: α}
  (ih1 : denote (derive r1 x) = Language.derive (denote r1) x)
  (ih2 : denote (derive r2 x) = Language.derive (denote r2) x):
  denote (derive (r1.concat r2) x) = Language.derive (denote (r1.concat r2)) x := by
  funext xs
  simp [derive, denote]
  rw [←smartOr_is_or, denote, Language.or]
  rw [←smartConcat_is_concat]
  simp only [denote, Language.concat, exists_and_left]
  apply Iff.intro
  · intro h
    match h with
    | Or.inl ⟨ys, h, zs, h', hxs⟩ =>
      rw [ih1] at h
      rw [Language.derive, Language.derives, singleton_append] at h
      refine ⟨x::ys, h, zs, h', ?_⟩
      rw [hxs, cons_append]
    | Or.inr h =>
      rw [onlyif] at h
      split_ifs at h with hn
      · rw [null_commutes, Language.null] at hn
        rw [ih2] at h
        rw [Language.derive, Language.derives, singleton_append] at h
        refine ⟨[], hn, x::xs, h, ?_⟩
        rw [nil_append]
      · simp only [denote, Language.emptyset] at h
  · intro ⟨ys, h, zs, h', hxs⟩
    rw [ih1]
    simp only [Language.derive, Language.derives, singleton_append]
    cases ys with
    | nil =>
      rw [nil_append] at hxs
      rw [onlyif]
      split_ifs with hn
      · rw [ih2]
        rw [Language.derive, Language.derives, singleton_append, hxs]
        exact Or.inr h'
      · rw [null_commutes, Language.null] at hn
        contradiction
    | cons w ws =>
      rw [cons_append, cons.injEq] at hxs
      rw [hxs.left]
      exact Or.inl ⟨ws, h, zs, h', hxs.right⟩

lemma derive_commutes_star {r: Regex α φ} {x: α}
  (ih : denote (derive r x) = Language.derive (denote r) x):
  denote (derive r.star x) = Language.derive (denote r.star) x := by
  funext xs
  simp [derive, denote]
  rw [←smartConcat_is_concat]
  simp only [denote, Language.concat, exists_and_left]
  apply Iff.intro
  · intro ⟨ys, h, zs, h', hxs⟩
    rw [ih] at h
    rw [Language.derive, Language.derives, singleton_append] at h
    apply Language.star.more x ys zs
    rw [hxs, cons_append]
    exact h
    exact h'
  · intro h
    cases h with
    | more y ys zs _ hxs h h'  =>
      rw [cons_append, cons.injEq] at hxs
      rw [ih, hxs.left]
      exact ⟨ys, h, zs, h', hxs.right⟩

theorem derive_commutes {α: Type} (r: Regex α φ) (x: α):
  denote (derive r x) = Language.derive (denote r) x := by
  induction r with
  | emptyset =>
    exact derive_commutes_emptyset
  | emptystr =>
    exact derive_commutes_emptystr
  | any =>
    exact derive_commutes_any
  | pred p =>
    exact derive_commutes_pred
  | or r1 r2 ih1 ih2 =>
    exact derive_commutes_or ih1 ih2
  | concat r1 r2 ih1 ih2 =>
    exact derive_commutes_concat ih1 ih2
  | star r ih =>
    exact derive_commutes_star ih

def derives (r: Regex α φ) (xs: List α): Regex α φ :=
  (List.foldl derive r) xs

-- copy of SimpleRegex.derives_commutes
theorem derives_commutes {α: Type} (r: Regex α φ) (xs: List α):
  denote (derives r xs) = Language.derives (denote r) xs := by
  unfold derives
  rw [Language.derives_foldl]
  revert r
  induction xs with
  | nil =>
    simp only [foldl_nil]
    intro h
    exact True.intro
  | cons x xs ih =>
    simp only [foldl_cons]
    intro r
    have h := derive_commutes r x
    have ih' := ih (derive r x)
    rw [h] at ih'
    exact ih'

def validate (r: Regex α φ) (xs: List α): Bool :=
  null (derives r xs)

-- copy of SimpleRegex.validate_commutes
theorem validate_commutes {α: Type} (r: Regex α φ) (xs: List α):
  (validate r xs = true) = (denote r) xs := by
  rw [<- Language.validate (denote r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- copy of SimpleRegex.decidableDenote
def decidableDenote (r: Regex α φ): DecidablePred (denote r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes r xs)
