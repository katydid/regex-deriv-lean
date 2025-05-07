import Katydid.Std.Linter.DetectClassical

namespace Predicate

-- φ is the predicate function
-- α is the input to the predicate
-- Bool is the output, since we require that the predicate is decidable, we might as well use Bool.
-- The Predicate needs to be comparable for simplification purposes, via deduplication and sorting via associativity.
class PredLib (α: Type u) (φ: Type) extends Repr φ, Ord φ, BEq φ, LawfulBEq φ where
  eval : φ -> α -> Bool

inductive StdNat where
  | eq (n: Nat): StdNat
  | lt (n: Nat): StdNat
  deriving Ord, DecidableEq, Repr

def evalStdNat (p: StdNat) (x: Nat): Bool :=
  match p with
  | StdNat.eq y => x == y
  | StdNat.lt y => x < y

instance : (PredLib Nat) StdNat where
  eval := evalStdNat

inductive StdChar where
  | eq (c: Char): StdChar
  deriving Ord, DecidableEq, Repr

def evalEqChar (p: StdChar) (x: Char): Bool :=
  match p with
  | StdChar.eq y => x == y

instance : (PredLib Char) StdChar where
  eval := evalEqChar

def evalPred [DecidableEq φ] [PredLib α φ] (p: φ) (x: α): Bool :=
  PredLib.eval p x

#eval evalPred (StdChar.eq 'a') 'b'
#eval evalPred (StdChar.eq 'a') 'a'
#eval evalPred (StdNat.eq 1) 1
#eval evalPred (StdNat.lt 1) 2

inductive Predicate [PredLib α φ] (α: Type u) (φ: Type)  where
  | mk
    (p: φ)
  : Predicate α φ

-- def mkChar (c: Char): Predicate Char StdChar :=
--   Predicate.mk (StdChar.eq c)

-- def Predicate.compare [PredLib α φ] (x y: Predicate α φ): Ordering :=
--   match x with
--   | mk px =>
--   match y with
--   | mk py =>
--   Ord.compare px py

-- instance [PredLib α φ] : Ord (Predicate α φ) where
--   compare (x y: Predicate α φ): Ordering := Predicate.compare x y

-- -- theorem eq_of_val_eq {n:Nat} : ∀{x y : BitVec n}, x.val = y.val → x = y
-- --   | ⟨_,_⟩, _, rfl => rfl

-- -- theorem ne_of_val_ne {x y : BitVec n} (h : x.val ≠ y.val) : x ≠ y :=
-- --   λ h' => absurd (h' ▸ rfl) h

-- -- protected def decideEq : (x y : BitVec n) → Decidable (x = y) :=
-- --   fun ⟨i, _⟩ ⟨j, _⟩ =>
-- --     match decEq i j with
-- --     | isTrue h  => isTrue (eq_of_val_eq h)
-- --     | isFalse h => isFalse (ne_of_val_ne h)

-- theorem eq_of_val_eq : ∀ {x y : Predicate α φ}, x.1 = y.1 → x = y
--   | _, ⟨_, _⟩, rfl => rfl

-- def Predicate.p [PredLib α φ] (x: Predicate α φ): φ :=
--   match x with
--   | mk px => px

-- private def Predicate.decideEq (x y: Predicate α φ) : Decidable (x = y) := by
--   cases x with
--   | mk px =>
--     rename_i lx
--     induction y with
--     | mk py =>
--       rename_i ly
--       cases decEq px py with
--       | isTrue heq =>
--         sorry



--       | isFalse hneq =>

--         sorry

-- instance : DecidableEq (Predicate α φ) := Predicate.decideEq

-- def eval (p: Predicate α φ) (x: α): Bool :=
--   match p with
--   | Predicate.mk p' => PredLib.eval p' x
