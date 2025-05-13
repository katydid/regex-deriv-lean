import Katydid.Std.Ordering

namespace Predicate

inductive Pred (α: Type u): Type (u + 1) where
  | eq (x: α): Pred α
  | lt (x: α): Pred α
  | le (x: α): Pred α
  | gt (x: α): Pred α
  | ge (x: α): Pred α
  | and (p1 p2: Pred α): Pred α
  deriving Ord, DecidableEq, Repr

def Pred.eval {α: Type u} [Ord α] (p: Pred α) (x: α): Prop :=
  match p with
  | Pred.eq y => x = y
  | Pred.lt y => Ord.compare x y = Ordering.lt
  | Pred.le y => (Ord.compare x y).isLE
  | Pred.gt y => Ord.compare x y = Ordering.gt
  | Pred.ge y => (Ord.compare x y).isGE
  | Pred.and p1 p2 => Pred.eval p1 x /\ Pred.eval p2 x

-- Test that instances of recursively inferred:
instance inst_pred_ord {α: Type u} [Ord α]: Ord (Pred α) := inferInstance
instance inst_pred_deq {α: Type u} [DecidableEq α]: DecidableEq (Pred α) := inferInstance
instance inst_pred_repr {α: Type u} [Repr α]: Repr (Pred α) := inferInstance

def pred_is_decpred {α : Type u} [d: DecidableEq α] [o: Ord α] (p: Pred α): (a: α) -> Decidable (Pred.eval p a) :=
  fun x =>
  match p with
  | Pred.eq y => d x y
  | Pred.lt y => Ordering.compare_is_decidable_eq x y Ordering.lt
  | Pred.le y => Ordering.compare_isle_is_decidable x y
  | Pred.gt y => Ordering.compare_is_decidable_eq x y Ordering.gt
  | Pred.ge y => Ordering.compare_isge_is_decidable x y
  | Pred.and y1 y2 => by
    unfold Pred.eval
    have h1 : DecidablePred (Pred.eval y1) := pred_is_decpred y1
    have h2 : DecidablePred (Pred.eval y2) := pred_is_decpred y2
    infer_instance

def Pred.decidableEval {α: Type u} [Ord α] [d: DecidableEq α] (p: Pred α) : DecidablePred p.eval :=
  pred_is_decpred p

instance inst_pred_decpred {α: Type u} [d: DecidableEq α] [o: Ord α] (p: Pred α): DecidablePred p.eval :=
  p.decidableEval

-- Test several predicates
example : Pred.eval (Pred.eq 1) 1 = true := by simp [Pred.eval]
example : Pred.eval (Pred.eq 2) 1 = false := by simp [Pred.eval, Nat.reduceEqDiff, Bool.false_eq_true]
def isUpperCase: Pred Char := Pred.and (Pred.ge 'A') (Pred.le 'Z')
example : Pred.eval isUpperCase 'A' = true := by simp [isUpperCase, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]
example : Pred.eval isUpperCase 'a' = false := by simp [isUpperCase, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]
example : Pred.eval isUpperCase 'U' = true := by simp [isUpperCase, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]

-- Test that LawfulBEq is inferred for our specific inductive type
instance inst_pred_lbeq {α: Type u} [DecidableEq (Pred α)]: LawfulBEq (Pred α) := inferInstance

-- Test that BEq is inferred for our specific inductive type
instance inst_pred_beq {α: Type u} [DecidableEq (Pred α)]: BEq (Pred α) := inferInstance

def Pred.eq_of_beq {α: Type u} {a b : Pred α} [d: DecidableEq (Pred α)]
  (heq: a == b): a = b := of_decide_eq_true heq

def Pred.eq_of_beq' {α: Type u} {a b : Pred α} [d: DecidableEq (Pred α)] (heq: a == b): a = b := by
  refine @of_decide_eq_true (a = b) (d a b) heq

def Pred.rfl {α: Type u} {a : Pred α} [d: DecidableEq (Pred α)]: a == a := of_decide_eq_self_eq_true a

instance inst_deq_lbeq {α: Type u} [DecidableEq (Pred α)]: LawfulBEq (Pred α) where
  eq_of_beq : {a b : Pred α} → a == b → a = b := Pred.eq_of_beq
  rfl : {a : Pred α} → a == a := Pred.rfl

class Predicate (α: Type u) (φ: Type v) extends Ord φ, BEq φ, LawfulBEq φ where
  eval (p: φ): α -> Prop
  decidableEval (p: φ): DecidablePred (eval p)

instance {α: Type u} [o: Ord α] [da: DecidableEq α] [dp: DecidableEq (Pred α)]: Predicate α (Pred α) where
  eval := Pred.eval
  decidableEval := pred_is_decpred
  eq_of_beq {a b : Pred α} (heq: a == b): a = b := @Pred.eq_of_beq α a b dp heq
  rfl : {a : Pred α} → a == a := Pred.rfl

-- Test that we can compare Predicates, without implementing Ord
example [Predicate α φ] (x y: φ): Ordering :=
  Ord.compare x y

-- Test several Predicate examples
instance : Predicate Nat (Pred Nat) where eval := Pred.eval; decidableEval := pred_is_decpred
instance : Predicate Char (Pred Char) where eval := Pred.eval; decidableEval := pred_is_decpred
def isLowerCase: Pred Char := Pred.and (Pred.ge 'a') (Pred.le 'z')
example : Predicate.eval isLowerCase 'A' = false := by simp [isLowerCase, Predicate.eval, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]
example : Predicate.eval isLowerCase 'a' = true := by simp [isLowerCase, Predicate.eval, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]
example : Predicate.eval isLowerCase 'l' = true := by simp [isLowerCase, Predicate.eval, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]

-- Test that we can evaluate a Predicate via a generic function based on the class and not a specific instance
private def evalPredicate {α: Type u} {φ: Type v} [instPredicate: Predicate α φ] (p: φ) (a: α): Prop := instPredicate.eval p a
example : evalPredicate isLowerCase 'l' = true := by simp [isLowerCase, evalPredicate, Predicate.eval, Pred.eval, compare, compareOfLessAndEq, Ordering.isGE, Ordering.isLE]

-- Test that a Predicate is evaluatable to a Bool
private def evalDecPredicate {α: Type u} {φ: Type v} [instPredicate: Predicate α φ] (p: φ) (a: α): Bool := (instPredicate.decidableEval p a).decide
