import RegexDeriv.Std.Linter.DetectClassical

import RegexDeriv.Std.Ordering

import RegexDeriv.Regex.Smart.SmartRegex

open SmartRegex

-- SmartOrElem defines all Regexes that are allowed to be in an `or` expression
-- that was smartly constructed.
-- The normalized `or` expressions are expected to be in the following form,
-- which we call an `or` expression list:
-- `(or a (or b (or c d)))`, where `a`, `b`, `c` and `d` are considered elements in the `or` expression list.
-- We expect all nested `or` expressions to be normalized into a sorted list of `or` expressions.
-- `or` elements include all regexes, except `emptyset` and `star any`,
-- since these are equivalent to `true` and `false`, which we expect to simplified.
-- `or` elements also do not include other `or` expressions, as these are expected to be normalized into the `or` expression list.
inductive Regex.SmartOrElem: Regex α -> Prop where
  | emptystr: SmartOrElem Regex.emptystr
  | any: SmartOrElem Regex.any
  | pred (p: Predicate.Pred α): SmartOrElem (Regex.pred p)
  | concat (x1 x2: Regex α): SmartOrElem (Regex.concat x1 x2)
  | star (x1: Regex α) (x1nstar: x1 ≠ Regex.any): SmartOrElem (Regex.star x1)

-- NotOr defines all Regexes that are not `or` expressions.
inductive Regex.NotOr: Regex α -> Prop where
  | emptyset: NotOr Regex.emptyset
  | emptystr: NotOr Regex.emptystr
  | any: NotOr Regex.any
  | pred (p: Predicate.Pred α): NotOr (Regex.pred p)
  | concat (x1 x2: Regex α): NotOr (Regex.concat x1 x2)
  | star (x1: Regex α): NotOr (Regex.star x1)

-- Show that NorOr is a subset of SmartOrElem.
theorem SmartOrElem_implies_NotOr {x: Regex α}:
  Regex.SmartOrElem x -> Regex.NotOr x := by
  intro h
  cases h with
  | emptystr => exact Regex.NotOr.emptystr
  | any => exact Regex.NotOr.any
  | pred p => exact Regex.NotOr.pred p
  | concat x1 x2 => exact Regex.NotOr.concat x1 x2
  | star x1 => exact Regex.NotOr.star x1

-- The definition of Regex.isOr is only here to double check
-- the definition of NotOr
def Regex.isOr (x: Regex α) : Prop :=
  ∃ x1 x2, x = Regex.or x1 x2

-- Regex.NotOr.is_exhaustive checks that if a new
private theorem Regex.NotOr.is_exhaustive {x: Regex α}:
  Regex.NotOr x = Not (Regex.isOr x) := by
  unfold isOr
  cases x with
  | emptyset =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.emptyset
  | emptystr =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.emptystr
  | any =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.any
  | pred p =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.pred
  | or x1 x2 =>
    simp only [Regex.or.injEq, exists_and_left, exists_eq', and_true, not_true_eq_false, eq_iff_iff,
      iff_false]
    intro h
    nomatch h
  | concat x1 x2 =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.concat
  | star x1 =>
    simp only [reduceCtorEq, exists_false, not_false_eq_true, eq_iff_iff, iff_true]
    apply NotOr.star

theorem Regex.NotOr.split.otherwise
  (h : ∀ (y1 y2 : Regex α), y = (Regex.or y1 y2) → False):
  Regex.NotOr y := by
  rw [Regex.NotOr.is_exhaustive]
  intro h'
  unfold Regex.isOr at h'
  cases h'
  case intro y1' h' =>
  cases h'
  case intro y2' h' =>
  apply h y1' y2'
  assumption

-- An alternative definition of SmartOrElem
-- We keep it as a sanity check that the definition of Regex.SmartOrElem is correct.
def Regex.SmartOrElem' (x: Regex α): Prop :=
  x ≠ Regex.emptyset
  /\ x ≠ Regex.star Regex.any
  /\ Regex.NotOr x

-- Another alternative definition of SmartOrElem
-- We keep it as a sanity check that the definition of Regex.SmartOrElem is correct.
private def Regex.SmartOrElem'' (x: Regex α) : Prop :=
  (x = Regex.emptystr)
  \/ (x = Regex.any)
  \/ (∃ p: Predicate.Pred α, x = Regex.pred p)
  \/ (∃ x1 x2, x = Regex.concat x1 x2)
  \/ (∃ x1, x = Regex.star x1 /\ x1 ≠ Regex.any)

-- Alternative definition of NotOr
-- We keep it as a sanity check that the definition of Regex.NotOr is correct.
private def Regex.NotOr' (x: Regex α) : Prop :=
  (x = Regex.emptyset)
  \/ (x = Regex.emptystr)
  \/ (x = Regex.any)
  \/ (∃ p: Predicate.Pred α, x = Regex.pred p)
  \/ (∃ x1 x2, x = Regex.concat x1 x2)
  \/ (∃ x1, x = Regex.star x1)

-- Check that Regex.notOr does an exhaustive match of all possible patterns, except for Regex.or.
private theorem Regex.NotOr'.is_exhaustive {x: Regex α}:
  Regex.NotOr' x = Not (Regex.isOr x) := by
  unfold NotOr'
  unfold isOr
  cases x <;> simp

-- Check that the alternative definition of NotOr is equivalent to the exported one.
private theorem Regex.NotOr_is_NotOr' (x: Regex α):
  Regex.NotOr x = Regex.NotOr' x := by
  rw [Regex.NotOr'.is_exhaustive]
  rw [Regex.NotOr.is_exhaustive]

-- Prove that an or is not not and or.
private theorem Regex.Not_NotOr'_or {α: Type u} {x y: Regex α}:
  Not (Regex.NotOr' (Regex.or x y)) := by
  intro h
  unfold NotOr' at h
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    cases h
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    cases h
    next h =>
    cases h
    contradiction
  | inr h =>
  cases h
  contradiction

-- Check that the alternative definition of SmartOrElem is equivalent to the exported one.
private theorem Regex.SmartOrElem''_is_SmartOrElem {x: Regex α}:
  Regex.SmartOrElem'' x <-> Regex.SmartOrElem x := by
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case inl h =>
      rw [h]
      apply Regex.SmartOrElem.emptystr
    case inr h =>
    cases h
    case inl h =>
      rw [h]
      apply Regex.SmartOrElem.any
    case inr h =>
    cases h
    case inl h =>
      cases h
      case intro p h =>
      rw [h]
      apply Regex.SmartOrElem.pred
    case inr h =>
    cases h
    case inl h =>
      cases h
      case intro x1 h =>
      cases h
      case intro x2 h =>
      rw [h]
      apply Regex.SmartOrElem.concat
    case inr h =>
      cases h
      case intro x1 h =>
      cases h
      case intro x1star x1any =>
      rw [x1star]
      apply Regex.SmartOrElem.star
      exact x1any
  case mpr =>
    intro h
    unfold Regex.SmartOrElem''
    cases h with
    | emptystr =>
      apply Or.inl
      rfl
    | any =>
      apply Or.inr
      apply Or.inl
      rfl
    | pred p =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exists p
    | concat x1 x2 =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exists x1
      exists x2
    | star x1 =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exists x1

-- Check that the alternative definitions of SmartOrElem are equivalent.
private theorem Regex.SmartOrElem''_is_SmartOrElem' (x: Regex α):
  Regex.SmartOrElem'' x <-> Regex.SmartOrElem' x := by
  apply Iff.intro
  case mp =>
    intro h
    unfold Regex.SmartOrElem'' at h
    unfold Regex.SmartOrElem'
    cases h
    case inl hemptystr =>
      rw [hemptystr]
      simp
      apply Regex.NotOr.emptystr
    case inr h =>
    cases h
    case inl hany =>
      rw [hany]
      simp
      apply Regex.NotOr.any
    case inr h =>
    cases h
    case inl hpred =>
      cases hpred
      case intro p hpred =>
      rw [hpred]
      simp
      apply Regex.NotOr.pred
    case inr h =>
    cases h
    case inl hconcat =>
      cases hconcat
      case intro x1 hconcat =>
      cases hconcat
      case intro x2 hconcat =>
      rw [hconcat]
      simp
      apply Regex.NotOr.concat
    case inr hstar =>
      cases hstar
      case intro x1 hstar =>
      cases hstar
      case intro hstar hany =>
      rw [hstar]
      simp
      split_ands
      exact hany
      apply Regex.NotOr.star
  case mpr =>
    intro h
    unfold Regex.SmartOrElem' at h
    unfold Regex.SmartOrElem''
    cases h
    case intro hnemptyset h =>
    cases h
    case intro hnstarany h =>
    cases h with
    | emptyset =>
      contradiction
    | emptystr =>
      apply Or.inl
      rfl
    | any =>
      apply Or.inr
      apply Or.inl
      rfl
    | pred p =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exists p
    | concat x1 x2 =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exists x1
      exists x2
    | star x1 =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exists x1
      apply And.intro rfl
      intro hx1
      rw [hx1] at hnstarany
      contradiction

-- Check that the alternative definition of SmartOrElem is equivalent to the exported one.
theorem Regex.SmartOrElem'_is_SmartOrElem {x: Regex α}:
  Regex.SmartOrElem' x <-> Regex.SmartOrElem x := by
  rw [<- Regex.SmartOrElem''_is_SmartOrElem']
  rw [<- Regex.SmartOrElem''_is_SmartOrElem]

-- Allow the construction of SmartOrElem using 3 properties of a Regex.
theorem Regex.SmartOrElem.mk {x: Regex α}
  (not_emptyset: x ≠ Regex.emptyset)
  (not_starany: x ≠ Regex.star Regex.any)
  (not_or: Regex.NotOr x): SmartOrElem x := by
  rw [<- Regex.SmartOrElem'_is_SmartOrElem]
  unfold Regex.SmartOrElem'
  split_ands <;> assumption
