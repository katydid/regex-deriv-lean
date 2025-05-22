import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex

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

def Regex.isOr (x: Regex α) : Prop :=
  ∃ x1 x2, x = Regex.or x1 x2

def Regex.notOr (x: Regex α) : Prop :=
  (x = Regex.emptyset)
  \/ (x = Regex.emptystr)
  \/ (x = Regex.any)
  \/ (∃ p: Predicate.Pred α, x = Regex.pred p)
  \/ (∃ x1 x2, x = Regex.concat x1 x2)
  \/ (∃ x1, x = Regex.star x1)

-- check that Regex.notOr does an exhaustive match of all possible patterns, except for Regex.or.
theorem Regex.notOr_is_exhaustive {x: Regex α}:
  Regex.notOr x = Not (Regex.isOr x) := by
  unfold notOr
  unfold isOr
  cases x <;> simp

theorem Regex.NotOr_is_NotisOr {x: Regex α}:
  NotOr x = Not (Regex.isOr x) := by
  unfold isOr
  cases x with
  | emptyset =>
    simp
    apply NotOr.emptyset
  | emptystr =>
    simp
    apply NotOr.emptystr
  | any =>
    simp
    apply NotOr.any
  | pred p =>
    simp
    apply NotOr.pred
  | or x1 x2 =>
    simp
    intro h
    nomatch h
  | concat x1 x2 =>
    simp
    apply NotOr.concat
  | star x1 =>
    simp
    apply NotOr.star

theorem Regex.NotOr_is_notOr (x: Regex α):
  NotOr x = Regex.notOr x := by
  rw [Regex.notOr_is_exhaustive ]
  rw [Regex.NotOr_is_NotisOr]

theorem Regex.Not_notOr_or {α: Type u} {x y: Regex α}:
  Not (Regex.notOr (Regex.or x y)) := by
  intro h
  unfold notOr at h
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

theorem Regex.notOr_emptyset {α: Type u}:
  Regex.notOr (@Regex.emptyset α) := by
  unfold notOr
  simp

theorem Regex.notOr_emptystr {α: Type u}:
  Regex.notOr (@Regex.emptystr α) := by
  unfold notOr
  simp

theorem Regex.notOr_any {α: Type u}:
  Regex.notOr (@Regex.any α) := by
  unfold notOr
  simp

theorem Regex.notOr_pred {α: Type u} {p: Predicate.Pred α}:
  Regex.notOr (@Regex.pred α p) := by
  unfold notOr
  simp

theorem Regex.notOr_concat {α: Type u} {x y: Regex α}:
  Regex.notOr (Regex.concat x y) := by
  unfold notOr
  simp

theorem Regex.notOr_star {α: Type u} {x: Regex α}:
  Regex.notOr (Regex.star x) := by
  unfold notOr
  simp

def Regex.orElem' (x: Regex α): Prop :=
  x ≠ Regex.emptyset
  /\ x ≠ Regex.star Regex.any
  /\ Regex.notOr x

-- An or element does not include an `or`, `emptyset` or `star any`.
def Regex.orElem (x: Regex α) : Prop :=
  (x = Regex.emptystr)
  \/ (x = Regex.any)
  \/ (∃ p: Predicate.Pred α, x = Regex.pred p)
  \/ (∃ x1 x2, x = Regex.concat x1 x2)
  \/ (∃ x1, x = Regex.star x1 /\ x1 ≠ Regex.any)

theorem OrElem_is_orElem {x: Regex α}:
  Regex.orElem x <-> Regex.SmartOrElem x := by
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
    unfold Regex.orElem
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

theorem orElem'_is_orElem (x: Regex α):
  Regex.orElem x <-> Regex.orElem' x := by
  apply Iff.intro
  case mp =>
    intro h
    unfold Regex.orElem at h
    unfold Regex.orElem'
    cases h
    case inl hemptystr =>
      rw [hemptystr]
      simp
      apply Regex.notOr_emptystr
    case inr h =>
    cases h
    case inl hany =>
      rw [hany]
      simp
      apply Regex.notOr_any
    case inr h =>
    cases h
    case inl hpred =>
      cases hpred
      case intro p hpred =>
      rw [hpred]
      simp
      apply Regex.notOr_pred
    case inr h =>
    cases h
    case inl hconcat =>
      cases hconcat
      case intro x1 hconcat =>
      cases hconcat
      case intro x2 hconcat =>
      rw [hconcat]
      simp
      apply Regex.notOr_concat
    case inr hstar =>
      cases hstar
      case intro x1 hstar =>
      cases hstar
      case intro hstar hany =>
      rw [hstar]
      simp
      split_ands
      exact hany
      apply Regex.notOr_star
  case mpr =>
    intro h
    unfold Regex.orElem' at h
    unfold Regex.orElem
    cases h
    case intro hnemptyset h =>
    cases h
    case intro hnstarany h =>
    cases h
    case inl hemptyset =>
      contradiction
    case inr h =>
    cases h
    case inl hemptystr =>
      apply Or.inl
      assumption
    case inr h =>
    cases h
    case inl hany =>
      apply Or.inr
      apply Or.inl
      assumption
    case inr h =>
    cases h
    case inl hpred =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      assumption
    case inr h =>
    cases h
    case inl hconcat =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      assumption
    case inr hstar =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      cases hstar
      case intro x1 hstar =>
        exists x1
        apply And.intro
        exact hstar
        intro hany
        apply hnstarany
        rw [hstar]
        congr

theorem OrElem_implies_NotOr {x: Regex α}:
  Regex.SmartOrElem x -> Regex.NotOr x := by
  intro h
  cases h with
  | emptystr => exact Regex.NotOr.emptystr
  | any => exact Regex.NotOr.any
  | pred p => exact Regex.NotOr.pred p
  | concat x1 x2 => exact Regex.NotOr.concat x1 x2
  | star x1 => exact Regex.NotOr.star x1

lemma lame2
  (h : ∀ (y1 y2 : Regex α), y = (Regex.or y1 y2) → False):
  Regex.notOr y := by
  rw [Regex.notOr_is_exhaustive]
  intro h'
  unfold Regex.isOr at h'
  cases h'
  case intro y1' h' =>
  cases h'
  case intro y2' h' =>
  apply h y1' y2'
  assumption
