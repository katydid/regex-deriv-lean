import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex

open SmartRegex

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
theorem Regex.notOr_is_exhaustive (x: Regex α):
  Regex.notOr x = Not (Regex.isOr x) := by
  unfold notOr
  unfold isOr
  cases x <;> simp

inductive NotOr: Regex α -> Prop where
  | emptyset: NotOr Regex.emptyset
  | emptystr: NotOr Regex.emptystr
  | any: NotOr Regex.any
  | pred (p: Predicate.Pred α): NotOr (Regex.pred p)
  | concat (x1 x2: Regex α): NotOr (Regex.concat x1 x2)
  | star (x1: Regex α): NotOr (Regex.star x1)

theorem Regex.NotOr_is_NotisOr (x: Regex α):
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

theorem Regex.notOr_or {α: Type u} {x y: Regex α}:
  Regex.notOr (Regex.or x y) -> False := by
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

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
inductive OrList: Regex α -> Prop where
  | base (x: Regex α):
    Regex.notOr x
    -> OrList x
  | bin (xy x y: Regex α):
    xy = Regex.or x y
    -> Regex.notOr x
    -> OrList y
    -> OrList xy

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
inductive OrList3: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.notOr x
    -> OrList3 x
  | lastcons (xy x y: Regex α):
    xy = Regex.or x y
    -> Regex.notOr x
    -> Regex.notOr y
    -> OrList3 xy
  | cons (xy x y y1 y2: Regex α):
    xy = Regex.or x y
    -> y = Regex.or y1 y2
    -> Regex.notOr x
    -> OrList3 y
    -> OrList3 xy

theorem orlist_is_OrList3 (xy: Regex α):
  OrList xy <-> OrList3 xy := by
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | base _ notx =>
      apply OrList3.singleton
      exact notx
    | bin xy x y hxy hx hy ih =>
      revert hy hxy
      cases y with
      | emptyset =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_emptyset
      | emptystr =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_emptystr
      | any =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_any
      | pred p =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_pred
      | concat x21 x22 =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_concat
      | star x21 =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_star
      | or y1 y2 =>
        intro hxy
        intro hy
        rw [hxy]
        apply OrList3.cons _ x (Regex.or y1 y2) y1 y2 rfl rfl hx
        exact ih
  case mpr =>
    intro h
    induction h with
    | singleton x h =>
      apply OrList.base
      exact h
    | lastcons xy x y hxy hx hy =>
      apply OrList.bin xy x y hxy hx
      apply OrList.base y hy
    | cons _ x y y1 y2 hxy hy1y2 hx hy ihy =>
      rename_i xy'
      apply OrList.bin xy' x y hxy hx ihy

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
-- The or list is also sorted and does not contain duplicates.
inductive OrSortedList3 [LT (Regex α)]: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.notOr x -- or list only element
    -> OrSortedList3 x
  | lastcons (xy x y: Regex α):
    xy = Regex.or x y
    -> x < y -- sorted
    -> Regex.notOr x -- or list second last element
    -> Regex.notOr y -- or list last element
    -> OrSortedList3 xy
  | cons (xy x y y1 y2: Regex α):
    xy = Regex.or x y
    -> y = Regex.or y1 y2
    -> x < y1 -- sorted
    -> Regex.notOr x -- or list element
    -> OrSortedList3 y -- sorted or list of at least two elements
    -> OrSortedList3 xy

theorem orSortedList3_implies_OrList3 [LT (Regex α)] (xy: Regex α):
  OrSortedList3 xy -> OrList3 xy := by
  intro h
  induction h with
  | singleton x h =>
    apply OrList3.singleton x h
  | lastcons xy x y hxy ltxy hx hy =>
    apply OrList3.lastcons xy x y hxy hx hy
  | cons xy x y y1 y2 hxy hy ltxy1 hx hoy ihy =>
    apply OrList3.cons xy x y y1 y2 hxy hy hx ihy

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

inductive OrElem: Regex α -> Prop where
  | emptystr: OrElem Regex.emptystr
  | any: OrElem Regex.any
  | pred (p: Predicate.Pred α): OrElem (Regex.pred p)
  | concat (x1 x2: Regex α): OrElem (Regex.concat x1 x2)
  | star (x1: Regex α) (x1nstar: x1 ≠ Regex.any): OrElem (Regex.star x1)

theorem OrElem_is_orElem (x: Regex α):
  Regex.orElem x <-> OrElem x := by
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case inl h =>
      rw [h]
      apply OrElem.emptystr
    case inr h =>
    cases h
    case inl h =>
      rw [h]
      apply OrElem.any
    case inr h =>
    cases h
    case inl h =>
      cases h
      case intro p h =>
      rw [h]
      apply OrElem.pred
    case inr h =>
    cases h
    case inl h =>
      cases h
      case intro x1 h =>
      cases h
      case intro x2 h =>
      rw [h]
      apply OrElem.concat
    case inr h =>
      cases h
      case intro x1 h =>
      cases h
      case intro x1star x1any =>
      rw [x1star]
      apply OrElem.star
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

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
-- The or list is also sorted and does not contain duplicates.
inductive OrIsSmart [LT (Regex α)]: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.notOr x -- or list only element
    -> OrIsSmart x
  | lastcons (xy x y: Regex α):
    xy = Regex.or x y
    -> x < y -- sorted
    -> Regex.orElem x -- or list second last element
    -> Regex.orElem y -- or list last element
    -> OrIsSmart xy
  | cons (xy x y y1 y2: Regex α):
    xy = Regex.or x y
    -> y = Regex.or y1 y2
    -> x < y1 -- sorted
    -> Regex.orElem x -- or list element
    -> OrIsSmart y -- sorted or list of at least two elements
    -> OrIsSmart xy

theorem IsOrSmart_emptyset [Ord α]:
  OrIsSmart (@Regex.emptyset α) :=
  OrIsSmart.singleton Regex.emptyset Regex.notOr_emptyset

theorem IsOrSmart_emptystr [Ord α]:
  OrIsSmart (@Regex.emptystr α) :=
  OrIsSmart.singleton Regex.emptystr Regex.notOr_emptystr

theorem IsOrSmart_any [Ord α]:
  OrIsSmart (@Regex.any α) :=
  OrIsSmart.singleton Regex.any Regex.notOr_any

theorem IsOrSmart_pred [Ord α] (p: Predicate.Pred α):
  OrIsSmart (Regex.pred p) :=
  OrIsSmart.singleton (Regex.pred p) Regex.notOr_pred

theorem IsOrSmart_concat [Ord α] (x1 x2: Regex α):
  OrIsSmart (Regex.concat x1 x2) :=
  OrIsSmart.singleton (Regex.concat x1 x2) Regex.notOr_concat

theorem IsOrSmart_star [Ord α] (x1: Regex α):
  OrIsSmart (Regex.star x1) :=
  OrIsSmart.singleton (Regex.star x1) Regex.notOr_star

-- TODO: Wait for Std.LawfulEqOrd to land, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Ordering.2Eeq.20is.20equivalent.20to.20LawfulEq/with/519113072
theorem neq_is_lt_or_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (neq: x ≠ y): (x < y) \/ (x > y) := by
  sorry

theorem not_less_than_is_greater_than [o: Ord α] [DecidableEq α] {x y: α}
  (neq: x ≠ y) (nlt: Not (x < y)): x > y := by
  have h := neq_is_lt_or_gt neq
  cases h
  case inl h =>
    contradiction
  case inr h =>
    exact h

theorem mkOr_preserves_smartOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α)
  (smartx: OrIsSmart x) (notorx: Regex.notOr x) (smarty: OrIsSmart y) (notory: Regex.notOr y):
  OrIsSmart (mkOr x y) := by
  unfold mkOr
  split_ifs
  case pos h =>
    exact smartx
  case pos h =>
    exact smarty
  case pos h =>
    exact smartx
  case pos h =>
    exact smartx
  case pos h =>
    exact smarty
  case pos h =>
    apply OrIsSmart.lastcons (Regex.or x y) x y rfl h
    · rw [orElem'_is_orElem]
      unfold Regex.orElem'
      split_ands <;> assumption
    · rw [orElem'_is_orElem]
      unfold Regex.orElem'
      split_ands <;> assumption
  case neg h =>
    rename_i hneq hxemptyset hxanystar hyemptyset hyanystar
    apply OrIsSmart.lastcons (Regex.or y x) y x rfl
    · apply not_less_than_is_greater_than hneq h
    · rw [orElem'_is_orElem]
      unfold Regex.orElem'
      split_ands <;> assumption
    · rw [orElem'_is_orElem]
      unfold Regex.orElem'
      split_ands <;> assumption

theorem insertOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: Regex.notOr y):
  OrIsSmart (insertOr x y) := by
  induction hx with
  | singleton x h =>
    unfold insertOr
    rw [<- Regex.NotOr_is_notOr] at h
    cases h with
    | emptyset =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_emptyset
      · exact Regex.notOr_emptyset
      · exact OrIsSmart.singleton y hy
      · exact hy
    | emptystr =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_emptystr
      · exact Regex.notOr_emptystr
      · exact OrIsSmart.singleton y hy
      · exact hy
    | any =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_any
      · exact Regex.notOr_any
      · exact OrIsSmart.singleton y hy
      · exact hy
    | pred p =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_pred p
      · exact Regex.notOr_pred
      · exact OrIsSmart.singleton y hy
      · exact hy
    | concat x1 x2 =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_concat x1 x2
      · exact Regex.notOr_concat
      · exact OrIsSmart.singleton y hy
      · exact hy
    | star x1 =>
      simp only
      apply mkOr_preserves_smartOr
      · exact IsOrSmart_star x1
      · exact Regex.notOr_star
      · exact OrIsSmart.singleton y hy
      · exact hy
  | lastcons x1x2 x1 x2 hx1x2 ltx1x2 hx1 hx2 =>
    rw [hx1x2]
    unfold insertOr
    split_ifs
    case pos h =>
      exact OrIsSmart.lastcons (Regex.or x1 x2) x1 x2 rfl ltx1x2 hx1 hx2
    case pos h =>
      sorry
    case neg h =>
      sorry
  | cons h =>
    sorry


theorem mergeOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  sorry

theorem smartOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  sorry
