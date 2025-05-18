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

-- check that Regex.notOr does an exhaustive match of all possible patterns, except for Regex.or.
theorem Regex.notOr_is_exhaustive (x: Regex α):
  Regex.notOr x = Not (Regex.isOr x) := by
  unfold notOr
  unfold isOr
  cases x <;> simp

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

theorem orElem'_is_orElem (x: Regex α):
  Regex.orElem x <-> Regex.orElem' x := by
  sorry

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

theorem mkOr_preserves_smartOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α)
  (smartx: OrIsSmart x) (notorx: Regex.notOr x) (smarty: OrIsSmart y) (notory: Regex.notOr y):
  OrIsSmart (mkOr x y) := by
  unfold mkOr
  split_ifs
  case pos h =>
    exact smartx
  case pos h =>
    sorry
  case pos h =>
    sorry
  case pos h =>
    sorry
  case pos h =>
    sorry
  case pos h =>
    apply OrIsSmart.lastcons (Regex.or x y) x y rfl h
    rw [orElem'_is_orElem]
    unfold Regex.orElem'
    split_ands <;> assumption
    rw [orElem'_is_orElem]
    unfold Regex.orElem'
    split_ands <;> assumption
  case neg h =>
    sorry

theorem mergeOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  sorry

theorem smartOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  sorry
