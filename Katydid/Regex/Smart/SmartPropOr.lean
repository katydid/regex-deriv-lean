import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex
import Katydid.Regex.Smart.SmartPropOrElem

open SmartRegex

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

theorem mkOr_makes_smartOr {α: Type} [Ord α] [DecidableEq α] {x y: Regex α}
  (notorx: Regex.notOr x) (notory: Regex.notOr y):
  OrIsSmart (mkOr x y) := by
  unfold mkOr
  split_ifs
  case pos h =>
    apply OrIsSmart.singleton x notorx
  case pos h =>
    apply OrIsSmart.singleton y notory
  case pos h =>
    apply OrIsSmart.singleton x notorx
  case pos h =>
    apply OrIsSmart.singleton x notorx
  case pos h =>
    apply OrIsSmart.singleton y notory
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
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: OrIsSmart x) (hy: Regex.notOr y):
  OrIsSmart (insertOr x y) := by
  induction hx with
  | singleton x h =>
    unfold insertOr
    rw [<- Regex.NotOr_is_notOr] at h
    cases h with
    | emptyset =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_emptyset hy
    | emptystr =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_emptystr hy
    | any =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_any hy
    | pred p =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_pred hy
    | concat x1 x2 =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_concat hy
    | star x1 =>
      simp only
      exact mkOr_makes_smartOr Regex.notOr_star hy
  | lastcons x1x2 x1 x2 hx1x2 ltx1x2 hx1 hx2 =>
    rw [hx1x2]
    unfold insertOr
    split_ifs
    case pos h =>
      exact OrIsSmart.lastcons (Regex.or x1 x2) x1 x2 rfl ltx1x2 hx1 hx2
    case pos hneq hlt =>
      rw [insertOr]
      · have hx1' := OrElem_is_orElem.mp hx1
        have hx2' := OrElem_is_orElem.mp hx2
        have hhx1 := OrElem_implies_NotOr hx1'
        have hhx2 := OrElem_implies_NotOr hx2'
        rw [Regex.NotOr_is_notOr] at hhx1
        rw [Regex.NotOr_is_notOr] at hhx2
        have hh := mkOr_makes_smartOr hhx2 hy
        cases hh with
        | singleton x2y hx2y =>
          apply OrIsSmart.lastcons (Regex.or x1 (mkOr x2 y)) x1 (mkOr x2 y)
          · rfl
          · sorry -- mkOr preserves OrElem
          · assumption
          · sorry
        | lastcons =>
          sorry
        | cons =>
          sorry
      · intro x1' x2' hh
        rw [hh] at hx2
        -- Regex.orElem (x1'.or x2') -> False
        sorry
    case neg hneq hnlt =>
      have h := not_less_than_is_greater_than hneq hnlt
      sorry
  | cons h =>
    sorry

theorem mergeOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  unfold mergeOr
  split
  next _ x1 x2 =>
    split
    next _ y1 y2 =>
      sorry
    next _ h =>
      apply insertOr_preserves_smartOr hx
      apply lame2 h
  next _ h =>
    apply insertOr_preserves_smartOr hy
    apply lame2 h


theorem smartOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  sorry
