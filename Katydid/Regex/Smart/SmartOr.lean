import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex
import Katydid.Regex.Smart.SmartOrElem

open SmartRegex

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
-- The or list is also sorted and does not contain duplicates.
inductive OrIsSmart [LT (Regex α)]: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.NotOr x -- or list only element
    -> OrIsSmart x
  | lastcons (xy x y: Regex α):
    xy = Regex.or x y
    -> x < y -- sorted
    -> Regex.SmartOrElem x -- or list second last element
    -> Regex.SmartOrElem y -- or list last element
    -> OrIsSmart xy
  | cons (xy x y y1 y2: Regex α):
    xy = Regex.or x y
    -> y = Regex.or y1 y2
    -> x < y1 -- sorted
    -> Regex.SmartOrElem x -- or list element
    -> OrIsSmart y -- sorted or list of at least two elements
    -> OrIsSmart xy

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
  (notorx: Regex.NotOr x) (notory: Regex.NotOr y):
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
    · apply Regex.SmartOrElem.mk <;> assumption
    · apply Regex.SmartOrElem.mk <;> assumption
  case neg h =>
    rename_i hneq hxemptyset hxanystar hyemptyset hyanystar
    apply OrIsSmart.lastcons (Regex.or y x) y x rfl
    · apply not_less_than_is_greater_than hneq h
    · apply Regex.SmartOrElem.mk <;> assumption
    · apply Regex.SmartOrElem.mk <;> assumption

theorem insertOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: OrIsSmart x) (hy: Regex.NotOr y):
  OrIsSmart (insertOr x y) := by
  induction hx with
  | singleton x h =>
    unfold insertOr
    cases h with
    | emptyset =>
      simp only
      exact mkOr_makes_smartOr Regex.NotOr.emptyset hy
    | emptystr =>
      simp only
      exact mkOr_makes_smartOr Regex.NotOr.emptystr hy
    | any =>
      simp only
      exact mkOr_makes_smartOr Regex.NotOr.any hy
    | pred p =>
      simp only
      exact mkOr_makes_smartOr (Regex.NotOr.pred p) hy
    | concat x1 x2 =>
      simp only
      exact mkOr_makes_smartOr (Regex.NotOr.concat x1 x2) hy
    | star x1 =>
      simp only
      exact mkOr_makes_smartOr (Regex.NotOr.star x1) hy
  | lastcons x1x2 x1 x2 hx1x2 ltx1x2 hx1 hx2 =>
    rw [hx1x2]
    unfold insertOr
    split_ifs
    case pos h =>
      exact OrIsSmart.lastcons (Regex.or x1 x2) x1 x2 rfl ltx1x2 hx1 hx2
    case pos hneq hlt =>
      rw [insertOr]
      · have hhx1 := SmartOrElem_implies_NotOr hx1
        have hhx2 := SmartOrElem_implies_NotOr hx2
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
      apply Regex.NotOr.split.otherwise h
  next _ h =>
    apply insertOr_preserves_smartOr hy
    apply Regex.NotOr.split.otherwise h


theorem smartOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  sorry
