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
  admit

theorem lt_and_gt_is_impossible [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: x < y) (hgt: x > y): False := by
  admit

theorem not_lt_is_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x < y)) (hneq: x ≠ y): x > y := by
  admit

theorem not_gt_is_lt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x > y)) (hneq: x ≠ y): x < y := by
  admit

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

private lemma insertOr_NotOr_NotOr_OrIsSmart
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.NotOr x) (hy: Regex.NotOr y):
  OrIsSmart (insertOr x y) := by
  unfold insertOr
  cases hy with
  | emptyset =>
    simp only
    exact mkOr_makes_smartOr hx Regex.NotOr.emptyset
  | emptystr =>
    simp only
    exact mkOr_makes_smartOr hx Regex.NotOr.emptystr
  | any =>
    simp only
    exact mkOr_makes_smartOr hx Regex.NotOr.any
  | pred p =>
    simp only
    exact mkOr_makes_smartOr hx (Regex.NotOr.pred p)
  | concat y1 y2 =>
    simp only
    exact mkOr_makes_smartOr hx (Regex.NotOr.concat y1 y2)
  | star y1 =>
    simp only
    exact mkOr_makes_smartOr hx (Regex.NotOr.star y1)

lemma Regex.NotOr_mkOr_implies_idemp
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α}:
  Regex.NotOr (mkOr x y) ->
  x = y
  \/ x = Regex.emptyset
  \/ x = Regex.star Regex.any
  \/ y = Regex.emptyset
  \/ y = Regex.star Regex.any := by
  unfold mkOr
  split_ifs
  case pos h =>
    intro _
    apply Or.inl h
  case pos h =>
    intro _
    apply Or.inr (Or.inl h)
  case pos h =>
    intro _
    apply Or.inr (Or.inr (Or.inl h))
  case pos h =>
    intro _
    apply Or.inr (Or.inr (Or.inr (Or.inl h)))
  case pos h =>
    intro _
    apply Or.inr (Or.inr (Or.inr (Or.inr h)))
  case pos _ =>
    intro h
    contradiction
  case neg h =>
    intro h
    contradiction

lemma Regex.mkOr_comm
  {α: Type u} [Ord α] [DecidableEq α] {x y: Regex α}:
  mkOr x y = mkOr y x := by
  unfold mkOr
  split_ifs <;> try (subst_vars ; (first | assumption | rfl | contradiction))
  next pos h =>
    exfalso
    apply lt_and_gt_is_impossible h ; assumption
  next neg h =>
    exfalso
    rename_i h'
    have h' := not_gt_is_lt h' neg
    have h := not_lt_is_gt h neg
    apply lt_and_gt_is_impossible h ; assumption

theorem insertOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: Regex.NotOr x) (hy: OrIsSmart y):
  OrIsSmart (insertOr x y) := by
  induction hy with
  | singleton y hy =>
    apply insertOr_NotOr_NotOr_OrIsSmart hx hy
  | lastcons y1y2 y1 y2 hy1y2 lty1y2 hy1 hy2 =>
    rw [hy1y2]
    unfold insertOr
    split_ifs
    case pos h =>
      exact OrIsSmart.lastcons (Regex.or y1 y2) y1 y2 rfl lty1y2 hy1 hy2
    case pos hneq hlt =>
      rw [insertOr]
      · have hhy1 := SmartOrElem_implies_NotOr hy1
        have hhy2 := SmartOrElem_implies_NotOr hy2
        have hh := mkOr_makes_smartOr hx hhy2
        cases hh with
        | singleton _ hxy2 =>
          have hxy2' := Regex.NotOr_mkOr_implies_idemp hxy2
          apply OrIsSmart.lastcons (Regex.or y1 (mkOr x y2)) y1 (mkOr y2 x) ?_ ?_ hy1 ?_
          · rw [Regex.mkOr_comm]
          · sorry -- true by cases
          · sorry -- true by cases
        | lastcons =>
          sorry
        | cons =>
          sorry
      · intro x1' x2' hh
        -- rw [hh] at hx2
        -- Regex.orElem (x1'.or x2') -> False
        sorry
    case neg hneq hnlt =>
      have h := not_less_than_is_greater_than hneq hnlt
      sorry

  | cons h =>
    sorry

theorem mergeOr_preserves_smartOr_for_notor_left
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: Regex.NotOr x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  unfold mergeOr
  split
  next _ y1 y2 =>
    split
    next _ x1 x2 =>
      contradiction
    next _ h =>
      apply insertOr_preserves_smartOr hx hy
  next _ h =>
    have h := Regex.NotOr.split.otherwise h
    apply insertOr_preserves_smartOr h
    apply OrIsSmart.singleton
    exact hx

theorem mergeOr_preserves_smartOr_for_notor_right
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: Regex.NotOr y) (hy: OrIsSmart x):
  OrIsSmart (mergeOr x y) := by
  unfold mergeOr
  split
  next _ y1 y2 =>
    contradiction
  next _ h =>
    apply insertOr_preserves_smartOr hx hy

theorem mergeOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  induction hy with
  | singleton y hy =>
    unfold mergeOr
    split
    next _ y1 y2 =>
      contradiction
    next _ h =>
      apply insertOr_preserves_smartOr
      · exact Regex.NotOr.split.otherwise h
      · exact hx
  | lastcons y1y2 y1 y2 hy1y2 lty1y2 hy1 hy2 =>
    unfold mergeOr
    rw [hy1y2]
    simp only
    split
    next _ x1 x2 =>
      have hy1' := SmartOrElem_implies_NotOr hy1
      have hy2' := SmartOrElem_implies_NotOr hy2
      apply insertOr_preserves_smartOr hy1'
      apply mergeOr_preserves_smartOr_for_notor_right hy2'
      exact hx
    next _ h =>
      have h := Regex.NotOr.split.otherwise h
      apply insertOr_preserves_smartOr h
      apply OrIsSmart.lastcons (Regex.or y1 y2) y1 y2 rfl lty1y2 hy1 hy2
  | cons y y1 y2 y21 y22 hy1y2 hy21y22 hlt hy1 hy2 ih =>
    have hny1 := SmartOrElem_implies_NotOr hy1
    unfold mergeOr
    split
    next _ y1 y2 =>
      split
      next _ x1 x2 =>
        cases hy1y2
        subst_vars
        apply insertOr_preserves_smartOr hny1 ih
      next _ h =>
        cases hy1y2
        subst_vars
        apply insertOr_preserves_smartOr
        · apply Regex.NotOr.split.otherwise h
        · apply OrIsSmart.cons (Regex.or y1 (Regex.or y21 y22)) y1 (Regex.or y21 y22) y21 y22 rfl rfl hlt hy1 hy2
    next _ h hn =>
      apply insertOr_preserves_smartOr
      · apply Regex.NotOr.split.otherwise hn
      · exact hx

theorem smartOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  sorry
