import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex
import Katydid.Regex.Smart.SmartOrElem
import Katydid.Regex.Smart.LawfulEqOrd

open SmartRegex

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
-- The or list is also sorted and does not contain duplicates.
inductive OrIsSmart [LT (Regex α)]: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.NotOr x -- or list only element
    -> OrIsSmart x
  | lastcons (x y: Regex α):
    x < y -- sorted
    -> Regex.SmartOrElem x -- or list second last element
    -> Regex.SmartOrElem y -- or list last element
    -> OrIsSmart (Regex.or x y)
  | cons (x y1 y2: Regex α):
    x < y1 -- sorted
    -> Regex.SmartOrElem x -- or list element
    -> OrIsSmart (Regex.or y1 y2) -- sorted or list of at least two elements
    -> OrIsSmart (Regex.or x (Regex.or y1 y2))

theorem mkOr_idemp
  {α: Type} [Ord α] [DecidableEq α] (x: Regex α):
  mkOr x x = x := by
  unfold mkOr
  split_ifs <;> trivial

theorem consOr_makes_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y1 y2: Regex α}
  (hx: Regex.NotOr x)
  (hy: OrIsSmart (Regex.or y1 y2))
  (hlty1: x < y1):
  (OrIsSmart (consOr x (Regex.or y1 y2))) := by
  unfold consOr
  split_ifs
  case pos h =>
    exact hy
  case pos h =>
    rw [h]
    apply OrIsSmart.singleton
    apply Regex.NotOr.star
  case neg h =>
    apply OrIsSmart.cons x y1 y2 hlty1 ?_ hy
    apply Regex.SmartOrElem.mk <;> assumption

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
    apply OrIsSmart.lastcons x y h
    · apply Regex.SmartOrElem.mk <;> assumption
    · apply Regex.SmartOrElem.mk <;> assumption
  case neg h =>
    rename_i hneq hxemptyset hxanystar hyemptyset hyanystar
    apply OrIsSmart.lastcons y x
    · apply not_less_than_is_greater_than hneq h
    · apply Regex.SmartOrElem.mk <;> assumption
    · apply Regex.SmartOrElem.mk <;> assumption

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

theorem OrIsSmart.cons_mkOr
  {α: Type} [Ord α] [DecidableEq α] {x y1 y2: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: OrIsSmart (mkOr y1 y2))
  (hy1: Regex.NotOr y1)
  (hny1: y1 ≠ Regex.star Regex.any)
  (hy2: Regex.SmartOrElem y2)
  (hlty1: x < y1)
  (hlty2: x < y2):
  (OrIsSmart (Regex.or x (mkOr y1 y2))) := by
  unfold mkOr at hy
  split_ifs at hy
  case pos h =>
    rw [<- h]
    rw [mkOr_idemp]
    rw [<- h] at hy2
    apply OrIsSmart.lastcons x y1 hlty1 hx hy2
  case pos h =>
    rw [h]
    rename_i h'
    unfold mkOr
    simp only [↓reduceIte]
    split_ifs
    case pos h =>
      subst_vars
      contradiction
    case neg h =>
      apply OrIsSmart.lastcons x y2 hlty2 hx hy2
  case pos h h' h'' =>
    rw [h'']
    rename_i h'
    unfold mkOr
    split_ifs <;> try contradiction
    case pos h =>
      rw [h''] at hy2
      cases hy2
  case pos =>
    unfold mkOr
    split_ifs
    apply OrIsSmart.lastcons x y2 hlty2 hx hy2
  case pos =>
    unfold mkOr
    split_ifs
    apply OrIsSmart.cons x y1 y2 hlty1 hx hy
  case neg h h' h'' h''' h'''' h''''' =>
    unfold mkOr
    split_ifs
    apply OrIsSmart.cons x y2 y1 hlty2 hx hy

theorem OrIsSmart.cons_insertOr
  {α: Type} [Ord α] [DecidableEq α] {x y z1 z2: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: Regex.NotOr y)
  (hny: y ≠ Regex.star Regex.any)
  (hi: OrIsSmart (insertOr y (Regex.or z1 z2)))
  (hlty: x < y)
  (hltz1: x < z1):
  (OrIsSmart (Regex.or x (insertOr y (Regex.or z1 z2)))) := by
  unfold insertOr
  split_ifs
  case pos h =>
    have h := eq_of_beq h
    contradiction
  case neg h =>
    clear h
    simp only
    split_ifs
    case pos h =>
      apply OrIsSmart.cons x z1 z2 hltz1 hx
      sorry
    case pos h =>
      apply OrIsSmart.cons x z1 (insertOr y z2) hltz1 hx
      sorry
    case neg h =>
      sorry

private lemma insertOr_NotOr_NotOr_OrIsSmart
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.NotOr x) (hy: Regex.NotOr y):
  OrIsSmart (insertOr x y) := by
  unfold insertOr
  split_ifs
  case pos h =>
    have h := eq_of_beq h
    rw [h]
    apply OrIsSmart.singleton
    apply Regex.NotOr.star
  case neg h =>
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

theorem insertOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α] {x y: Regex α} (hx: Regex.NotOr x) (hy: OrIsSmart y):
  OrIsSmart (insertOr x y) := by
  induction hy with
  | singleton y hy =>
    apply insertOr_NotOr_NotOr_OrIsSmart hx hy
  | lastcons y1 y2 lty1y2 hy1 hy2 =>
    unfold insertOr
    split_ifs
    case pos h =>
      have h := eq_of_beq h
      rw [h]
      apply OrIsSmart.singleton
      apply Regex.NotOr.star
    case neg h =>
      simp only
      split_ifs
      case pos h =>
        exact OrIsSmart.lastcons y1 y2 lty1y2 hy1 hy2
      case pos hneq hlt =>
        rw [insertOr]
        · have hhy1 := SmartOrElem_implies_NotOr hy1
          have hhy2 := SmartOrElem_implies_NotOr hy2
          have hh := mkOr_makes_smartOr hx hhy2
          have h := neq_of_beq h
          split_ifs
          apply @OrIsSmart.cons_mkOr α _ _ y1 x y2 hy1 hh hx h hy2 hlt lty1y2
        · intro y21 y22 hh
          rw [hh] at hy2
          contradiction
      case neg hneq hnlt =>
        have hgt := not_less_than_is_greater_than hneq hnlt
        apply consOr_makes_smartOr hx ?_ hgt
        apply OrIsSmart.lastcons y1 y2 lty1y2 hy1 hy2
  | cons y1 y21 y22 hlt hy1 hy2 ih =>
    unfold insertOr
    split_ifs
    case pos h =>
      have h := eq_of_beq h
      rw [h]
      apply OrIsSmart.singleton
      apply Regex.NotOr.star
    case neg h =>
      simp only
      split_ifs
      case pos h =>
        rw [<- h] at ih
        apply OrIsSmart.cons y1 y21 y22 hlt hy1 hy2
      case pos h h' h'' =>
        have h := neq_of_beq h
        apply OrIsSmart.cons_insertOr hy1 hx h ih h'' hlt
      case neg h =>
        rename_i h'
        have hgt := not_less_than_is_greater_than h' h
        apply consOr_makes_smartOr hx ?_ hgt
        apply OrIsSmart.cons y1 y21 y22 hlt hy1 hy2

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
  | lastcons y1 y2 lty1y2 hy1 hy2 =>
    unfold mergeOr
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
      apply OrIsSmart.lastcons y1 y2 lty1y2 hy1 hy2
  | cons y1 y21 y22 hlt hy1 hy2 ih =>
    have hny1 := SmartOrElem_implies_NotOr hy1
    unfold mergeOr
    split
    next _ x1 x2 =>
      apply insertOr_preserves_smartOr hny1 ih
    next _ h hn =>
      have hn := Regex.NotOr.split.otherwise hn
      apply insertOr_preserves_smartOr
      · exact hn
      · apply OrIsSmart.cons _ _ _ hlt hy1 hy2
