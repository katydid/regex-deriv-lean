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

lemma neq_star_any (h: Regex.star x ≠ Regex.star Regex.any): x ≠ Regex.any := by
  simp at h
  assumption

theorem insertOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: OrIsSmart y)
  (hy_emptyset: y ≠ Regex.emptyset)
  (hy_starany: y ≠ Regex.star Regex.any):
  OrIsSmart (insertOr x y) := by
  induction hy: hy with
  | singleton y h =>
    unfold insertOr
    cases h <;> simp only <;> try contradiction
    · case emptystr =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          apply not_eq_is_neq.mp
          assumption
        · constructor
    · case any =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          assumption
        · constructor
    · case pred =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          assumption
        · constructor
    · case concat =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          assumption
        · constructor
    · case star =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
        apply neq_star_any hy_starany
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          assumption
        · constructor
          apply neq_star_any hy_starany
  | lastcons y1 y2 lty1y2 hy1 hy2 =>
    unfold insertOr
    split_ifs
    case pos h => -- x = y1
      assumption
    case pos h => -- y1 < x
      unfold insertOr
      split_ifs
      case pos h => -- x = y2
        cases hy2 <;> simp only <;> assumption
      case pos h => -- y2 < x
        cases hy2 <;> simp only
        case emptystr =>
          apply OrIsSmart.cons y1 Regex.emptystr x lty1y2 hy1
          apply OrIsSmart.lastcons Regex.emptystr x h (by constructor) hx
        case any =>
          apply OrIsSmart.cons y1 Regex.any x lty1y2 hy1
          apply OrIsSmart.lastcons Regex.any x h (by constructor) hx
        case pred =>
          apply OrIsSmart.cons y1 (Regex.pred _) x lty1y2 hy1
          apply OrIsSmart.lastcons (Regex.pred _) x h (by constructor) hx
        case concat =>
          apply OrIsSmart.cons y1 (Regex.concat _ _) x lty1y2 hy1
          apply OrIsSmart.lastcons (Regex.concat _ _) x h (by constructor) hx
        case star =>
          apply OrIsSmart.cons y1 (Regex.star _) x lty1y2 hy1
          apply OrIsSmart.lastcons (Regex.star _) x h ?_ hx
          constructor
          assumption
      case neg h h' h'' h''' h''' h'''' => -- x < y2
        have hneq := not_eq_is_neq.mp h'''
        symm at hneq
        have hgt := not_less_than_is_greater_than hneq h''''
        cases hy2 <;> simp only
        case emptystr =>
          apply OrIsSmart.cons y1 x Regex.emptystr (by assumption) hy1
          apply OrIsSmart.lastcons x Regex.emptystr hgt hx (by constructor)
        case any =>
          apply OrIsSmart.cons y1 x Regex.any (by assumption) hy1
          apply OrIsSmart.lastcons x Regex.any hgt hx (by constructor)
        case pred =>
          apply OrIsSmart.cons y1 x (Regex.pred _) (by assumption) hy1
          apply OrIsSmart.lastcons x (Regex.pred _) hgt hx (by constructor)
        case concat =>
          apply OrIsSmart.cons y1 x (Regex.concat _ _) (by assumption) hy1
          apply OrIsSmart.lastcons x (Regex.concat _ _) hgt hx (by constructor)
        case star =>
          apply OrIsSmart.cons y1 x (Regex.star _) (by assumption) hy1
          apply OrIsSmart.lastcons x (Regex.star _) hgt hx
          constructor
          assumption
    case neg h h' => -- x < y1
      have hneq := not_eq_is_neq.mp h
      have hgt := not_less_than_is_greater_than hneq h'
      apply OrIsSmart.cons x y1 y2 hgt hx (by assumption)
  | cons y1 y21 y22 hlt hy1 hy2 ih =>
    clear hy
    rename_i hy
    have ih' := ih hy2 (by simp) (by simp) rfl
    clear ih
    unfold insertOr
    split_ifs
    case pos h => -- x = y1
      exact hy
    case pos h h' => -- y1 < x
      unfold insertOr
      split_ifs
      case pos h => -- x == y21
        exact hy
      case pos h => -- y21 < x
        apply OrIsSmart.cons y1 y21 (insertOr x y22) hlt hy1
        unfold insertOr at ih'
        split_ifs at ih'
        assumption
      case neg h =>
        apply OrIsSmart.cons y1 x (Regex.or y21 y22) h' hy1
        apply OrIsSmart.cons x y21 y22 ?_ hx hy2
        apply not_less_than_is_greater_than
        assumption
        assumption
    case neg h h' => -- y22 > x
      have hgt := not_less_than_is_greater_than h h'
      apply OrIsSmart.cons x y1 (Regex.or y21 y22) hgt hx hy

lemma mergeOr_or_neq_emptyset_or
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y1 y2: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: OrIsSmart (Regex.or y1 y2)):
  mergeOr (Regex.or x1 x2) (Regex.or y1 y2) ≠ Regex.emptyset := by
  sorry

lemma mergeOr_or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: Regex.SmartOrElem y):
  mergeOr (Regex.or x1 x2) y ≠ Regex.emptyset := by
  sorry

lemma mergeOr_or_neq_star_any_or
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: OrIsSmart y):
  mergeOr (Regex.or x1 x2) y ≠ Regex.star Regex.any := by
  sorry

lemma mergeOr_or_neq_star_any
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: Regex.SmartOrElem y):
  mergeOr (Regex.or x1 x2) y ≠ Regex.star Regex.any := by
  sorry

lemma or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2: Regex α):
  Regex.or x1 x2 ≠ Regex.emptyset := by
  simp

lemma or_neq_star_any
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2: Regex α):
  Regex.or x1 x2 ≠ Regex.star Regex.any := by
  simp

theorem mergeOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α]
  (x y: Regex α)
  (hx_emptyset: x ≠ Regex.emptyset)
  (hx_starany: x ≠ Regex.star Regex.any)
  (hy_emptyset: y ≠ Regex.emptyset)
  (hy_starany: y ≠ Regex.star Regex.any)
  (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (mergeOr x y) := by
  induction hy: hy with
  | singleton y hy' =>
    have hsmartelemy := Regex.SmartOrElem.mk hy_emptyset hy_starany hy'
    unfold mergeOr
    cases hy': hy' <;> simp only <;> apply insertOr_preserves_smartOr <;> assumption
  | lastcons y1 y2 lty1y2 hy1 hy2 =>
    cases hx: hx with
    | singleton x hx' =>
      have hsmartelemx := Regex.SmartOrElem.mk hx_emptyset hx_starany hx'
      unfold mergeOr
      cases hx': hx' <;> simp only <;> apply insertOr_preserves_smartOr <;> assumption
    | lastcons x1 x2 ltx1x2 hx1 hx2 =>
      unfold mergeOr
      simp only
      have hny1 := SmartOrElem_implies_NotOr hy1
      have hny2 := SmartOrElem_implies_NotOr hy2
      apply insertOr_preserves_smartOr hy1
      · unfold mergeOr
        simp only
        cases hy2: hy2 <;> simp only <;> apply insertOr_preserves_smartOr <;> assumption
      · apply mergeOr_or_neq_emptyset (by assumption) hy2
      · apply mergeOr_or_neq_star_any (by assumption) hy2
    | cons x1 x21 x22 hlt hx1 hx2 =>
      unfold mergeOr
      simp only
      have hny1 := SmartOrElem_implies_NotOr hy1
      have hny2 := SmartOrElem_implies_NotOr hy2
      apply insertOr_preserves_smartOr hy1
      · unfold mergeOr
        simp only
        cases hny2: hny2 <;> simp only <;> apply insertOr_preserves_smartOr <;> assumption
      · apply mergeOr_or_neq_emptyset (by assumption) hy2
      · apply mergeOr_or_neq_star_any (by assumption) hy2
  | cons y1 y21 y22 hlt hy1 hy2 ih =>
    have hny1 := SmartOrElem_implies_NotOr hy1
    unfold mergeOr
    split
    next _ x1 x2 =>
      have ih' := ih ?_ ?_ hy2 rfl
      apply insertOr_preserves_smartOr hy1 ih'
      · apply mergeOr_or_neq_emptyset_or hx hy2
      · apply mergeOr_or_neq_star_any_or hx hy2
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    next _ h hn =>
      have hn := Regex.NotOr.split.otherwise hn
      apply insertOr_preserves_smartOr
      · apply Regex.SmartOrElem.mk hx_emptyset hx_starany hn
      · apply OrIsSmart.cons _ _ _ hlt hy1 hy2
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem smartOr_preserves_smartOr
  {α: Type} [Ord α] [DecidableEq α]
  (x y: Regex α)
  (hx: OrIsSmart x) (hy: OrIsSmart y):
  OrIsSmart (smartOr x y) := by
  unfold smartOr
  split
  next =>
    exact hy
  next =>
    exact hx
  next h =>
    split
    next h =>
      exact hx
    next h =>
      exact hy
    next h =>
      apply mergeOr_preserves_smartOr <;> assumption
