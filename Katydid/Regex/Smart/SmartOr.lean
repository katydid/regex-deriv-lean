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
        · admit
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
        · admit
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
        · admit
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
        · admit
        · constructor
    · case star =>
      split_ifs
      case pos h =>
        apply OrIsSmart.singleton
        constructor
      case pos h =>
        apply OrIsSmart.lastcons <;> try assumption
        constructor
        admit
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · admit
        · constructor
          admit
  | lastcons h =>
    sorry
  | cons h =>
    sorry

lemma mergeOr_or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2 y: Regex α):
  mergeOr (Regex.or x1 x2) y ≠ Regex.emptyset := by
  sorry

lemma mergeOr_or_neq_star_any
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2 y: Regex α):
  mergeOr (Regex.or x1 x2) y ≠ Regex.star Regex.any := by
  sorry

lemma or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2: Regex α):
  Regex.or x1 x2 ≠ Regex.emptyset := by
  sorry

lemma or_neq_star_any
  {α: Type} [Ord α] [DecidableEq α]
  (x1 x2: Regex α):
  Regex.or x1 x2 ≠ Regex.star Regex.any := by
  sorry

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
      · apply mergeOr_or_neq_emptyset
      · apply mergeOr_or_neq_star_any
    | cons x1 x21 x22 hlt hx1 hx2 =>
      unfold mergeOr
      simp only
      have hny1 := SmartOrElem_implies_NotOr hy1
      have hny2 := SmartOrElem_implies_NotOr hy2
      apply insertOr_preserves_smartOr hy1
      · unfold mergeOr
        simp only
        cases hny2: hny2 <;> simp only <;> apply insertOr_preserves_smartOr <;> assumption
      · apply mergeOr_or_neq_emptyset
      · apply mergeOr_or_neq_star_any
  | cons y1 y21 y22 hlt hy1 hy2 ih =>
    have hny1 := SmartOrElem_implies_NotOr hy1
    unfold mergeOr
    split
    next _ x1 x2 =>
      have ih' := ih ?_ ?_ hy2 rfl
      apply insertOr_preserves_smartOr hy1 ih'
      · apply mergeOr_or_neq_emptyset
      · apply mergeOr_or_neq_star_any
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
  sorry
