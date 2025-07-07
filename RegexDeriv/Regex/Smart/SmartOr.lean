import RegexDeriv.Std.Linter.DetectClassical

import RegexDeriv.Std.Ordering

import RegexDeriv.Regex.Smart.SmartRegex
import RegexDeriv.Regex.Smart.SmartOrElem
import RegexDeriv.Regex.Smart.LawfulEqOrd

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

lemma neq_star_any: Regex.star x ≠ Regex.star Regex.any <-> x ≠ Regex.any := by
  apply Iff.intro
  case mp =>
    intro h
    simp at h
    assumption
  case mpr =>
    intro h
    intro h'
    apply h
    cases h'
    rfl

theorem insertOr_preverves_or
  {α: Type} [Ord α] [DecidableEq α]
  {x yz: Regex α}
  (hyz: Regex.isOr yz):
  Regex.isOr (insertOr x yz) := by
  cases hyz
  case intro y h =>
  cases h
  case intro z h =>
  rw [h]
  unfold insertOr
  split_ifs
  case pos h =>
    unfold Regex.isOr
    exists y
    exists z
  case pos h =>
    unfold Regex.isOr
    exists y
    exists (insertOr x z)
  case neg h =>
    unfold Regex.isOr
    exists x
    exists (Regex.or y z)

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
        apply neq_star_any.mp hy_starany
      case neg h =>
        apply OrIsSmart.lastcons <;> try assumption
        rename_i h'
        · apply not_less_than_is_greater_than ?_ h
          symm
          assumption
        · constructor
          apply neq_star_any.mp hy_starany
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

lemma insertOr_SmartOrElem_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: Regex.SmartOrElem y):
  insertOr x y ≠ Regex.emptyset := by
  unfold insertOr
  cases hy
    <;> simp only
    <;> cases hx
    <;> split_ifs
    <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

lemma insertOr_SmartOrElem_neq_is_or
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: Regex.SmartOrElem y)
  (hxy: x ≠ y):
  Regex.isOr (insertOr x y) := by
  unfold insertOr
  cases hy
    <;> simp only
    <;> cases hx
    <;> split_ifs
    <;> unfold Regex.isOr
    <;> (try trivial)
    <;> simp only [Regex.or.injEq, exists_and_left, exists_eq', and_true]

lemma insertOr_SmartOrElem_neq_is_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: Regex.SmartOrElem y)
  (hxy: x ≠ y):
  insertOr x y ≠ Regex.emptyset := by
  have h := insertOr_SmartOrElem_neq_is_or hx hy hxy
  cases h
  case intro x h =>
  cases h
  case intro y h =>
  rw [h]
  intro h'
  cases h'

lemma insertOr_SmartOrElem_neq_star_any
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.SmartOrElem x)
  (hy: Regex.SmartOrElem y):
  insertOr x y ≠ Regex.star Regex.any := by
  unfold insertOr
  cases hy
    <;> simp only
    <;> cases hx
    <;> split_ifs
    <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true, neq_star_any]
    <;> trivial

lemma insertOr_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hxe: x ≠ Regex.emptyset)
  (hxo: Regex.NotOr x)
  (hye: y ≠ Regex.emptyset)
  (hyo: Regex.NotOr y):
  insertOr x y ≠ Regex.emptyset := by
  unfold insertOr
  cases hyo
    <;> simp only
    <;> cases hxo
    <;> (try trivial)
    <;> split_ifs
    <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

lemma insertOr_or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y: Regex α}
  (_hx: OrIsSmart (Regex.or x1 x2))
  (_hy: Regex.SmartOrElem y):
  insertOr y (Regex.or x1 x2) ≠ Regex.emptyset := by
  unfold insertOr
  split_ifs <;> simp

lemma mergeOr_or_neq_emptyset
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: Regex.SmartOrElem y):
  mergeOr (Regex.or x1 x2) y ≠ Regex.emptyset := by
  unfold mergeOr
  simp only
  cases hy
  <;> simp only
  <;> apply insertOr_or_neq_emptyset hx ?_
  <;> try constructor <;> assumption

lemma insertOr_comm
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}
  (hx: Regex.NotOr x)
  (hy: Regex.NotOr y):
  insertOr x y = insertOr y x := by
  unfold insertOr
  have himpossible := @lt_and_gt_is_impossible (Regex α) _ _ x y
  have heq := @not_lt_and_not_gt_is_eq (Regex α) _ _ x y
  cases hx
  <;> (try simp only)
  <;> cases hy
  <;> (try trivial)
  <;> split_ifs
  <;> (try trivial)
  <;> (try simp only)
  <;> (try nomatch (himpossible (by assumption) (by assumption)))
  <;> (try (cases (heq (by assumption) (by assumption))))
  <;> (try (subst_eqs; contradiction))

lemma mergeOr_comm
  {α: Type} [Ord α] [DecidableEq α]
  {x y: Regex α}:
  mergeOr x y = mergeOr y x := by
  induction x generalizing y with
  | emptyset =>
    have hi := @insertOr_comm _ _ _ Regex.emptyset y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
    | emptystr =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | any =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor
  | emptystr =>
    have hi := @insertOr_comm _ _ _ Regex.emptystr y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | emptystr =>
      simp only
    | any =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor
  | any =>
    have hi := @insertOr_comm _ _ _ Regex.any y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | emptystr =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | any =>
      simp only
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor
  | pred px =>
    have hi := @insertOr_comm _ _ _ (Regex.pred px) y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | emptystr =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | any =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor
  | or x1 x2 ihx1 ihx2 =>
    induction y with
    | emptyset =>
      unfold mergeOr
      simp only
    | emptystr =>
      unfold mergeOr
      simp only
    | any =>
      unfold mergeOr
      simp only
    | pred py =>
      unfold mergeOr
      simp only
    | or y1 y2 ihy1 ihy2 =>
      have ihx2' := @ihx2 (Regex.or y1 y2)
      unfold mergeOr
      simp only
      rw [ihy2]
      rw [<- ihx2]
      unfold mergeOr
      rw [<- ihx2]
      sorry
    | concat y1 y2 =>
      unfold mergeOr
      simp only
    | star y1 =>
      unfold mergeOr
      simp only
  | concat x1 x2 =>
    have hi := @insertOr_comm _ _ _ (Regex.concat x1 x2) y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | emptystr =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | any =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor
  | star x1 =>
    have hi := @insertOr_comm _ _ _ (Regex.star x1) y
    unfold mergeOr
    simp only
    cases y with
    | emptyset =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | emptystr =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | any =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | pred py =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | or y1 y2 =>
      simp only
    | concat y1 y2 =>
      simp only
      symm
      apply hi
      constructor
      constructor
    | star y1 =>
      simp only
      symm
      apply hi
      constructor
      constructor

lemma mergeOr_or_neq_emptyset_or
  {α: Type} [Ord α] [DecidableEq α]
  {x1 x2 y1 y2: Regex α}
  (hx: OrIsSmart (Regex.or x1 x2))
  (hy: OrIsSmart (Regex.or y1 y2)):
  mergeOr (Regex.or x1 x2) (Regex.or y1 y2) ≠ Regex.emptyset := by
  unfold mergeOr
  simp only
  have hy1: Regex.SmartOrElem y1 := by cases hy <;> trivial
  have hx1: Regex.SmartOrElem x1 := by cases hx <;> trivial
  unfold mergeOr
  simp only
  cases y2 <;> simp only <;> sorry


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
