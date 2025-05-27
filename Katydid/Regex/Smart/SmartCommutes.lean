import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex
import Katydid.Regex.Smart.SmartCommutesOr

open SmartRegex
open List

-- copy of SimpleRegex.null_commutes
theorem null_commutes {α: Type} [Ord α] (r: Regex α):
  ((null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | any =>
    unfold denote
    rw [Language.null_any]
    unfold null
    simp only [Bool.false_eq_true]
  | pred p =>
    unfold denote
    rw [Language.null_pred]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold null
    simp only

theorem smartStar_is_star [Ord α] (x: Regex α):
  denote (Regex.star x) = denote (smartStar x) := by
  cases x with
  | emptyset =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptyset_is_emptystr]
  | emptystr =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptystr_is_emptystr]
  | any =>
    simp only [smartStar]
  | pred p =>
    simp only [smartStar]
  | concat x1 x2 =>
    simp only [smartStar]
  | or x1 x2 =>
    simp only [smartStar]
  | star x' =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_star_is_star]

theorem smartConcat_is_concat {α: Type} [Ord α] (x y: Regex α):
  denote (Regex.concat x y) = denote (smartConcat x y) := by
  cases x with
  | emptyset =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptyset_l_is_emptyset (denote y)
  | emptystr =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptystr_l_is_r (denote y)
  | any =>
    cases y <;> simp only [denote, smartConcat]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | pred p =>
    cases y <;> simp only [denote, smartConcat]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | or x1 x2 =>
    cases y <;> simp only [denote, smartConcat]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | concat x1 x2 =>
    unfold smartConcat
    simp only [denote]
    rw [<- smartConcat_is_concat x2 y]
    simp only [denote]
    rw [Language.simp_concat_assoc]
  | star x1 =>
    cases y <;> simp only [denote, smartConcat]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l

lemma derive_commutes_emptyset [Ord α] [DecidableEq α] {x: α}:
  denote (derive Regex.emptyset x) = Language.derive (denote Regex.emptyset) x := by
  funext xs
  simp only [derive, denote, Language.emptyset, Language.derive, Language.derives]

lemma derive_commutes_emptystr [Ord α] [DecidableEq α] {x: α}:
  denote (derive Regex.emptystr x) = Language.derive (denote Regex.emptystr) x := by
  funext xs
  simp only [
    denote,
    derive,
    Language.emptyset, Language.derive, Language.derives, Language.emptystr,
    singleton_append,
    reduceCtorEq,
  ]

lemma derive_commutes_any [Ord α] [DecidableEq α] {x: α}:
  denote (derive Regex.any x) = Language.derive (denote Regex.any) x := by
  funext xs
  unfold derive
  unfold denote
  unfold Language.any
  simp only [Language.emptystr, Language.derive, Language.derives, singleton_append, cons.injEq,
    exists_and_right, exists_eq', true_and]

lemma derive_commutes_pred [Ord α] [DecidableEq α] {p: Predicate.Pred α} {x: α}:
  denote (derive (Regex.pred p) x) = Language.derive (denote (Regex.pred p)) x := by
  funext xs
  simp only [derive, Language.derive, Language.derives, denote, singleton_append, eq_iff_iff]
  rw [onlyif', Language.pred]
  split_ifs with h
  · rw [denote]
    simp only [Language.emptystr, cons.injEq]
    apply Iff.intro
    · intro hxs
      use x
    · intro ⟨w, hxs, hp⟩
      exact hxs.right
  · rw [denote]
    simp only [Language.emptyset, cons.injEq, false_iff, not_exists, not_and, and_imp, forall_eq']
    intro _ h'
    contradiction

theorem smartOr_is_or {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  apply smartOr_is_correct_denote

lemma derive_commutes_or [Ord α] [DecidableEq α] {r1 r2: Regex α} {x: α}
  (ih1: denote (derive r1 x) = Language.derive (denote r1) x)
  (ih2: denote (derive r2 x) = Language.derive (denote r2) x):
  denote (derive (Regex.or r1 r2) x) = Language.derive (denote (r1.or r2)) x := by
  funext xs
  simp only [derive, Language.derive, Language.derives, denote, Language.or, singleton_append,
    eq_iff_iff]
  rw [←smartOr_is_or, denote, Language.or]
  rw [ih1, ih2]
  rfl

lemma derive_commutes_concat [Ord α] [DecidableEq α] {r1 r2: Regex α} {x: α}
  (ih1 : denote (derive r1 x) = Language.derive (denote r1) x)
  (ih2 : denote (derive r2 x) = Language.derive (denote r2) x):
  denote (derive (r1.concat r2) x) = Language.derive (denote (r1.concat r2)) x := by
  funext xs
  simp [derive, denote]
  rw [←smartOr_is_or, denote, Language.or]
  rw [←smartConcat_is_concat]
  simp only [denote, Language.concat, exists_and_left]
  apply Iff.intro
  · intro h
    match h with
    | Or.inl ⟨ys, h, zs, h', hxs⟩ =>
      rw [ih1] at h
      rw [Language.derive, Language.derives, singleton_append] at h
      refine ⟨x::ys, h, zs, h', ?_⟩
      rw [hxs, cons_append]
    | Or.inr h =>
      rw [onlyif] at h
      split_ifs at h with hn
      · rw [null_commutes, Language.null] at hn
        rw [ih2] at h
        rw [Language.derive, Language.derives, singleton_append] at h
        refine ⟨[], hn, x::xs, h, ?_⟩
        rw [nil_append]
      · simp only [denote, Language.emptyset] at h
  · intro ⟨ys, h, zs, h', hxs⟩
    rw [ih1]
    simp only [Language.derive, Language.derives, singleton_append]
    cases ys with
    | nil =>
      rw [nil_append] at hxs
      rw [onlyif]
      split_ifs with hn
      · rw [ih2]
        rw [Language.derive, Language.derives, singleton_append, hxs]
        exact Or.inr h'
      · rw [null_commutes, Language.null] at hn
        contradiction
    | cons w ws =>
      rw [cons_append, cons.injEq] at hxs
      rw [hxs.left]
      exact Or.inl ⟨ws, h, zs, h', hxs.right⟩

lemma derive_commutes_star [Ord α] [DecidableEq α] {r: Regex α} {x: α}
  (ih : denote (derive r x) = Language.derive (denote r) x):
  denote (derive r.star x) = Language.derive (denote r.star) x := by
  funext xs
  simp [derive, denote]
  rw [←smartConcat_is_concat]
  simp only [denote, Language.concat, exists_and_left]
  apply Iff.intro
  · intro ⟨ys, h, zs, h', hxs⟩
    rw [ih] at h
    rw [Language.derive, Language.derives, singleton_append] at h
    apply Language.star.more x ys zs
    rw [hxs, cons_append]
    exact h
    exact h'
  · intro h
    cases h with
    | more y ys zs _ hxs h h'  =>
      rw [cons_append, cons.injEq] at hxs
      rw [ih, hxs.left]
      exact ⟨ys, h, zs, h', hxs.right⟩

theorem derive_commutes {α: Type} [Ord α] [DecidableEq α] (r: Regex α) (x: α):
  denote (derive r x) = Language.derive (denote r) x := by
  induction r with
  | emptyset =>
    exact derive_commutes_emptyset
  | emptystr =>
    exact derive_commutes_emptystr
  | any =>
    exact derive_commutes_any
  | pred p =>
    exact derive_commutes_pred
  | or r1 r2 ih1 ih2 =>
    exact derive_commutes_or ih1 ih2
  | concat r1 r2 ih1 ih2 =>
    exact derive_commutes_concat ih1 ih2
  | star r ih =>
    exact derive_commutes_star ih

-- copy of SimpleRegex.derives_commutes
theorem derives_commutes {α: Type} [Ord α] [DecidableEq α] (r: Regex α) (xs: List α):
  denote (derives r xs) = Language.derives (denote r) xs := by
  unfold derives
  rw [Language.derives_foldl]
  revert r
  induction xs with
  | nil =>
    simp only [foldl_nil]
    intro h
    exact True.intro
  | cons x xs ih =>
    simp only [foldl_cons]
    intro r
    have h := derive_commutes r x
    have ih' := ih (derive r x)
    rw [h] at ih'
    exact ih'

-- copy of SimpleRegex.validate_commutes
theorem validate_commutes {α: Type} [Ord α] [DecidableEq α] (r: Regex α) (xs: List α):
  (validate r xs = true) = (denote r) xs := by
  rw [<- Language.validate (denote r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- copy of SimpleRegex.decidableDenote
def decidableDenote [Ord α] [DecidableEq α] (r: Regex α): DecidablePred (denote r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes r xs)
