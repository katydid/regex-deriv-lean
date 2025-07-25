import RegexDeriv.Std.Linter.DetectClassical

import RegexDeriv.Std.Ordering

import RegexDeriv.Regex.Smart.SmartRegex

open SmartRegex

theorem Regex.simp_or_comm {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (Regex.or y x) := by
  simp only [denote]
  apply Language.simp_or_comm

theorem insertOr_is_correct_denote {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (insertOr x y) := by
  induction y with
  | or y1 y2 ih1 ih2 =>
    unfold insertOr
    split_ifs
    · case pos h =>
      rw [h]
      simp only [denote]
      ac_rfl
    · case pos h =>
      simp only [denote]
      rw [<- ih2]
      simp only [denote]
      ac_rfl
    · case neg h =>
      simp only [denote]
  | _ =>
    unfold insertOr
    simp only [denote]
    split_ifs
      <;> subst_vars
      <;> simp only [denote]
      <;> ac_rfl

theorem mergeOr_is_correct_denote {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (mergeOr x y) := by
  induction y with
  | or y1 y2 ihy1 ihy2 =>
    cases x with
    | or x1 x2 =>
      rw [mergeOr]
      repeat rw [denote]
      rw [<- insertOr_is_correct_denote]
      repeat rw [denote]
      rw [<- ihy2]
      repeat rw [denote]
      ac_rfl
    | _ =>
      apply insertOr_is_correct_denote
  | _ =>
    simp [mergeOr]
    rw [Regex.simp_or_comm]
    apply insertOr_is_correct_denote

example {α: Type} [Ord α] [DecidableEq α]: (h: (@Regex.star α Regex.emptyset) = (Regex.star Regex.any)) -> False := by
  intro h
  simp at *

theorem smartOr_is_correct_denote_star_l {α: Type} [Ord α] [DecidableEq α] (x1 y: Regex α):
  denote (Regex.or (Regex.star x1) y) = denote (smartOr (Regex.star x1) y) := by
  cases x1 with
  | any =>
    simp only [denote]
    apply Language.simp_or_star_any_l_is_star_any
  | _ =>
    unfold smartOr
    simp only
    split
    · simp only [denote]
      apply Language.simp_or_emptyset_r_is_l
    · simp only [denote]
      apply Language.simp_or_star_any_r_is_star_any
    · rename_i y1 y2
      rw [mergeOr_is_correct_denote]

theorem smartOr_is_correct_denote_star_r {α: Type} [Ord α] [DecidableEq α] (x y1: Regex α):
  denote (Regex.or x (Regex.star y1)) = denote (smartOr x (Regex.star y1)) := by
  cases y1 with
  | any =>
    unfold smartOr
    simp only [denote]
    rw [Language.simp_or_star_any_r_is_star_any]
    split <;> simp only [denote]
  | _ =>
    unfold smartOr
    simp only
    split
    · simp only [denote]
      apply Language.simp_or_emptyset_l_is_r
    · simp only [denote]
      apply Language.simp_or_star_any_l_is_star_any
    · rename_i y1 y2
      rw [mergeOr_is_correct_denote]

theorem smartOr_is_correct_denote {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  induction x with
  | emptyset =>
    rw [smartOr]
    simp only [denote]
    ac_rfl
  | star x1 =>
    apply smartOr_is_correct_denote_star_l
  | or x1 x2 ihx1 ihx2 =>
    induction y with
    | emptyset =>
      simp only [smartOr]
      simp only [denote]
      ac_rfl
    | star _ =>
      apply smartOr_is_correct_denote_star_r
    | _ =>
      unfold smartOr
      rw [mergeOr_is_correct_denote]
  | _ =>
    induction y with
    | emptyset =>
      rw [smartOr] <;> (intros ; try contradiction)
      simp only [denote]
      ac_rfl
    | star _ =>
      apply smartOr_is_correct_denote_star_r
    | _ =>
      unfold smartOr
      rw [mergeOr_is_correct_denote]
