import Katydid.Std.Linter.DetectClassical

import Katydid.Std.NonEmptyList
import Katydid.Regex.SmartRegex

open List
open SmartRegex

def orToList (x: Regex α): NonEmptyList (Regex α) :=
  match x with
  | Regex.or x1 x2 =>
    -- smartOr guarantees that left hand side will not be an Regex.or so a recursive call is only required on the right hand side.
    NonEmptyList.cons x1 (orToList x2)
  | _ =>
    NonEmptyList.mk x []

private def orFromList' (x1: Regex α) (xs: List (Regex α)): Regex α :=
  match xs with
  | [] => x1
  | (x2::xs') => Regex.or x1 (orFromList' x2 xs')

def orFromList (xs: NonEmptyList (Regex α)): Regex α :=
  match xs with
  | NonEmptyList.mk x1 xs' => orFromList' x1 xs'

theorem orToList_is_orFromList (x: Regex α):
  orFromList (orToList x) = x := by
  induction x <;> (try simp only [orToList, orFromList, orFromList'])
  · case or x1 x2 ih1 ih2 =>
    rw [NonEmptyList.cons_head]
    congr

theorem simp_star_pred_any_is_universal {α: Type}:
  denote (Regex.star (@Regex.any α)) = Language.universal := by
  unfold denote
  exact Language.simp_star_any_is_universal

theorem simp_or_universal_r_is_universal [Ord α] (x: Regex α):
  denote (Regex.or x (Regex.star Regex.any)) = Language.universal := by
  nth_rewrite 1 [denote]
  rw [simp_star_pred_any_is_universal]
  rw [Language.simp_or_universal_r_is_universal]

theorem simp_or_universal_l_is_universal [Ord α] (x: Regex α):
  denote (Regex.or (Regex.star Regex.any) x) = Language.universal := by
  nth_rewrite 1 [denote]
  rw [simp_star_pred_any_is_universal]
  rw [Language.simp_or_universal_l_is_universal]

-- 1. If x or y is emptyset then return the other (Language.simp_or_emptyset_r_is_l and Language.simp_or_emptyset_l_is_r)
-- 2. If x or y is star (any) then return star (any) (Language.simp_or_universal_r_is_universal and Language.simp_or_universal_l_is_universal)
-- 3. Get the lists of ors using orToList (Language.simp_or_assoc)
-- 4. Merge sort the sorrted lists (Language.simp_or_comm and Language.simp_or_assoc)
-- 5. Remove duplicates from the list (or create a set) (Language.simp_or_idemp)
-- 6. If at any following step the set is size one, simply return
-- TODO: 7. If any of the set is nullable, remove emptystr from the set (Language.simp_or_emptystr_null_r_is_r and Language.simp_or_null_l_emptystr_is_l)
-- 8. Reconstruct Regex.or from the list using orFromList (Language.simp_or_assoc)
def smartOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | Regex.star Regex.any => x
  | _ =>
  match y with
  | Regex.emptyset => x
  | Regex.star Regex.any => y
  | _ =>
    let xs := orToList x
    let ys := orToList y
    -- It is implied that xs is sorted, given it was created using smartOr.
    -- Merge the sorted lists and remove duplicates, resulting in a sorted list of unique items.
    let ors := NonEmptyList.mergeReps xs ys
    orFromList ors

private lemma smartOr_emptyset_l_is_r (x: Regex α):
  denote (Regex.or Regex.emptyset x) = denote (smartOr Regex.emptyset x) := by
  simp only [smartOr]
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_l_is_r]

private lemma smartOr_emptyset_r_is_l':
  smartOr x Regex.emptyset = x := by
  simp only [smartOr]
  split <;> rfl

private lemma smartOr_emptyset_r_is_l (x: Regex α):
  denote (Regex.or x Regex.emptyset) = denote (smartOr x Regex.emptyset) := by
  nth_rewrite 1 [denote]
  nth_rewrite 1 [denote]
  rw [Language.simp_or_emptyset_r_is_l]
  rw [smartOr_emptyset_r_is_l']

private lemma smartOr_orFromList_mergeReps_orToList_is_or (x y: Regex α):
  denote (orFromList (NonEmptyList.mergeReps (orToList x) (orToList y))) = denote (Regex.or x y):= by
  induction x with
  | emptyset =>
    simp only [orToList, orFromList]
    cases y with
    | emptyset =>
      sorry
    | emptystr =>
      sorry
    | any =>
      sorry
    | pred _ =>
      sorry
    | or x1 x2 =>
      sorry
    | concat x1 x2 =>
      sorry
    | star x1 =>
      sorry
  | emptystr =>
    sorry
  | any =>
    sorry
  | pred _ =>
    sorry
  | or x1 x2 =>
    sorry
  | concat x1 x2 =>
    sorry
  | star x1 =>
    sorry

lemma simp_or_x_star_any_is_star_any {x: Regex α}:
  denote (Regex.or x (Regex.star Regex.any)) = denote (Regex.star Regex.any) := by
  unfold denote
  unfold denote
  unfold denote
  rw [Language.simp_star_any_is_universal]
  rw [Language.simp_or_universal_r_is_universal]

lemma simp_or_star_any_x_is_star_any {x: Regex α}:
  denote (Regex.or (Regex.star Regex.any) x) = denote (Regex.star Regex.any) := by
  unfold denote
  unfold denote
  unfold denote
  rw [Language.simp_star_any_is_universal]
  rw [Language.simp_or_universal_l_is_universal]

private lemma smartOr_emptystr_is_or (y: Regex α):
  denote (Regex.or Regex.emptystr y) = denote (smartOr Regex.emptystr y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_any_is_or (y: Regex α):
  denote (Regex.or Regex.any y) = denote (smartOr Regex.any y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_pred_is_or (p: Predicate α) (y: Regex α):
  denote (Regex.or (Regex.pred p) y) = denote (smartOr (Regex.pred p) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_star_is_or (x y: Regex α):
  denote (Regex.or (Regex.star x) y) = denote (smartOr (Regex.star x) y) := by
  cases x with
  | any =>
    simp only [smartOr]
    rw [simp_or_star_any_x_is_star_any]
  | _ =>
    cases y with
    | emptyset =>
      rw [smartOr_emptyset_r_is_l]
    | star y1 =>
      cases y1 with
      | any =>
        simp only [smartOr]
        rw [simp_or_x_star_any_is_star_any]
      | _ =>
        simp only [smartOr]
        rw [smartOr_orFromList_mergeReps_orToList_is_or]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_concat_is_or (x1 x2 y: Regex α):
  denote (Regex.or (Regex.concat x1 x2) y) = denote (smartOr (Regex.concat x1 x2) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

private lemma smartOr_or_is_or (x1 x2 y: Regex α):
  denote (Regex.or (Regex.or x1 x2) y) = denote (smartOr (Regex.or x1 x2) y) := by
  cases y with
  | emptyset =>
    rw [smartOr_emptyset_r_is_l]
  | star y1 =>
    cases y1 with
    | any =>
      simp only [smartOr]
      rw [simp_or_x_star_any_is_star_any]
    | _ =>
      simp only [smartOr]
      rw [smartOr_orFromList_mergeReps_orToList_is_or]
  | _ =>
    simp only [smartOr]
    rw [smartOr_orFromList_mergeReps_orToList_is_or]

theorem smartOr_is_or (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  induction x with
  | emptyset =>
    apply smartOr_emptyset_l_is_r
  | emptystr =>
    apply smartOr_emptystr_is_or
  | any =>
    apply smartOr_any_is_or
  | pred p =>
    apply smartOr_pred_is_or
  | or x1 x2 ih1 ih2 =>
    apply smartOr_or_is_or
  | concat x1 x2 =>
    apply smartOr_concat_is_or
  | star x1 =>
    apply smartOr_star_is_or
