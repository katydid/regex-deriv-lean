import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.SmartRegex

open SmartRegex

def Regex.isOr (x: Regex α) : Prop :=
  ∃ x1 x2, x = Regex.or x1 x2

def Regex.isLeftNestedOr (x: Regex α) : Prop :=
  ∃ x1 x2 x3, x = Regex.or (Regex.or x1 x2) x3

def Regex.isTerminatingSmartOr [LT (Regex α)] (x: Regex α): Prop :=
  ∃ x1 x2,
    x = Regex.or x1 x2
    /\ Not (Regex.isOr x1)
    /\ Not (Regex.isOr x2)
    /\ x1 ≠ Regex.star (Regex.any)
    /\ x2 ≠ Regex.star (Regex.any)
    /\ x1 ≠ Regex.emptyset
    /\ x2 ≠ Regex.emptyset
    /\ x1 < x2

def OrIsSortedNoDup [Ord α] (x: Regex α) : Prop :=
  match x with
  | Regex.or (Regex.or _ _) _ =>
    False
  | Regex.or x1 (Regex.or x21 x22) =>
    Ord.compare x1 x21 = Ordering.lt /\ OrIsSortedNoDup (Regex.or x21 x22)
  | Regex.or x1 x2 =>
    Ord.compare x1 x2 = Ordering.lt
  | _ => True

def OrContainsStarAny (x: Regex α) : Prop :=
  match x with
  | Regex.or (Regex.star Regex.any) _ =>
    True
  | Regex.or _ (Regex.star Regex.any) =>
    True
  | Regex.or _ x2 =>
    OrContainsStarAny x2
  | _ =>
    False

def OrContainsEmptyset (x: Regex α) : Prop :=
  match x with
  | Regex.or Regex.emptyset _ =>
    True
  | Regex.or _ Regex.emptyset =>
    True
  | Regex.or _ x2 =>
    OrContainsEmptyset x2
  | _ =>
    False

def OrIsSmart [Ord α] (x: Regex α) : Prop :=
  (OrIsSortedNoDup x) /\
  (Not (OrContainsStarAny x)) /\
  (Not (OrContainsEmptyset x))

def mkOr [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  if x = y
  then x
  else if x < y
  then Regex.or x y
  else Regex.or y x

theorem mkOr_is_correct_denote {α: Type} [o: Ord α] [dr: DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (mkOr x y) := by
  unfold mkOr
  split_ifs
  · case pos h =>
    rw [h]
    apply Language.simp_or_idemp
  · case pos h =>
    rfl
  · case neg h =>
    apply Language.simp_or_comm

-- insertOr inserts y into x, where x might be or expression and y is not.
-- It inserts y into x if y is not a duplicate found in the or expression of x.
-- It inserts y into x into a sorted position in the or expression of x.
-- example:
--   insertOr (Regex.or a c) b = Regex.or a (Regex.or b c)
--   insertOr (Regex.or a c) a = Regex.or a c
--   insertOr a b = Regex.or a b
--   insertOr a a = a
def insertOr [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match x with
  | Regex.or x1 x2 =>
    if x1 = y
    then x
    else if x1 < y
    then Regex.or x (insertOr x2 y)
    else Regex.or x1 (Regex.or y x2)
  | _ =>
    mkOr x y

theorem Regex.simp_or_comm {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (Regex.or y x) := by
  simp only [denote]
  apply Language.simp_or_comm

theorem insertOr_is_correct_denote {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (insertOr x y) := by
  induction x with
  | or x1 x2 ih1 ih2 =>
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
      ac_rfl
  | _ =>
    apply mkOr_is_correct_denote

def mergeOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match x with
  | Regex.or x1 x2 =>
    match y with
    | Regex.or _ _ =>
      insertOr (mergeOr x2 y) x1
    | _ => insertOr x y
  | _ => insertOr y x

theorem mergeOr_is_correct_denote {α: Type} [Ord α] [DecidableEq α] (x y: Regex α):
  denote (Regex.or x y) = denote (mergeOr x y) := by
  induction x generalizing y with
  | or x1 x2 ihx1 ihx2 =>
    induction y with
    | or y1 y2 ihy1 ihy2 =>
      rw [mergeOr]
      repeat rw [denote]
      rw [<- insertOr_is_correct_denote]
      repeat rw [denote]
      rw [<- ihx2]
      repeat rw [denote]
      ac_rfl
    | _ =>
      apply insertOr_is_correct_denote
  | _ =>
    simp [mergeOr]
    rw [Regex.simp_or_comm]
    apply insertOr_is_correct_denote

theorem mergeOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (mergeOr x y) := by
  sorry

def smartOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | Regex.star Regex.any => Regex.star Regex.any
  | Regex.or _ _ =>
    match y with
    | Regex.emptyset => x
    | Regex.star Regex.any => Regex.star Regex.any
    | Regex.or _ _ =>
      mergeOr x y
    | _ =>
      insertOr x y
  | x' =>
    match y with
    | Regex.emptyset => x'
    | Regex.star Regex.any => Regex.star Regex.any
    | Regex.or y1 y2 =>
      insertOr (Regex.or y1 y2) x'
    | y' =>
      Regex.or x' y'

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
      rw [<- insertOr_is_correct_denote]
      simp only [denote]
      ac_rfl
    · rfl

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
      rw [<- insertOr_is_correct_denote]
    · rfl

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
      rw [smartOr]
      simp only [denote]
      ac_rfl
    | star _ =>
      apply smartOr_is_correct_denote_star_r
    | or y1 y2 ihy1 ihy2 =>
      unfold smartOr
      simp only
      rw [<- mergeOr_is_correct_denote]
    | _ =>
      unfold smartOr
      simp only
      rw [<- insertOr_is_correct_denote]
  | _ =>
    induction y with
    | emptyset =>
      rw [smartOr] <;> (intros ; try contradiction)
      · simp only [denote]
        ac_rfl
    | star _ =>
      apply smartOr_is_correct_denote_star_r
    | or y1 y1 ihy1 ihy2 =>
      unfold smartOr
      simp only
      rw [<- insertOr_is_correct_denote]
      simp only [denote]
      ac_rfl
    | _ =>
      rw [smartOr] <;> simp only [reduceCtorEq, imp_self, implies_true]


theorem smartOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (smartOr x y) := by
  sorry
