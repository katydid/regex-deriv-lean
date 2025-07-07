import Mathlib.Tactic.Linarith

open Nat

theorem nat_succ_le_succ_iff (x y: Nat):
  succ x ≤ succ y <-> x ≤ y := by
  apply Iff.intro
  case mp =>
    apply Nat.le_of_succ_le_succ
  case mpr =>
    apply Nat.succ_le_succ

theorem nat_succ_eq_plus_one : succ n = n + 1 := by
  simp only

theorem nat_pred_le_succ : {n m : Nat} -> Nat.le n (succ m) -> Nat.le (pred n) m
  | zero, zero, _ => Nat.le.refl
  | _, _, Nat.le.refl => Nat.le.refl
  | zero, succ _, Nat.le.step h => h
  | succ _, succ _, Nat.le.step h => Nat.le_trans (le_succ _) h

theorem nat_pred_le_succ' : {n m : Nat} -> Nat.le n (succ m) -> Nat.le (pred n) m := by
  intro n m h
  cases h with
  | refl =>
    constructor
  | step h =>
    cases n with
    | zero =>
      dsimp only [zero_eq, Nat.pred_zero, le_eq]
      exact h
    | succ n =>
      dsimp only [Nat.pred_succ, le_eq]
      have h_n_le_succ_n := Nat.le_succ n
      exact (Nat.le_trans h_n_le_succ_n h)

theorem nat_min_zero {n: Nat}: min 0 n = 0 :=
  Nat.min_eq_left (Nat.zero_le _)

theorem nat_zero_min {n: Nat}: min n 0 = 0 :=
  Nat.min_eq_right (Nat.zero_le _)

theorem nat_min_succ' {n: Nat}: min (n + 1) (m + 1) = (min n m) + 1 := by
  unfold min
  unfold instMin_mathlib
  unfold inferInstance
  unfold instMinNat
  unfold minOfLe
  simp only
  split
  next h =>
    rw [nat_succ_le_succ_iff] at h
    split_ifs
    omega
  next h =>
    rw [nat_succ_le_succ_iff] at h
    split_ifs
    omega

theorem nat_min_succ {n: Nat}: min (n + 1) (m + 1) = (min n m) + 1 := by
  omega

theorem nat_add_succ_is_succ_add (n m: Nat): succ n + m = succ (n + m) := by
  cases n with
  | zero =>
    rewrite [Nat.add_comm]
    simp only [zero_eq, zero_add]
  | succ n =>
    rewrite [Nat.add_comm]
    rewrite [Nat.add_comm (succ n)]
    repeat rewrite [Nat.add_succ]
    rfl

theorem nat_pred_le_pred : {n m : Nat} → LE.le n m → LE.le (pred n) (pred m) := by
  intro n m h
  cases h with
  | refl => constructor
  | step h =>
    rename_i m
    cases n with
    | zero =>
      dsimp
      exact h
    | succ n =>
      dsimp
      have h_n_le_succ_n := Nat.le_succ n
      exact (Nat.le_trans h_n_le_succ_n h)

theorem nat_succ_gt_succ {n m: Nat}:
  succ n > succ m -> n > m := by
  intro h
  cases h with
  | refl =>
    constructor
  | step s =>
    apply Nat.le_of_succ_le_succ
    exact (Nat.le_succ_of_le s)

theorem nat_succ_gt_succ' {n m: Nat}:
  succ n > succ m -> n > m := by
  apply Nat.le_of_succ_le_succ

theorem nat_sub_zero {n: Nat}:
  n - 0 = n := by
  rfl

theorem nat_zero_sub {n: Nat}:
  (0 - n) = 0 := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp only [Nat.reduceSubDiff]
    rw [ih]

theorem nat_x_add_1_sub_y_add_1 {x y: Nat}:
  x + 1 - (y + 1) = x - y := by
  omega
