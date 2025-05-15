import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex

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

theorem mergeOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (mergeOr x y) := by
  sorry

theorem smartOr_is_correct_sorted_no_dup
  {α: Type} [Ord α] [DecidableEq α] (x y: Regex α) (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (smartOr x y) := by
  sorry
