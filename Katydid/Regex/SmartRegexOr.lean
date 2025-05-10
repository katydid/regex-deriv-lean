import Katydid.Std.Linter.DetectClassical

import Katydid.Regex.SmartRegex

open SmartRegex

def OrIsSortedNoDup (x: Regex α) : Prop :=
  match x with
  | Regex.or x1 (Regex.or x21 x22) =>
    Regex.compare x1 x21 = Ordering.lt /\ OrIsSortedNoDup (Regex.or x21 x22)
  | Regex.or x1 x2 =>
    Regex.compare x1 x2 = Ordering.lt
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

def OrIsSmart (x: Regex α) : Prop :=
  (OrIsSortedNoDup x) /\
  (Not (OrContainsStarAny x)) /\
  (Not (OrContainsEmptyset x))

def mkOr (x y: Regex α): Regex α :=
  match Ord.compare x y with
  | Ordering.lt =>
    Regex.or x y
  | Ordering.eq =>
    x
  | Ordering.gt =>
    Regex.or y x

theorem mkOr_is_correct_denote:
  denote (Regex.or x y) = denote (mkOr x y) := by
  unfold mkOr
  cases compare x y with
  | lt =>
    sorry
  | eq =>
    sorry
  | gt =>
    sorry

-- insertOr inserts y into x, where x might be or expression and y is not.
-- It inserts y into x if y is not a duplicate found in the or expression of x.
-- It inserts y into x into a sorted position in the or expression of x.
-- example:
--   insertOr (Regex.or a c) b = Regex.or a (Regex.or b c)
--   insertOr (Regex.or a c) a = Regex.or a c
--   insertOr a b = Regex.or a b
--   insertOr a a = a
def insertOr (x y: Regex α): Regex α :=
  match x with
  | Regex.or x1 x2 =>
    match Ord.compare x1 y with
    | Ordering.lt =>
      Regex.or x (insertOr x2 y)
    | Ordering.eq =>
      x
    | Ordering.gt =>
      Regex.or x1 (Regex.or y x2)
  | _ =>
    mkOr x y

theorem insertOr_is_correct_denote:
  denote (Regex.or x y) = denote (insertOr x y) := by
  induction x with
  | or x1 x2 ih1 ih2 =>
    sorry
  | _ =>
    sorry

def mergeOr (x y: Regex α): Regex α :=
  match x with
  | Regex.or x1 x2 =>
    match y with
    | Regex.or y1 y2 =>
      match Ord.compare x1 y1 with
      | Ordering.lt => Regex.or x1 (insertOr y1 (mergeOr x2 y2))
      | Ordering.eq => mergeOr x2 y
      | Ordering.gt => Regex.or y1 (insertOr x1 (mergeOr x2 y2))
    | _ => insertOr x y
  | _ => insertOr y x

theorem mergeOr_is_correct_denote:
  denote (Regex.or x y) = denote (mergeOr x y) := by
  sorry

theorem mergeOr_is_correct_sorted_no_dup
  {x y: Regex α} (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (mergeOr x y) := by
  sorry

def smartOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | Regex.star Regex.any => x
  | Regex.or _ _ =>
    match y with
    | Regex.emptyset => x
    | Regex.star Regex.any => y
    | Regex.or _ _ =>
      mergeOr x y
    | _ =>
      insertOr x y
  | _ =>
    match y with
    | Regex.emptyset => x
    | Regex.star Regex.any => y
    | Regex.or _ _ =>
      insertOr y x
    | _ =>
      Regex.or x y

theorem smartOr_is_correct_denote:
  denote (Regex.or x y) = denote (smartOr x y) := by
  sorry

theorem smartOr_is_correct_sorted_no_dup
  {x y: Regex α} (hx: OrIsSortedNoDup x) (hy: OrIsSortedNoDup y):
  OrIsSortedNoDup (smartOr x y) := by
  sorry
