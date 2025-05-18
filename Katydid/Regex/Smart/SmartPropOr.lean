import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

import Katydid.Regex.Smart.SmartRegex

open SmartRegex

def Regex.isOr (x: Regex α) : Prop :=
  ∃ x1 x2, x = Regex.or x1 x2

def Regex.notOr (x: Regex α) : Prop :=
  (x = Regex.emptyset)
  \/ (x = Regex.emptystr)
  \/ (x = Regex.any)
  \/ (∃ p: Predicate.Pred α, x = Regex.pred p)
  \/ (∃ x1 x2, x = Regex.concat x1 x2)
  \/ (∃ x1, x = Regex.star x1)

theorem Regex.notOr_or {α: Type u} {x y: Regex α}:
  Regex.notOr (Regex.or x y) -> False := by
  intro h
  unfold notOr at h
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    cases h
    contradiction
  | inr h =>
  cases h with
  | inl h =>
    cases h
    next h =>
    cases h
    contradiction
  | inr h =>
  cases h
  contradiction

theorem Regex.notOr_emptyset {α: Type u}:
  Regex.notOr (@Regex.emptyset α) := by
  unfold notOr
  simp

theorem Regex.notOr_emptystr {α: Type u}:
  Regex.notOr (@Regex.emptystr α) := by
  unfold notOr
  simp

theorem Regex.notOr_any {α: Type u}:
  Regex.notOr (@Regex.any α) := by
  unfold notOr
  simp

theorem Regex.notOr_pred {α: Type u} {p: Predicate.Pred α}:
  Regex.notOr (@Regex.pred α p) := by
  unfold notOr
  simp

theorem Regex.notOr_concat {α: Type u} {x y: Regex α}:
  Regex.notOr (Regex.concat x y) := by
  unfold notOr
  simp

theorem Regex.notOr_star {α: Type u} {x: Regex α}:
  Regex.notOr (Regex.star x) := by
  unfold notOr
  simp

-- check that Regex.notOr does an exhaustive match of all possible patterns, except for Regex.or.
theorem Regex.notOr_is_exhaustive (x: Regex α):
  Regex.notOr x = Not (Regex.isOr x) := by
  unfold notOr
  unfold isOr
  cases x <;> simp

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
inductive OrList: Regex α -> Prop where
  | base (x: Regex α):
    Regex.notOr x
    -> OrList x
  | bin (xy x y: Regex α):
    xy = Regex.or x y
    -> Regex.notOr x
    -> OrList y
    -> OrList xy

-- The or is balanced to the right as a list
-- (or a (or b (or c d)))
inductive OrList3: Regex α -> Prop where
  | singleton (x: Regex α):
    Regex.notOr x
    -> OrList3 x
  | lastcons (xy x y: Regex α):
    xy = Regex.or x y
    -> Regex.notOr x
    -> Regex.notOr y
    -> OrList3 xy
  | cons (x y y1 y2: Regex α):
    xy = Regex.or x y
    -> y = Regex.or y1 y2
    -> Regex.notOr x
    -> OrList3 y
    -> OrList3 xy

theorem orlist_is_OrList3 (xy: Regex α):
  OrList xy <-> OrList3 xy := by
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | base _ notx =>
      apply OrList3.singleton
      exact notx
    | bin xy x y hxy hx hy ih =>
      revert hy hxy
      cases y with
      | emptyset =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_emptyset
      | emptystr =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_emptystr
      | any =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_any
      | pred p =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_pred
      | concat x21 x22 =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_concat
      | star x21 =>
        intro hx2 hxy
        apply OrList3.lastcons xy x <;> try assumption
        apply Regex.notOr_star
      | or y1 y2 =>
        intro hxy
        intro hy
        rw [hxy]
        apply OrList3.cons x (Regex.or y1 y2) y1 y2 rfl rfl hx
        exact ih
  case mpr =>
    intro h
    induction h with
    | singleton x h =>
      apply OrList.base
      exact h
    | lastcons xy x y hxy hx hy =>
      apply OrList.bin xy x y hxy hx
      apply OrList.base y hy
    | cons x y y1 y2 hxy hy1y2 hx hy ihy =>
      rename_i xy'
      apply OrList.bin xy' x y hxy hx ihy

inductive SimpOrStarAny: Regex α -> Prop where
  | base (x: Regex α):
    Regex.notOr x
    -> SimpOrStarAny x
  | base_or (x y: Regex α):
    xy = Regex.or x y
    /\ Regex.notOr y
    /\ x ≠ (Regex.star Regex.any)
    /\ y ≠ (Regex.star Regex.any)
    -> SimpOrStarAny xy
  | nested (x y1 y2: Regex α):
    y = Regex.or y1 y2
    /\ xy = Regex.or x y
    /\ x ≠ (Regex.star Regex.any)
    -> SimpOrStarAny y
    -> SimpOrStarAny xy

theorem mkOr_preserves_no_star_any {α: Type} [Ord α] [DecidableEq α] (x y: Regex α)
  (smartx: SimpOrStarAny x) (smarty: SimpOrStarAny y):
  SimpOrStarAny (mkOr x y) := by
  unfold mkOr
  split_ifs
  case pos h =>
    exact smartx
  case pos h =>
    sorry
  case neg h =>
    sorry


theorem smartOr_removes_star_any {α: Type} [Ord α] [DecidableEq α] (x y: Regex α)
  (smartx: SimpOrStarAny x) (smarty: SimpOrStarAny y):
  SimpOrStarAny (smartOr x y) := by
  induction x with
  | emptyset =>
    rw [smartOr]
    exact smarty
  | emptystr =>
    cases y with
    | emptyset =>
      simp only [smartOr]
      exact smartx
    | emptystr =>
      simp only [smartOr]
      unfold mkOr
      simp only [↓reduceIte]
      exact smartx
    | any =>
      simp only [smartOr]
      unfold mkOr
      simp
      sorry
    | _ =>
      sorry
  | _ =>
    sorry

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

inductive OrContainsStarAny': Regex α -> Prop where
  | orLeft (x: Regex α): OrContainsStarAny' (Regex.or (Regex.star Regex.any) x)
  | orRight (x: Regex α): OrContainsStarAny' (Regex.or x (Regex.star Regex.any))
  | orNested (x y: Regex α): OrContainsStarAny' y -> OrContainsStarAny' (Regex.or x y)

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
