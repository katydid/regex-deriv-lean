instance : Repr Ordering where
  reprPrec
    | Ordering.lt, _ => "<"
    | Ordering.gt, _ => ">"
    | Ordering.eq, _ => "="

namespace Ordering

-- lexicographical ordering
def lex (x: Ordering) (y: Ordering): Ordering :=
  match x with
  | Ordering.eq => y
  | _ => x

theorem lex_assoc:
  ∀ a b c, lex (lex a b) c = lex a (lex b c) := by
  intros a b c
  cases a <;> simp [lex]

instance IsAssociative_Ordering: Std.Associative lex :=
  { assoc := lex_assoc }

theorem lex_assoc' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) := by
  cases a
  {
    case lt => rfl
  }
  case eq => rfl
  case gt => rfl

theorem lex_assoc'' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) :=
  by cases a with
  | eq => rfl
  | lt => rfl
  | gt => rfl

theorem lex_assoc''' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) :=
  match a with
  | Ordering.eq => rfl
  | Ordering.lt => by rfl
  | Ordering.gt => by rfl

theorem lex_left_identity (a: Ordering):
  lex Ordering.eq a = a := by
  cases a <;> rfl

theorem lex_right_identity (a: Ordering):
  lex a Ordering.eq = a := by
  cases a <;> rfl

theorem lex_right_identity':
  ∀ x, lex x Ordering.eq = x := by
  intro x
  cases x
  · rfl
  · rfl
  · rfl

theorem lex_right_identity'':
  ∀ x, lex x Ordering.eq = x := by
  intro x
  cases x
  { rfl }
  { rfl }
  { rfl }

def compare_is_decidable_eq {α: Type u} (x y: α) (z: Ordering) [o: Ord α]: Decidable (Ord.compare x y = z) := by
  cases h: compare x y
  · case lt =>
    cases z <;> simp
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
  · case eq =>
    cases z <;> simp
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
  · case gt =>
    cases z <;> simp
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isTrue
      simp only

def compare_is_decidable_neq {α: Type u} (x y: α) (z: Ordering) [o: Ord α]: Decidable (Ord.compare x y ≠ z) := by
  cases h: compare x y
  · case lt =>
    cases z <;> simp
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isTrue
      simp only
  · case eq =>
    cases z <;> simp
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isFalse
      simp only [not_false_eq_true]
    · apply Decidable.isTrue
      simp only
  · case gt =>
    cases z <;> simp
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isTrue
      simp only
    · apply Decidable.isFalse
      simp only [not_false_eq_true]

def compare_isle_is_decidable {α: Type u} (x y: α) [o: Ord α]: Decidable (Ord.compare x y).isLE := by
  unfold isLE
  cases h: compare x y
  · case lt =>
    simp only
    apply Decidable.isTrue
    simp only
  · case eq =>
    simp only
    apply Decidable.isTrue
    simp only
  · case gt =>
    simp only
    apply Decidable.isFalse
    simp only [Bool.false_eq_true, not_false_eq_true]

def compare_isge_is_decidable {α: Type u} (x y: α) [o: Ord α]: Decidable (Ord.compare x y).isGE := by
  unfold isGE
  cases h: compare x y
  · case lt =>
    simp only
    apply Decidable.isFalse
    simp only [Bool.false_eq_true, not_false_eq_true]
  · case eq =>
    simp only
    apply Decidable.isTrue
    simp only
  · case gt =>
    simp only
    apply Decidable.isTrue
    simp only

instance {α: Type u} [Ord α] : DecidableRel (@LT.lt α ltOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => compare a b = Ordering.lt))

instance {α: Type u} [Ord α] : DecidableRel (@LE.le α leOfOrd) :=
  inferInstanceAs (DecidableRel (fun a b => (compare a b).isLE))

instance {α: Type u} [Ord α]: LT α where
  lt : α → α → Prop := fun x y => Ord.compare x y = Ordering.lt

instance {α: Type u} [Ord α]: LE α where
  le : α → α → Prop := fun x y => (Ord.compare x y).isLE

instance {α: Type u} [Ord α] (x y: α): Decidable (x < y) := inferInstance

instance {α: Type u} [Ord α] (x y: α): Decidable (x ≤ y) := inferInstance
