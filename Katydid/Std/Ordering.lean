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

end Ordering
