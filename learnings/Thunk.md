# Thunk

A Thunk is function that takes no parameters and returns a value.
It is a way to enforce lazy evaluation.
The `get` method is use to force the evaluation and return the argument.

Here is an example of creating a Thunk that returns an Ordering type and some proofs about it:

```lean
instance : Repr (Thunk Ordering) where
  reprPrec thunk _ :=
    match thunk.get with
    | Ordering.lt => "<"
    | Ordering.gt => ">"
    | Ordering.eq => "="

namespace OrderingThunk

-- lexicographical ordering
def lex (x: Thunk Ordering) (y: Thunk Ordering): Thunk Ordering :=
  match x.get with
  | Ordering.eq => y
  | _ => x.get

theorem lex_assoc:
  ∀ a b c, lex (lex a b) c = lex a (lex b c) := by
  intros a b c
  unfold lex
  cases a.get with
  | lt => simp only
          simp [Thunk.get]
  | gt => dsimp
          rfl
  | eq => dsimp only

theorem lex_left_identity (a: Thunk Ordering):
  lex Ordering.eq a = a := by
  cases a <;> rfl

theorem lex_right_identity (a: Thunk Ordering):
  lex a Ordering.eq = a := by
  unfold lex
  cases h: a.get <;>
    simp only <;>
    rw [<-h] <;>
    rfl

end OrderingThunk
```