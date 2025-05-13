# remember

In Coq we first used the `remember` tactic to first create an hyptohesis for the comparison and then did case analysis on the comparison. Lean has a shorthand for this as part of the cases tatic.

There might be other alternative options, but if we think specifically the use case of breaking up a hypothesis on `compare` with `cases` there is shorthand that is very helpful.

> cases h : e, where e is a variable or an expression, performs cases on e as above, but also adds a hypothesis h : e = ... to each hypothesis, where ... is the constructor instance for that particular case.

```lean
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
```

## References

* [cases tactic](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md#cases)