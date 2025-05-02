# simp

The `simp` tactic is a very popular tactic.

## How to include your theorems in simp

Here is an example of how to use `@[simp]` to include theorems in simp:

```lean
@[simp]
theorem simp_and_emptyset_l_is_emptyset (r: Lang α):
  and emptyset r = emptyset := by
  unfold and
  simp only [emptyset, false_and]
  rfl
```

Adding the `@[simp]` annotation before a theorem adds it to the `simp` library.
We can now use it to reprove the same theorem, by simply calling simp:

```lean
theorem simp_and_emptyset_l_is_emptyset' (r: Lang α):
  and emptyset r = emptyset := by
  simp
```

## How to see what simp did

If you used the `simp` tactic you might be wondering what did the simp tactic do.
You can find this out by replacing it with `simp?`

```lean
theorem simp_and_emptyset_l_is_emptyset' (r: Lang α):
  and emptyset r = emptyset := by
  simp?
```

You will then find in the Lean InfoView in VSCode:

```lean
simp only [simp_and_emptyset_l_is_emptyset]
```

You can now copy this to replace `simp` and to have a more maintainable theorem:

```lean
theorem simp_and_emptyset_l_is_emptyset' (r: Lang α):
  and emptyset r = emptyset := by
  simp only [simp_and_emptyset_l_is_emptyset]
```

## References

* [Example of how to extend simp in mathlib](https://github.com/leanprover-community/mathlib4/blob/56c1ca9832bdd85620d6b0bbd37ef56818e6b667/Mathlib/Data/Matrix/Basis.lean)