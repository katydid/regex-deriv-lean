# aesop

aesop is a very powerful tactic.

Given the following proof:

```lean
theorem simp_or_and_right_distrib (a b c : Lang α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro Hab Hc =>
    cases Hab with
    | inl Ha =>
      apply Or.inl
      apply And.intro Ha Hc
    | inr Hb =>
      apply Or.inr
      apply And.intro Hb Hc
  · case mpr =>
    intro H
    cases H with
    | inl Hac =>
      cases Hac with
      | intro Ha Hc =>
        apply And.intro
        apply Or.inl
        exact Ha
        exact Hc
    | inr Hbc =>
      cases Hbc with
      | intro Hb Hc =>
        apply And.intro
        apply Or.inr
        exact Hb
        exact Hc
```

We can rewrite it with aesop as:

```lean
theorem simp_or_and_right_distrib (a b c : Lang α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  aesop
```

## aesop?

aesop can become expensive to run every time, so we use `aesop?` to extract the proof that was created as is reproducible:

```lean
theorem simp_or_and_right_distrib (a b c : Lang α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  aesop?
```

We can now replace `aesop?` with the proof it found:


```lean
theorem simp_or_and_right_distrib (a b c : Lang α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a_1
    simp_all only [and_true]
  · intro a_1
    cases a_1 with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]
```

## References

* [aesop readme](https://github.com/leanprover-community/aesop#readme)
* [aesop tactic](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md#aesop)