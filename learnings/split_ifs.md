# split_ifs

The `split_ifs` tactic is useful for considering both cases of an if statement.
Given you are in the following proof state:

```lean
m n : ℕ
h : n ≤ m
⊢ n + 1 = (if n ≤ m then n else m) + 1
```

You can use the `split_ifs` tactic to get to:

```lean
m n : ℕ
h : n ≤ m
⊢ n + 1 = n + 1
```

It eliminated the case where n ≤ m is false, since this caused a contradiction with `h`.

In cases where this is not eliminated when case using `split_ifs` in the following way:

```lean
split_ifs
case pos hc =>
  sorry
case neg hc =>
  sorry
```
