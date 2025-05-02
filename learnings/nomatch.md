# nomatch

In cases where we know that one of our hypotheses have no inhabitants (are equivalent to False) we know that the prove is done once we destruct this hypothesis.

One way to do this is using the cases tactic:

```lean
theorem emptystr_is_false_for_non_empty_string {α: Type} (x: α) (xs: List α):
  emptystr (x :: xs) -> False := by
  intro H
  cases H
```

This looks weird, since after cases, we expect to evaluate the cases of H, but there are none.
A more explicit way to do this is using `nomatch`:

```lean
theorem emptystr_is_false_for_non_empty_string {α: Type} (x: α) (xs: List α):
  emptystr (x :: xs) -> False := by
  intro H
  nomatch H
```
