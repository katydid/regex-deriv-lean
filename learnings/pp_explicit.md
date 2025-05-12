## pp_explicit

Sometimes it is helpful to see which implicit parameters was passed to a theorem or definition.

When we print a theorem, we do not always see these, for example when printing `of_decide_eq_true`:

```lean
#print of_decide_eq_true
```

We do not see which implicit parameters were passed to absurd, decide, etc:

```lean
theorem of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p :=
fun {p} [inst : Decidable p] h =>
  match inst with
  | isTrue h₁ => h₁
  | isFalse h₁ => absurd h (ne_true_of_eq_false (decide_eq_false h₁))
```

We can change the behaviour of print to also print the by setting it to print parameter as if they are all explicit:

```lean
set_option pp.explicit true
```

Now when we print again:

```lean
#print of_decide_eq_true
```

it prints out all the implicit parameters:

```lean
theorem of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], @Eq Bool (@decide p inst) true → p :=
fun {p} [inst : Decidable p] h =>
  @of_decide_eq_true.match_1 p (fun inst => p) inst (fun h₁ => h₁) fun h₁ =>
    @absurd (@Eq Bool (@decide p inst) true) p h (@ne_true_of_eq_false (@decide p inst) (@decide_eq_false p inst h₁))
```

## References

* [pp.explicit used in docs](https://lean-lang.org/theorem_proving_in_lean4/type_classes.html)