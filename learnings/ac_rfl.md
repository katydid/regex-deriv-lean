# ac_rfl

`ac_rfl` is a tactic used to finish proof where two sides of an equality are the same, except that some associative or commutative operation is required:

For example given we want to prove that appending lists are associative we can use ac_rfl:

```lean
theorem list_app_assoc (xs ys zs: List α):
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  ac_rfl
```

We can do this since appending lists have already been proven to be associative.

## Using ac_rfl for our own types:

Appending lists have already been proven to be associative, but we can also do this for our own type.

### Associative

We know that the `concat` operator in a regular expression is associative.

```lean
def concat {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (xs : List α) =>
    ∃ (xs1 : List α) (xs2 : List α), P xs1 /\ Q xs2 /\ xs = (xs1 ++ xs2)

theorem simp_concat_assoc (r s t: Lang α):
  concat (concat r s) t = concat r (concat s t) := by
  ...
```

If we show that it is an instance of `Associative`, then `ac_rfl` will use that fact.
`Associative` is a class found in Init/Core.lean in the `Std` namespace:

```lean
class Associative (op : α → α → α) : Prop where
  /-- An associative operation satisfies `(a ∘ b) ∘ c = a ∘ (b ∘ c)`. -/
  assoc : (a b c : α) → op (op a b) c = op a (op b c)
```

Now we can create an instance of `Associative` for `concat`:

```lean
instance IsAssociative_concat {α: Type}: Std.Associative (@concat α) :=
  { assoc := @simp_concat_assoc α }

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Lang α):
  concat (concat r s) t = concat r (concat s t) := by
  ac_rfl
```

`concat` is associative, but it is not commutative.
Even so `ac_rfl` can be used with operators that are only associative.

In our experiments, we have found that the opposite is not possible
The `ac_rfl` tactic works without commutativity, but not without assosiativity.

## Commutative

The `or` operator of a regular expression is associative and commutative, so we can use all the power of the `ac_rfl` tactic.
We just need to create instances of both `Associative` and `Commutative`.

`Commutative` is a class found in Init/Core.lean in the `Std` namespace:

```lean
class Commutative (op : α → α → α) : Prop where
  /-- A commutative operation satisfies `a ∘ b = b ∘ a`. -/
  comm : (a b : α) → op a b = op b a
```

We can create both instances for the `or` operator:

```lean
-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_or {α: Type}: Std.Associative (@or α) :=
  { assoc := @simp_or_assoc α }

-- class Commutative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsCommutative_or {α: Type}: Std.Commutative (@or α) :=
  { comm := @simp_or_comm α }
```

And then we can use `ac_rfl` to prove the following theorems:

```lean
-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Lang α):
  or r s = or s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Lang α):
  or (or r s) t = or r (or s t) := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Lang α):
  (or a (or b (or c d))) = (or d (or (or b c) a)) := by ac_rfl
```

## References

* [ac_rfl in Hitchhikers Guide to Lean](https://github.com/lean-forward/logical_verification_2024/blob/4e5e78a040dd34c98339f13db2b5357918dda32a/lean/LoVe/LoVe03_BackwardProofs_Demo.lean#L284C1-L289C12)