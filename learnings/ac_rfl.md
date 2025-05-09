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

The `ac_rfl` tactic uses instances of the following classes to complete the proof:

* Associative
* Commutative
* IdempotentOp
* LawfulIdentity

Given these instances, we can also use the tactic `ac_nf`.

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

## IdempotentOp

`ac_rfl` also uses another class for idempotent operators, like `or`:
`IdempotentOp` is a class found in Init/Core.lean in the `Std` namespace:

```lean
class IdempotentOp (op : α → α → α) : Prop where
  /-- An idempotent operation satisfies `a ∘ a = a`. -/
  idempotent : (x : α) → op x x = x
```

We can instantiate this class for `or` too:

```lean
instance IsIdempotentOp_or {α: Type}: Std.IdempotentOp (@or α) :=
  { idempotent := simp_or_idemp }
```

And then use it to prove the following theorems:

```lean
-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Lang α):
  or (or r r) r = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Lang α):
  (or a (or b (or c d))) = (or a (or d (or (or b c) a))) := by ac_rfl
```

## LawfulIdentity

Creating an instance of `LawfulIdentity` can be done in two ways:

1. Creating an instance of `LawfulIdentity` or
2. Creating an instance of `LawfulCommIdentity`, if the operator is an instance of `Commutative`.

The `concat` operator is not commutative, so we have to create an instance of `LawfulIdentity`:

```lean
instance IsLawfulIdentity_concat {α: Type} : Std.LawfulIdentity (@concat α) (@emptystr α) where
  left_id := simp_concat_emptystr_l_is_r
  right_id := simp_concat_emptystr_r_is_l

-- Test ac_rfl uses the instance of LawfulIdentity
example (r: Lang α):
  concat emptystr r = r := by
  ac_rfl
```

The `or` operator is commutative, so we can create an instance of `LawfulCommIdentity`, which only requires one of `left_id` or `right_id`:

```lean
instance IsLawfulCommIdentity_or {α: Type} : Std.LawfulCommIdentity (@or α) (@emptyset α) where
  right_id r := simp_or_emptyset_r_is_l r

-- Test that ac_rfl uses the instance of Std.LawfulCommIdentity
example (r: Lang α):
  or r emptyset = r := by
  ac_rfl
```

## ac_nf

The ac_nf tactic rewrites using associativity, commutativity, idempotency and identity to a normal form.

```lean
example (r s: Lang α) (H: s = r):
  or emptyset (or r s) = (or r r) := by
  ac_nf
  -- or r s = r
  rw [H]
  -- or r r = r
  ac_rfl
```

This means it is useful not only for the final step, but also to make progress in a proof.

## References

* [ac_rfl in Hitchhikers Guide to Lean](https://github.com/lean-forward/logical_verification_2024/blob/4e5e78a040dd34c98339f13db2b5357918dda32a/lean/LoVe/LoVe03_BackwardProofs_Demo.lean#L284C1-L289C12)