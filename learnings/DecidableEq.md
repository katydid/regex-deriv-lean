# DecidableEq

`DecidableEq` is a property that says that an equality is decidable.

```lean
abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (Eq a b)
```

## deriving

`DecidableEq` can be derived for our inductive types:

```lean
inductive Pred (α: Type u): Type (u + 1) where
  | eq (x: α): Pred α
  | and (p1 p2: Pred α): Pred α
  deriving DecidableEq, Repr
```

## BEq

If we derive `DecidableEq` for our inductive type we get an instance of BEq for free:

```lean
instance [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)
```

We can test whether the instance inferance works for `BEq` via `DecidableEq`:

```lean
instance inst_pred_beq {α: Type u} [DecidableEq (Pred α)]: BEq (Pred α) := inferInstance
```

Warning: Do not derive both `BEq` and `DecidableEq` for your inductive type:

```lean
-- inductive Pred (α: Type u): Type (u + 1) where
--   | eq (x: α): Pred α
--   | and (p1 p2: Pred α): Pred α
--   deriving BEq, DecidableEq, Repr
```

This can work, but can also result in confusing the compiler, when trying to find which instance of `BEq` it should use.

## inheritance

We cannot extend our classes with `DecidableEq`.
For example, given the following:

```lean
class Predicate (α: Type u) (φ: Type v) extends Ord φ, BEq φ, DecidableEq φ where
  eval : φ -> α -> Prop
```

We will get an red squiggle error at `DecidableEq φ`, which says: `expected structure`.

Unlike `DecidableEq`, we can extend our class with `LawfulBEq`, which might be what you looking for.
