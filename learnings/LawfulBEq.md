# LawfulBEq

`LawfulBEq` says that we can rewrite `a == b` as if it was a proper equality `a = b`:

```lean
class LawfulBEq (α : Type u) [BEq α] : Prop where
  /-- If `a == b` evaluates to `true`, then `a` and `b` are equal in the logic. -/
  eq_of_beq : {a b : α} → a == b → a = b
  /-- `==` is reflexive, that is, `(a == a) = true`. -/
  protected rfl : {a : α} → a == a
```

## deriving

LawfulBEq cannot be derived for our inductive types:

```lean
-- inductive Pred (α: Type u): Type (u + 1) where
--   | eq (x: α): Pred α
--   | and (p1 p2: Pred α): Pred α
--   deriving LawfulBEq, Repr
```

If we try it, we get following error:

```
default handlers have not been implemented yet, class: 'LawfulBEq' types: [Pred]
```

However we can derive `DecidableEq`:

```lean
inductive Pred (α: Type u): Type (u + 1) where
  | eq (x: α): Pred α
  | and (p1 p2: Pred α): Pred α
  deriving DecidableEq, Repr
```

All instances of `DecidableEq` gets an instance of `BEq` and `LawfulBEq` for free:

```lean
instance [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)

instance [DecidableEq α] : LawfulBEq α where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _
```

We can test that it works for our inductive type:

```lean
instance inst_pred_lbeq {α: Type u} [DecidableEq (Pred α)]: LawfulBEq (Pred α) := inferInstance
```

## inheritance

Unlike `DecidableEq`, we can use LawfulBEq to extend our classes

```lean
class Predicate (α: Type u) (φ: Type v) extends Ord φ, BEq φ, LawfulBEq φ where
  eval : φ -> α -> Prop
```

