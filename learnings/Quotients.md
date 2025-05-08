# Quotients

> Set-theoretically, Quotient `s` can seen as the set of equivalence classes of `α` modulo the Setoid instance's relation `s`.

We will explain Quotients with the example of regular expressions.

## Equivalence Class

An equivalence class is a set of items that are equivalent.

> Let α be any type, and let r be an equivalence relation on α. It is mathematically common to form the "quotient" α / r, that is, the type of elements of α "modulo" r. Set theoretically, one can view α / r as the set of equivalence classes of α modulo r. 

In our example α is (x: Regex α) and r is:

```lean
abbrev eqv (r1 r2 : Regex α) : Prop :=
  denote r1 = denote r2

infix:50 " ~ " => eqv
```

, which means that α / r is `denote x`, which is also expressed as ⟦x⟧ when we implement the Quotient type later.

Regular expressions are idempotent and commutative on the `Regex.or` operator.

This means that:
* `denote (Regex.or r r)` is in the same equivalence class as `denote r`, since they are equivalent, via idempotency.
* `denote (Regex.or r s)` is in the same equivalence class as `denote (Regex.or s r)`, since they are equivalent via commutativity of or: `Language.or (denote r) (denote s) = Language.or (denote r) (denote s)`

We can implement Equivalence for our relation:

```lean
private lemma eqv.refl {α} (r : Regex α) : r ~ r := rfl

private lemma eqv.symm  {α} : ∀ {r1 r2 : Regex α}, r1 ~ r2 → r2 ~ r1 := by
  intro r1 r2 h
  unfold eqv at *
  rw [h]

private lemma eqv.trans {α} : ∀ {r1 r2 r3 : Regex α}, r1 ~ r2 → r2 ~ r3 → r1 ~ r3 := by
  unfold eqv
  intro r1 r2 r3 r1r2 r2r3
  rw [r1r2, r2r3]

instance IsEquivalence_Regex : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

## Setoid

> Quotient types are built on setoids. A setoid is a type paired with a distinguished equivalence relation. Unlike a quotient type, the abstraction barrier is not enforced, and proof automation designed around equality cannot be used with the setoid's equivalence relation. Setoids are useful on their own, in addition to being a building block for quotient types.

We can implement a Setoid for our relation:

```lean
instance IsSetoid_Regex (α : Type) : Setoid (Regex α) where
   r     := eqv
   iseqv := IsEquivalence_Regex
```

HasEquiv is the typeclass which supports the notation `x ≈ y`.
All Setoids are automatically also instances of HasEquiv:

```lean
instance {α : Sort u} [Setoid α] : HasEquiv α :=
   ⟨Setoid.r⟩
```

This means we can use the syntax `x ≈ y` for our relation:

```lean
theorem Regex.refl (a : Regex α) : a ≈ a :=
  IsEquivalence_Regex.refl a

theorem Regex.symm {a b : Regex α} (hab : a ≈ b) : b ≈ a :=
  IsEquivalence_Regex.symm hab

theorem Regex.trans {a b c : Regex α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  IsEquivalence_Regex.trans hab hbc
```

## Quotient

We define a Quotient Type for our Regex:

```lean
def RegexQ (α : Type) : Type :=
  Quotient (IsSetoid_Regex α)
```

## Quotient.mk

We can now define our quotient constructor using our Setoid implementation:

```lean
def RegexQ.mk' {α : Type} (x: Regex α): RegexQ α :=
  Quot.mk Setoid.r x
```

We can also use the specialized version of `Quot`, called `Quotient` to do define the equivalent function:

```lean
def RegexQ.mk {α : Type} (x: Regex α): RegexQ α :=
  Quotient.mk' x
```

Here the specific Setoid is infered.

We can also use this to define constructors for each type of Regex, if we want:

```lean
def RegexQ.mkEmptyset {α: Type}: RegexQ α :=
  Quotient.mk' Regex.emptyset

def RegexQ.mkEmptystr {α: Type}: RegexQ α :=
  Quotient.mk' Regex.emptystr

def RegexQ.mkPred {α: Type} (p: α -> Prop) [DecidablePred p]: RegexQ α :=
  Quotient.mk' (Regex.pred p)

def RegexQ.mkOr {α: Type} (x y: Regex α): RegexQ α :=
  Quotient.mk' (Regex.or x y)

def RegexQ.mkConcat {α: Type} (x y: Regex α): RegexQ α :=
  Quotient.mk' (Regex.concat x y)

def RegexQ.mkStar {α: Type} (x: Regex α): RegexQ α :=
  Quotient.mk' (Regex.star x)
```

## Quotient.lift

> If f : α → β is any function that respects the equivalence relation in the sense that for every x y : α, r x y implies f x = f y, then f "lifts" to a function f' : α / r → β defined on each equivalence class ⟦x⟧ by f' ⟦x⟧ = f x. Lean's standard library extends the Calculus of Constructions with additional constants that perform exactly these constructions, and installs this last equation as a definitional reduction rule.

```lean
axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β

protected abbrev lift
    {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) :
    ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f
```

If we substitute our Regex we get:

```lean
axiom Quot.lift :
    {α : Type} → {eqv : Regex α → Regex α → Prop} → {β : Sort u} → (f : Regex α → β)
    → (∀ a b: Regex α, r a b → f a = f b) → RegexQ α → β
```

We have to decide what a useful β will be, but we can't move out of our equivalence relation, otherwise `(∀ a b: Regex α, r a b → f a = f b)` would not be True.
For example β cannot be Regex α, since then we lose denote and that would be outside of the equivalence relation.

We can however make β, Language.Lang α and lift star.
In this example `f = (fun x => denote (Regex.star x))`:

```lean
theorem star_respects_eqv:
  ∀ (x y: Regex α), x ~ y ->
    denote (Regex.star x) = denote (Regex.star y) := by
  intro x y
  intro H
  unfold denote
  simp only [H]

def liftStarQLang: (RegexQ α -> Language.Lang α) :=
  Quotient.lift (fun x => denote (Regex.star x)) star_respects_eqv
```

We can also choose β to be RegexQ α.
In this example `f = RegexQ.mkStar`:

```lean
theorem starq_respects_eqv:
  ∀ (x y: Regex α), x ~ y ->
    RegexQ.mkStar x = RegexQ.mkStar y := by
  intro x y
  intro H
  apply Quot.sound
  apply star_respects_eqv
  apply H

def RegexQ.star: (RegexQ α -> RegexQ α) :=
  Quotient.lift RegexQ.mkStar starq_respects_eqv
```

## Quotient.lift2

The `or` and `concat` operators are binary operators.
Quotient.lift` is useful for unary operators and Quotient.lift2 is used for binary operators:

```lean
theorem or_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): denote (Regex.or x1 y1) = denote (Regex.or x2 y2) := by
  unfold denote at *
  unfold eqv at *
  simp only [hx]
  simp only [hy]

def liftOrLang (x: Regex α) (y: Regex α): Language.Lang α :=
  Quotient.lift₂ (fun x' y' => denote (Regex.or x' y')) or_respects_eqv ⟦ x ⟧ ⟦ y ⟧

theorem orq_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2 := by
  apply Quot.sound
  apply or_respects_eqv
  · apply hx
  · apply hy

def RegexQ.or: (RegexQ α -> RegexQ α -> RegexQ α) :=
  Quotient.lift₂ RegexQ.mkOr orq_respects_eqv
```

## Quot.sound

In the previous proofs we used `Quot.sound`.

> What makes the Quot construction into a bona fide quotient is the following additional axiom:

```lean
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
```

> This is the axiom that asserts that any two elements of α that are related by r become identified in the quotient. If a theorem or definition makes use of Quot.sound, it will show up in the #print axioms command.

We used Quot.sound inr our proves to turn our equality between quotients, back into our relation.

In the theorem orq_respects_eqv:

```lean
theorem orq_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2 := by
  apply Quot.sound
```

when we apply Quot.sound we get the following goal:

```lean
(IsSetoid_Regex α) (x1.or y1) (x2.or y2) -> RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2
```

This somehow normalizes to:

```lean
Regex.or x1 y1 ~ Regex.or x2 y2 -> RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2
```

which normalises to:

```lean
denote (Regex.or x1 y1) = denote (Regex.or x2 y2) -> RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2
```

Which is our proof of `or_respects_eqv`.

## References

* [The Lean Language Reference - Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)
* [Theorem Proving in Lean4 - Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html)
* [Beginner problem: 'Lift' a proposition to a Quotient type](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.E2.9C.94.20Beginner.20problem.3A.20'Lift'.20a.20proposition.20to.20a.20Quotient.20type/near/516853703)
* [How to lift a binary function to a quotient?](https://proofassistants.stackexchange.com/questions/2663/how-to-lift-a-binary-function-to-a-quotient)