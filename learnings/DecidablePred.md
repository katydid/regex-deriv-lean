# How to Prove Decidability of a Predicate

## Step 1: Define your Predicate

A predicate is a function that takes a parameter are returns a Prop.
In this case our predicate will be a language that accepts strings, like a regular expression.

```lean
def Lang: Type := String -> Prop
```

We define a data type representing all the expressions that can be used to build the predicate.
In this case we build a regular expression type, called Regex:

```lean
inductive Regex: Type where ...
```

Finally we create a denotation function, which defines how the Regex type translates into a predicate:

```lean
def denote (r: Regex): Lang := ...
```

Now we have defined our predicate type and a way to create predicates of that type.

## Step 2: Define an Execute function

Next we need to define a way of executing our predicate, a way to check if the a string matches a regular expression:

```lean
def execute (r: Regex) (s: String): bool := ...
```

Note that the execute function is already decidable, since it returns a bool and is computable, since it does not have noncomputable tag.
What we need to prove now is the correctness of the execute function.

## Step 3: Prove Correctness

Decidability of r is proven via the execute function, but we need to prove the correctness.
Proving the correctness of the execute function, requires a commutes theorem:

```lean
theorem commutes (r: Regex) (s: String): (execute r s = true) = (denote r s) := by
```

This is a theorem, so feel free to use tactics and even the Law of Exclusive Middle (Classical.Choice).
Using the Law of Exclusive Middle just means the proof is not constructive, but it doesn't affect decidability.
Note if you want to be very strict and only use constructive proofs, you can [detect the axioms used by each theorem](./DetectingClassical.md).

## Step 4: Prove Decidability

The final step is really just a formality and not necessarily required.

```lean
def decidable (r: Regex α): DecidablePred (denote r) :=
   fun xs => decidable_of_decidable_of_eq (commutes r xs)  
```

Decidability of the Regex is now proven.
If you used the Law of Exclusive Middle, then the proof is not constructive, but that is fine apparently.

## Doubt the use of Law of Exclusive Middle

We doubt that it is really fine to use the Law of Exclusive Middle (Classical.choice) to prove decidability,
since the use Classical.choice implies that Props are decidable.

For example, if we use the the simplification rule that `(not (not r)) = r` (which requires Classical.choice)
in our proof of decidability, then would our proof really be correct?

For this reason we error on the side of caution and [detect the use of Classical.choice](./DetectingClassical.md) and make sure to avoid it.
This is why we prefer our proof of decidability to be constructive. 

## References

* [Zulip Chat on restricting axioms](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms)
