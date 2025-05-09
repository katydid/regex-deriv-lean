# ring

The ring tactic is a tactic for solving equations in commutative (semi)rings.

The ring tactic can be applied to instances of [CommSemiring](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#CommSemiring).

## CommSemiring

CommSemiring requires the implementation of the following:

```lean
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R : Type u
    add : R → R → R
    add_assoc (a b c : R) : a + b + c = a + (b + c)
    zero : R
    zero_add (a : R) : 0 + a = a
    add_zero (a : R) : a + 0 = a
    nsmul : ℕ → R → R
    nsmul_zero (x : R) : AddMonoid.nsmul 0 x = 0
    nsmul_succ (n : ℕ)  (x : R) : AddMonoid.nsmul (n + 1) x = AddMonoid.nsmul n x + x
    add_comm (a b : R) : a + b = b + a
    mul : R → R → R
    left_distrib (a b c : R) : a * (b + c) = a * b + a * c
    right_distrib (a b c : R) : (a + b) * c = a * c + b * c
    zero_mul (a : R) : 0 * a = 0
    mul_zero (a : R) : a * 0 = 0
    mul_assoc (a b c : R) : a * b * c = a * (b * c)
    one : R
    one_mul (a : R) : 1 * a = a
    mul_one (a : R) : a * 1 = a
    natCast : ℕ → R
    natCast_zero : ↑0 = 0
    natCast_succ (n : ℕ) : ↑(n + 1) = ↑n + 1
    npow : ℕ → R → R
    npow_zero (x : R) : Semiring.npow 0 x = 1
    npow_succ (n : ℕ)  (x : R) : Semiring.npow (n + 1) x = Semiring.npow n x * x
    mul_comm (a b : R) : a * b = b * a
```

Luckily we don't have to implement them all, since some are implemented via extensions CommSemiring inherits from.
This means we only have to implement:

```lean
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R : Type u
    add : R → R → R
    add_assoc (a b c : R) : a + b + c = a + (b + c)
    zero : R
    zero_add (a : R) : 0 + a = a
    add_zero (a : R) : a + 0 = a
    nsmul : ℕ → R → R
    add_comm (a b : R) : a + b = b + a
    mul : R → R → R
    left_distrib (a b c : R) : a * (b + c) = a * b + a * c
    right_distrib (a b c : R) : (a + b) * c = a * c + b * c
    zero_mul (a : R) : 0 * a = 0
    mul_zero (a : R) : a * 0 = 0
    mul_assoc (a b c : R) : a * b * c = a * (b * c)
    one : R
    one_mul (a : R) : 1 * a = a
    mul_one (a : R) : a * 1 = a
    mul_comm (a b : R) : a * b = b * a
```

### Monoid

The Monoid class is part of CommSemiring inheritance chain via:
CommSemiring -> CommMonoid -> Monoid

```lean
/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl
```

### AddMonoid

The AddMonoid class implements:
  * nsmul_zero
  * nsmul_succ

```lean
/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl
```

The AddMonoid class is part of CommSemiring inheritance chain via:
CommSemiring -> Semiring -> NonUnitalSemiring -> NonUnitalNonAssocSemiring -> AddCommMonoid -> AddCommSemigroup -> AddMonoid.

The Monoid class implements:
  * npow
  * npow_zero
  * npow_succ

###  AddCommMonoidWithOne

The AddMonoidWithOne class implements:
  * natCast
  * natCast_zero
  * natCast_succ

The AddMonoidWithOne class is part of CommSemiring inheritance chain via:
CommSemiring -> Semiring -> NonAssocSemiring -> AddCommMonoidWithOne -> AddMonoidWithOne

```lean
/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl
```

## Implementing CommSemiring for or, and

We can create a CommSemiring implementation if we choose:
* add := or
* mul := and

```lean
import Mathlib.Algebra.Ring.Defs

instance IsCommSemiring_or_and {α: Type}: CommSemiring (@Lang α) :=
  {
    add := or
    add_assoc := simp_or_assoc
    zero := emptyset
    zero_add := simp_or_emptyset_l_is_r
    add_zero := simp_or_emptyset_r_is_l
    add_comm := simp_or_comm
    nsmul := nsmul_or

    mul := and
    zero_mul := simp_and_emptyset_l_is_emptyset
    mul_zero := simp_and_emptyset_r_is_emptyset
    mul_assoc := simp_and_assoc

    one := universal
    one_mul := simp_and_universal_l_is_r
    mul_one := simp_and_universal_r_is_l

    left_distrib := simp_or_and_left_distrib
    right_distrib := simp_or_and_right_distrib
  }
```

These are all trivial, except for nsuml:

```lean
def nsmul_or (n: Nat) (r: Lang α): Lang α :=
  match n with
  | 0 => emptyset
  | Nat.succ n' => or (nsmul_or n' r) r
```

## ring tactic

We can now test the ring tactic:

```lean
import Mathlib.Tactic.Ring

example (a : Lang α) : 0 + a = a := by
  ring

example (a b c : Lang α) : (a + b) * c = (a * c) + (b * c) := by
  ring

example (a b c : Lang α) : (a + 0 + b) * c = (a * 1 * c) + (b * c) := by
  ring
```

The ring tactic works when we use the specific notation where:
* `0` = `emptyset`
* `1` = `universal`
* `+` = `or`
* `*` = `and`

## ring_nf tactic

The ring_nf tactic uses the ring tactic to normalize the equation:

```lean
example (a b: Lang α) (H: b = a * 3): a + a + a = b := by
  ring_nf
  rw [H]
```

## Implementing Semiring for or, concat

If we choose:
* add := or
* mul := concat

Then we are unable to implement mul_comm, since concat is not commutative.
This we cannot implement CommSemiring, however we can implement a Semiring:

```lean
instance IsSemiring_or_concat {α: Type}: Semiring (@Lang α) :=
  {
    add := or
    add_assoc := simp_or_assoc
    zero := emptyset
    zero_add := simp_or_emptyset_l_is_r
    add_zero := simp_or_emptyset_r_is_l
    add_comm := simp_or_comm
    nsmul := nsmul_or

    mul := concat
    zero_mul := simp_concat_emptyset_l_is_emptyset
    mul_zero := simp_concat_emptyset_r_is_emptyset
    mul_assoc := simp_concat_assoc

    one := emptystr
    one_mul := simp_concat_emptystr_l_is_r
    mul_one := simp_concat_emptystr_r_is_l

    left_distrib := simp_or_concat_left_distrib
    right_distrib := simp_or_concat_right_distrib
  }
```

Unfortunately, unlike in Coq, the implementation of the Semiring is not enough to be able to use the ring tactic.

## References

* [CommSemiring Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#CommSemiring)
* [Mathlib ring tactic lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Ring/Basic.lean)