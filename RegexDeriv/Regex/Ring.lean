import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

import RegexDeriv.Regex.Language

open Language

def nsmul_or (n: Nat) (r: Lang α): Lang α :=
  match n with
  | 0 => emptyset
  | Nat.succ n' => or (nsmul_or n' r) r

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
    mul_comm := simp_and_comm

    left_distrib := simp_or_and_left_distrib
    right_distrib := simp_or_and_right_distrib
  }

-- Test for the ring tactic
example (a : Lang α) : 0 + a = a := by
  ring

-- Test for the ring tactic
example (a b c : Lang α) : (a + b) * c = (a * c) + (b * c) := by
  ring

-- Test for the ring tactic
example (a b c : Lang α) : (a + 0 + b) * c = (a * 1 * c) + (b * c) := by
  ring

-- Test for the ring_nf tactic
example (a: Lang α) (H: b = a * 3): a + a + a = b := by
  ring_nf
  rw [H]
