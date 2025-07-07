import RegexDeriv.Std.Linter.DetectClassical

import RegexDeriv.Std.Ordering

-- TODO: Wait for Std.LawfulEqOrd to land, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Ordering.2Eeq.20is.20equivalent.20to.20LawfulEq/with/519113072
theorem neq_is_lt_or_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (neq: x ≠ y): (x < y) \/ (x > y) := by
  admit

theorem lt_and_gt_is_impossible [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: x < y) (hgt: x > y): False := by
  admit

theorem not_lt_and_not_gt_is_eq [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x < y)) (hgt: Not (x > y)): x = y := by
  admit

theorem not_lt_is_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x < y)) (hneq: x ≠ y): x > y := by
  admit

theorem not_gt_is_lt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x > y)) (hneq: x ≠ y): x < y := by
  admit

theorem Ordering.lt_is_lt [o: Ord α] [d: DecidableEq α] {x y: α}
  (h: Ord.compare x y = Ordering.lt): (x < y) := by
  admit

theorem Ordering.gt_is_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (h: Ord.compare x y = Ordering.gt): (x > y) := by
  admit

theorem Ordering.eq_is_eq [o: Ord α] [d: DecidableEq α] {x y: α}
  (h: Ord.compare x y = Ordering.eq): (x = y) := by
  admit

theorem lt_is_neq [o: Ord α] [d: DecidableEq α] {x y: α}
  (h: x < y): (x ≠ y) := by
  admit

theorem gt_is_neq [o: Ord α] [d: DecidableEq α] {x y: α}
  (h: x > y): (x ≠ y) := by
  admit

theorem not_less_than_is_greater_than [o: Ord α] [DecidableEq α] {x y: α}
  (neq: x ≠ y) (nlt: Not (x < y)): x > y := by
  have h := neq_is_lt_or_gt neq
  cases h
  case inl h =>
    contradiction
  case inr h =>
    exact h

theorem neq_of_beq [o: Ord α] [DecidableEq α] {x y: α}:
  (x == y) = false -> x ≠ y := by
  admit

theorem not_eq_is_neq [o: Ord α] [DecidableEq α] {x y: α}:
  Not (x = y) <-> x ≠ y := by
  sorry
