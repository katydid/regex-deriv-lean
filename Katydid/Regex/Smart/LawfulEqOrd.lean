import Katydid.Std.Linter.DetectClassical

import Katydid.Std.Ordering

-- TODO: Wait for Std.LawfulEqOrd to land, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Ordering.2Eeq.20is.20equivalent.20to.20LawfulEq/with/519113072
theorem neq_is_lt_or_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (neq: x ≠ y): (x < y) \/ (x > y) := by
  admit

theorem lt_and_gt_is_impossible [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: x < y) (hgt: x > y): False := by
  admit

theorem not_lt_is_gt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x < y)) (hneq: x ≠ y): x > y := by
  admit

theorem not_gt_is_lt [o: Ord α] [d: DecidableEq α] {x y: α}
  (hlt: Not (x > y)) (hneq: x ≠ y): x < y := by
  admit

theorem not_less_than_is_greater_than [o: Ord α] [DecidableEq α] {x y: α}
  (neq: x ≠ y) (nlt: Not (x < y)): x > y := by
  have h := neq_is_lt_or_gt neq
  cases h
  case inl h =>
    contradiction
  case inr h =>
    exact h
