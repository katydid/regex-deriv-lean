import RegexDeriv.Std.Linter.DetectClassical

theorem beq_eq_or_neq {α: Type} [BEq α] (x y: α):
  BEq.beq x y \/ (Not (BEq.beq x y)) := by
  by_cases BEq.beq x y
  · left
    assumption
  · right
    assumption

theorem beq_eq_or_neq_prop {α: Type} [BEq α] [LawfulBEq α] (x y: α):
  x = y \/ (Not (x = y)) := by
  have h := beq_eq_or_neq x y
  cases h
  · case inl h =>
    left
    rw [beq_iff_eq] at h
    assumption
  · case inr h =>
    right
    intro h'
    apply h
    rw [h']
    rw [beq_iff_eq]
