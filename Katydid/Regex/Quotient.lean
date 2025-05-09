import Katydid.Regex.SimpleRegex

open SimpleRegex

private abbrev eqv (r1 r2 : Regex α) : Prop :=
  denote r1 = denote r2

infix:50 " ~ " => eqv

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

instance IsSetoid_Regex (α : Type) : Setoid (Regex α) where
   r     := eqv
   iseqv := IsEquivalence_Regex

-- `HasEquiv α` is the typeclass which supports the notation `x ≈ y`
-- All Setoids are instances of HasEquiv
-- instance {α : Sort u} [Setoid α] : HasEquiv α :=
--   ⟨Setoid.r⟩

-- We can use the generic theorems Setoid.refl, Setoid.symm, Setoid.trans

theorem Regex.refl (a : Regex α) : a ≈ a :=
  IsEquivalence_Regex.refl a

theorem Regex.symm {a b : Regex α} (hab : a ≈ b) : b ≈ a :=
  IsEquivalence_Regex.symm hab

theorem Regex.trans {a b c : Regex α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  IsEquivalence_Regex.trans hab hbc

def RegexQ (α : Type) : Type :=
  Quotient (IsSetoid_Regex α)

def RegexQ.mk {α : Type} (x: Regex α): RegexQ α :=
  Quotient.mk' x

-- Quotient is a specialized version of Quot, which infers the instance of Setoid
def RegexQ.mk' {α : Type} (x: Regex α): RegexQ α :=
  Quot.mk Setoid.r x

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

-- f = denote ∘ Regex.or

-- (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
theorem or_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): denote (Regex.or x1 y1) = denote (Regex.or x2 y2) := by
  unfold denote at *
  unfold eqv at *
  simp only [hx]
  simp only [hy]

def liftOrLang (x: Regex α) (y: Regex α): Language.Lang α :=
  Quotient.lift₂ (fun x' y' => denote (Regex.or x' y')) or_respects_eqv ⟦ x ⟧ ⟦ y ⟧

-- f = RegexQ.mkOr

theorem orq_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): RegexQ.mkOr x1 y1 = RegexQ.mkOr x2 y2 := by
  apply Quot.sound
  apply or_respects_eqv
  · apply hx
  · apply hy

def RegexQ.or: (RegexQ α -> RegexQ α -> RegexQ α) :=
  Quotient.lift₂ RegexQ.mkOr orq_respects_eqv

-- f = denote ∘ Regex.concat

theorem concat_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): denote (Regex.concat x1 y1) = denote (Regex.concat x2 y2) := by
  unfold denote at *
  unfold eqv at *
  simp only [hx]
  simp only [hy]

def liftConcatLang (x: Regex α) (y: Regex α): Language.Lang α :=
  Quotient.lift₂ (fun x' y' => denote (Regex.concat x' y')) concat_respects_eqv ⟦ x ⟧ ⟦ y ⟧

-- f = RegexQ.mkConcat

theorem concatq_respects_eqv (x1 y1 x2 y2: Regex α) (hx: x1 ~ x2) (hy: y1 ~ y2): RegexQ.mkConcat x1 y1 = RegexQ.mkConcat x2 y2 := by
  apply Quot.sound
  apply concat_respects_eqv
  · apply hx
  · apply hy

def RegexQ.concat: (RegexQ α -> RegexQ α -> RegexQ α) :=
  Quotient.lift₂ RegexQ.mkConcat concatq_respects_eqv

-- f = denote ∘ Regex.star

theorem star_respects_eqv:
  ∀ (x y: Regex α), x ~ y ->
    denote (Regex.star x) = denote (Regex.star y) := by
  intro x y
  intro H
  unfold denote
  simp only [H]

def liftStarQLang: (RegexQ α -> Language.Lang α) :=
  Quotient.lift (fun x => denote (Regex.star x)) star_respects_eqv

def liftStarLang (x: Regex α): Language.Lang α :=
  liftStarQLang (RegexQ.mk x)

-- ⟦x⟧ = Quot.mk Setoid.r x = RegexQ.mk x
-- Notation: backslash [[
def liftStarLang' (x: Regex α): Language.Lang α :=
  liftStarQLang ⟦ x ⟧

-- f = RegexQ.mkStar

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

-- test using Quotient.ind for a proof

-- proving idempotency on eqv
theorem Regex.eqv_or_idemp (x: Regex α): Regex.or x x ~ x := by
  apply Language.simp_or_idemp

-- proving idempotency on RegexQ.mk using Quot.sound
theorem RegexQ.mk_or_idemp (x: Regex α): RegexQ.mk (Regex.or x x) = RegexQ.mk x := by
  apply Quot.sound
  guard_target = (IsSetoid_Regex α).r (Regex.or x x) x
  apply Language.simp_or_idemp

-- proving idempotency on RegexQ.or using Quotient.ind, Quot.sound and Quotient.lift2
theorem RegexQ.or_idemp (x: RegexQ α): RegexQ.or x x = x := by
  cases x using Quotient.ind
  case a x' =>
  guard_hyp x': Regex α
  guard_target = RegexQ.or ⟦ x'⟧ ⟦x'⟧ = ⟦x'⟧
  apply Quotient.sound
  guard_target = Regex.or x' x' ≈ x'
  apply Language.simp_or_idemp

-- proving idempotency on RegexQ.or using RegexQ.or_idemp
theorem RegexQ.or_idemp' (x: RegexQ α): RegexQ.or x x = x := by
  rw [RegexQ.or_idemp]
