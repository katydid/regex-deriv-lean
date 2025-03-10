import Katydid.Std.Linter.DetectClassical
import Katydid.Std.Decidable

import Katydid.Regex.Language

namespace IndexedRegex

open List

inductive Regex (α: Type): (List α -> Prop) -> Type where
  | emptyset : Regex α Language.emptyset
  | emptystr : Regex α Language.emptystr
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α (Language.pred a)
  | or : Regex α x → Regex α y → Regex α (Language.or x y)
  | concat : Regex α x → Regex α y → Regex α (Language.concat x y)
  | star : Regex α x → Regex α (Language.star x)

def null (r: Regex α l): Decidable (Language.null l) :=
  match r with
  | Regex.emptyset => Decidable.isFalse (Language.not_null_if_emptyset)
  | Regex.emptystr => Decidable.isTrue (Language.null_if_emptystr)
  | Regex.pred _ => Decidable.isFalse (Language.not_null_if_pred)
  | Regex.or x y =>
    Decidable.map (symm Language.null_iff_or)
      (Decidable.or (null x) (null y))
  | Regex.concat x y =>
    Decidable.map (symm Language.null_iff_concat)
      (Decidable.and (null x) (null y))
  | Regex.star _ => Decidable.isTrue (Language.null_if_star)

def iso {P Q: Language.Lang α} (ifflang: Q = P) (r: @Regex α P): @Regex α Q := by
  rw [ifflang]
  exact r

def iso' {P Q: Language.Lang α} (ifflang: ∀ xs, P xs <-> Q xs): P = Q := by
  funext xs
  have ifflang_xs: P xs ↔ Q xs := ifflang xs
  rw [ifflang_xs]

def iso'' {P Q: Language.Lang α} (ifflang: ∀ {xs: List α}, P xs <-> Q xs) (r: @Regex α P): @Regex α Q := by
  apply iso' at ifflang
  rw [<- ifflang]
  exact r

-- | scalar {s: Type u}: (Decidability.Dec s) -> Lang P -> Lang (Language.scalar s P)
def onlyif {cond: Prop} (dcond: Decidable cond) (r: Regex α l): Regex α (Language.onlyif cond l) :=
-- TODO
  sorry

def derive (r: Regex α l) (a: α): Regex α (Language.derive l a) :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr =>
    iso Language.derive_emptystr Regex.emptyset
  | Regex.pred p =>
    -- TODO
    -- iso Language.derive_pred (onlyif p Regex.emptystr)
    sorry
  | Regex.or x y =>
    iso Language.derive_or (Regex.or (derive x a) (derive y a))
  | Regex.concat x y =>
    -- TODO
    -- iso Language.derive_concat
    --   (Regex.or
    --     (onlyif (null x) (derive y a))
    --     (Regex.concat (derive x a) y)
    --   )
    sorry
  | Regex.star x =>
    iso Language.derive_star (Regex.concat (derive x a) (Regex.star x))

def denote (_: @Regex α l): Language.Lang α := l

-- decidableDenote shows that the derivative algorithm is decidable
def decidableDenote (r: @Regex α l): DecidablePred l :=
  fun w =>
    match w with
    | [] => null r
    | (a :: w) => decidableDenote (derive r a) w
