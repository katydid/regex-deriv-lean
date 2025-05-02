import Katydid.Std.Linter.DetectClassical
import Katydid.Std.Decidable

import Katydid.Regex.Language

namespace IndexedRegex

open List

inductive Regex (α: Type): (List α -> Prop) -> Type where
  | emptyset : Regex α Language.emptyset
  | emptystr : Regex α Language.emptystr
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α (Language.pred p)
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

def onlyif_true {cond: Prop} {l: List α -> Prop} (condIsTrue: cond):
  (fun xs => (cond ∧ l xs)) = l := by
  funext xs
  simp only [eq_iff_iff, and_iff_right_iff_imp]
  intro p'
  assumption

def onlyif_false {cond: Prop} {l: List α -> Prop} (condIsFalse: ¬cond):
  (fun xs => (cond ∧ l xs)) = Language.emptyset := by
  funext xs
  rw [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case intro condIsTrue lxs =>
    contradiction
  case mpr =>
    intro h
    nomatch h

-- | scalar {s: Type u}: (Decidability.Dec s) -> Lang P -> Lang (Language.scalar s P)
def onlyif {cond: Prop} (dcond: Decidable cond) (r: Regex α l): Regex α (Language.onlyif cond l) :=
  match dcond with
  | isTrue h =>
    iso (onlyif_true h) r
  | isFalse h =>
    iso (onlyif_false h) Regex.emptyset

def derive (r: Regex α l) (a: α): Regex α (Language.derive l a) :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr =>
    iso Language.derive_emptystr Regex.emptyset
  | @Regex.pred _ p dp =>
    iso Language.derive_pred (onlyif (dp a) Regex.emptystr)
  | Regex.or x y =>
    iso Language.derive_or (Regex.or (derive x a) (derive y a))
  | Regex.concat x y =>
    iso Language.derive_concat
      (Regex.or
        (Regex.concat (derive x a) y)
        (onlyif (null x) (derive y a))
      )
  | Regex.star x =>
    iso Language.derive_star (Regex.concat (derive x a) (Regex.star x))

def denote (_: @Regex α l): Language.Lang α := l

-- decidableDenote shows that the derivative algorithm is decidable
def decidableDenote (r: @Regex α l): DecidablePred l :=
  fun w =>
    match w with
    | [] => null r
    | (a :: w) => decidableDenote (derive r a) w
