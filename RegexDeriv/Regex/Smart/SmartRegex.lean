import RegexDeriv.Std.Linter.DetectClassical

import RegexDeriv.Regex.Language
import RegexDeriv.Regex.Predicate

open List

namespace SmartRegex

inductive Regex (α: Type u): Type (u + 1) where
  | emptyset : Regex α
  | emptystr : Regex α
  | any : Regex α -- We introduce any, so that we can apply smart constructor rules based on (star any)
  | pred : (p: Predicate.Pred α) → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving Ord, DecidableEq, Repr

instance [Ord α]: LE (Regex α) where
  le x y := (Ord.compare x y).isLE

instance [Ord α]: LT (Regex α) where
  lt x y := (Ord.compare x y) = Ordering.lt

instance inst_regex_beq {α: Type u} [DecidableEq (Regex α)]: BEq (Regex α) := inferInstance

instance [DecidableEq α]: DecidableEq (Regex α) := inferInstance

instance [Ord α]: Ord (Regex α) := inferInstance

def Regex.eq_of_beq {α: Type u} {a b : Regex α} [d: DecidableEq α]
  (heq: a == b): a = b := of_decide_eq_true heq

def Regex.rfl {α: Type u} {a: Regex α} [d: DecidableEq (Regex α)]: a == a := of_decide_eq_self_eq_true a

instance instLawfulBEq_Regex {α: Type u} [DecidableEq α]: LawfulBEq (Regex α) where
  eq_of_beq : {a b : Regex α} → a == b → a = b := Regex.eq_of_beq
  rfl : {a : Regex α} → a == a := Regex.rfl

def Regex.le [Ord α] (x y: Regex α): Bool :=
  x <= y

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def onlyif' {cond: Prop} (dcond: Decidable cond) (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def denote {α: Type} [Ord α] (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.any => Language.any
  | Regex.pred p => Language.pred p.eval
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

def null (r: Regex α): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.any => false
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

-- smartStar is a smart constructor for Regex.star which incorporates the following simplification rules:
-- 1. star (star x) = star x (Language.simp_star_star_is_star)
-- 2. star emptystr = emptystr (Language.simp_star_emptystr_is_emptystr)
-- 3. star emptyset = emptystr (Language.simp_star_emptyset_is_emptystr)
def smartStar (x: Regex α): Regex α :=
  match x with
  | Regex.emptyset => Regex.emptystr
  | Regex.emptystr => Regex.emptystr
  | Regex.star _ => x
  | _ => Regex.star x

-- smartConcat is a smart constructor for Regex.concat that includes the following simplification rules:
-- 1. If x or y is emptyset then return emptyset (Language.simp_concat_emptyset_l_is_emptyset and Language.simp_concat_emptyset_r_is_emptyset)
-- 2. If x or y is emptystr return the other (Language.simp_concat_emptystr_r_is_l and Language.simp_concat_emptystr_l_is_r)
-- 3. If x is a concat then `((concat x1 x2) y) = concat x1 (concat x2 y)` use associativity (Language.simp_concat_assoc).
def smartConcat (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => y
  | Regex.concat x1 x2 =>
      -- smartConcat needs to be called again on the rigth hand side, since x2 might also be a Regex.concat.
      -- x1 is gauranteed to not be a Regex.concat if it has been constructed with smartConcat, so we do not called smartConcat again on the left hand side.
      Regex.concat x1 (smartConcat x2 y)
  | _otherwise =>
      match y with
      | Regex.emptyset => Regex.emptyset
      | Regex.emptystr => x
      | _otherwise => Regex.concat x y

-- insertOr inserts x into y, where y might be or expression and x is not.
-- It inserts x into y if x is not a duplicate found in the or expression of y.
-- It inserts x into y into a sorted position in the or expression of y.
-- example:
--   insertOr b (Regex.or a c) = Regex.or a (Regex.or b c)
--   insertOr a (Regex.or a c) = Regex.or a c
--   insertOr a b = Regex.or a b
--   insertOr a a = a
def insertOr [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match y with
  | Regex.or y1 y2 =>
    if y1 = x
      then y
    else if y1 < x
      then Regex.or y1 (insertOr x y2)
    else
      Regex.or x y
  | _ =>
    if x = y
      then y
    else if y < x
      then Regex.or y x
      else Regex.or x y

def mergeOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match y with
  | Regex.or y1 y2 =>
    match x with
    | Regex.or _ _ =>
      insertOr y1 (mergeOr x y2)
    | _ =>
      insertOr x y
  | _ =>
    insertOr y x

def smartOr {α: Type} [Ord α] [DecidableEq α] (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | Regex.star Regex.any => Regex.star Regex.any
  | _ =>
    match y with
    | Regex.emptyset => x
    | Regex.star Regex.any => Regex.star Regex.any
    | _ =>
      mergeOr x y

def derive [Ord α] [DecidableEq α] (r: Regex α) (a: α): Regex α :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.any => Regex.emptystr
  | Regex.pred p => onlyif' (p.decidableEval a) Regex.emptystr
  | Regex.or x y =>
      SmartRegex.smartOr (derive x a) (derive y a)
  | Regex.concat x y =>
      SmartRegex.smartOr
        (SmartRegex.smartConcat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      SmartRegex.smartConcat (derive x a) (Regex.star x)

def derives [Ord α] [DecidableEq α] (r: Regex α) (xs: List α): Regex α :=
  (List.foldl derive r) xs

def validate [Ord α] [DecidableEq α] (r: Regex α) (xs: List α): Bool :=
  null (derives r xs)
