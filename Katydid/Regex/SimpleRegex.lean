import Lean

import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.CongrM

import Katydid.Std.Linter.DetectClassical
import Katydid.Std.Decidable

import Katydid.Regex.Language

open List

namespace SimpleRegex

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def mkChar (c: Char): Regex Char :=
  Regex.pred (· = c)

def null (r: Regex α): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def derive (r: Regex α) (a: α): Regex α :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.pred p => onlyif (p a) Regex.emptystr
  | Regex.or x y => Regex.or (derive x a) (derive y a)
  | Regex.concat x y =>
      Regex.or
        (Regex.concat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      Regex.concat (derive x a) (Regex.star x)

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

def denote_onlyif {α: Type} (condition: Prop) [dcond: Decidable condition] (r: Regex α):
  denote (onlyif condition r) = Language.onlyif condition (denote r) := by
  unfold Language.onlyif
  unfold onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [denote]
    rw [Language.emptyset]
    simp only [false_iff, not_and]
    intro hc'
    contradiction

theorem null_commutes {α: Type} (r: Regex α):
  ((null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | pred p =>
    unfold denote
    rw [Language.null_pred]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold null
    simp only

theorem derive_commutes {α: Type} (r: Regex α) (x: α):
  denote (derive r x) = Language.derive (denote r) x := by
  induction r with
  | emptyset =>
    simp only [denote]
    rw [Language.derive_emptyset]
  | emptystr =>
    simp only [denote]
    rw [Language.derive_emptystr]
  | pred p =>
    simp only [denote]
    rw [Language.derive_pred]
    unfold derive
    rw [denote_onlyif]
    simp only [denote]
  | or p q ihp ihq =>
    simp only [denote]
    rw [Language.derive_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [denote]
    rw [Language.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    rw [denote_onlyif]
    congrm (Language.or (Language.concat (denote (derive p x)) (denote q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote]
    rw [Language.derive_star]
    guard_target =
      Language.concat (denote (derive r x)) (Language.star (denote r))
      = Language.concat (Language.derive (denote r) x) (Language.star (denote r))
    congrm ((Language.concat ?_ (Language.star (denote r))))
    guard_target = denote (derive r x) = Language.derive (denote r) x
    exact ih

def derives (r: Regex α) (xs: List α): Regex α :=
  (List.foldl derive r) xs

theorem derives_commutes {α: Type} (r: Regex α) (xs: List α):
  denote (derives r xs) = Language.derives (denote r) xs := by
  unfold derives
  rw [Language.derives_foldl]
  revert r
  induction xs with
  | nil =>
    simp only [foldl_nil]
    intro h
    exact True.intro
  | cons x xs ih =>
    simp only [foldl_cons]
    intro r
    have h := derive_commutes r x
    have ih' := ih (derive r x)
    rw [h] at ih'
    exact ih'

def validate (r: Regex α) (xs: List α): Bool :=
  null (derives r xs)

theorem validate_commutes {α: Type} (r: Regex α) (xs: List α):
  (validate r xs = true) = (denote r) xs := by
  rw [<- Language.validate (denote r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms
def decidableDenote (r: Regex α): DecidablePred (denote r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes r xs)

def smartishOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | _ =>
  match y with
  | Regex.emptyset => x
  | _ =>
  Regex.or x y

theorem Regex.smartishOr_is_or: denote (Regex.or x y) = denote (smartishOr x y) := by
  induction x with
  | emptyset =>
    rw [smartishOr]
    apply Language.simp_or_emptyset_l_is_r
  | _ =>
    induction y with
    | emptyset =>
      rw [smartishOr] <;> try (intro H ; contradiction)
      apply Language.simp_or_emptyset_r_is_l
    | _ =>
      rfl

theorem Regex.smartishOr_is_or': denote (Regex.or (Regex.or x y) z) = denote (smartishOr x (Regex.or y z)) := by
  induction x with
  | emptyset =>
    rw [smartishOr]
    guard_target = denote ((emptyset.or y).or z) = denote (y.or z)
    -- I want to rewrite with Language.simp_or_emptyset_l_is_r to get
    -- guard_target = denote (y.or z) = denote (y.or z)
    -- simp only [Language.simp_or_emptyset_l_is_r]
    sorry
  | _ =>
    induction y with
    | emptyset =>
      rw [smartishOr] <;> try (intro H ; contradiction)
      -- I want to rewrite: (emptyset.or z) to z inside denote (x.or (emptyset.or z))
      -- apply Language.simp_or_emptyset_r_is_l
      sorry
    | _ =>
      rw [smartishOr] <;>
      -- these goals are equal up to associativity, but I can't use ac_rfl
      sorry
