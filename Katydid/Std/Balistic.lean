import Katydid.Std.Lists

import Katydid.Std.Ltac
import Qq
open Qq

-- balistic is a tactic that tries to solve simple theorems about lists

-- This temporarily fixes matching exists using quote4 in wreck_exists
-- see https://github.com/leanprover-community/quote4/issues/52
set_option linter.constructorNameAsVariable false

-- TODO: incorporate ac_rfl into balistic
-- ac_rfl uses IsAssociative to prove associativity of operators
example (xs ys zs: List α): (xs ++ ys ++ zs) = (xs ++ ys) ++ zs := by
  ac_rfl

-- list_empty_matcher is a tactic that tries to solve simple theorems about empty lists
-- Reference for list tactic in Coq: https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
local elab "list_empty_matcher" : tactic => newTactic do
  let goal ← getGoalProp
  match goal with
  | ~q([] ≠ $x :: $xs) =>
    -- [] ≠ x :: xs
    run `(tactic| apply list_cons_nil_ne )
  | ~q($x :: $xs ≠ []) =>
    -- x :: xs ≠ []
    run `(tactic| apply list_cons_ne_nil )
  | ~q([$x] ++ $xs ≠ []) =>
    -- [x] ++ xs ≠ []
    run `(tactic| apply list_append_ne_nil )
  | ~q($xs ++ [$x] ≠ []) =>
    -- xs ++ [x] ≠ []
    run `(tactic| apply list_append_nil_ne )
  | _ =>
    let hyps ← getHypothesesProp
    for (name, ty) in hyps do
      let matched ← match ty with
      | ~q([] = $x :: $xs) =>
        -- [] = x :: xs -> False
        run `(tactic| contradiction )
        return true
      | ~q($x :: $xs = []) =>
        -- x :: xs = [] -> False
        run `(tactic| contradiction )
        return true
      | ~q($xs ++ $ys = []) =>
        -- xs ++ ys = [] -> xs = [] /\ ys = []
        let conjName ← mkHyp "H" `((list_app_nil_nil _ _).mp $name)
        run `(tactic| clear $name)
        _ ← mkHyp (toString name ++ "Left") `(($conjName).left )
        _ ← mkHyp (toString name ++ "Right") `(($conjName).right )
        run `(tactic| clear $conjName)
        run `(tactic| try subst_vars )
        return true
      | ~q([] = $xs ++ $ys) =>
        -- [] = xs ++ ys -> xs = [] /\ ys = []
        let symmName ← mkHyp "Hsymm" `(Eq.symm $name)
        run `(tactic| clear $name)
        let conjName ← mkHyp "H" `((list_app_nil_nil _ _).mp $symmName)
        run `(tactic| clear $symmName)
        _ ← mkHyp (toString name ++ "Left") `(($conjName).left )
        _ ← mkHyp (toString name ++ "Right") `(($conjName).right )
        run `(tactic| clear $conjName)
        run `(tactic| try subst_vars )
        return true
      | _ =>
        return false
      if matched then
        -- matching one is enough
        return ()
    throwError "tactic 'list_empty_matcher' did not match the goal or any hypotheses"

local elab "list_empty_rewriter" : tactic => newTactic do
  run `(tactic| (first
    | rw [list_app_nil_l] at *
    | rw [list_app_nil_r] at *
  ))

local elab "list_empty": tactic => newTactic do
  run `(tactic| (first
    | list_empty_matcher
    | list_empty_rewriter
  ))

example (H: [] = List.cons x xs): False := by
  have _: Lean.Name := `list_empty
  list_empty

example (H: List.cons x xs = []): False := by
  list_empty

example (H: [] = x :: xs): False := by
  list_empty

example (H: x :: xs = []): False := by
  list_empty

example: [] ≠ x :: xs := by
  list_empty

example: x :: xs ≠ [] := by
  list_empty

example (H : xs ++ ys = []): ys = [] := by
  list_empty
  rfl

example (H0: xs ++ ys = []) (H1: zs = ys): zs = [] := by
  list_empty
  rfl

example (H0: [] = xs ++ ys) (H1: zs = ys): zs = [] := by
  list_empty
  rfl

example: [] ++ xs = xs := by
  list_empty

example: xs ++ [] = xs := by
  list_empty

example (H: [] ++ xs = ys): ys = xs := by
  list_empty
  subst_vars
  rfl

example (H: xs ++ [] = ys): ys = xs := by
  list_empty
  subst_vars
  rfl

example: [] ≠ [x] := by
  list_empty

example: [x] ≠ [] := by
  list_empty

local elab "list_single_matcher" : tactic => newTactic do
  let goal ← getGoalProp
  match goal with
  | ~q([] ≠ $xs ++ ($y :: $ys)) =>
    -- [] ≠ xs ++ y :: ys
    run `(tactic| apply list_nil_ne_app_cons )
  | ~q($xs ++ ($y :: $ys) ≠ []) =>
    -- xs ++ y :: ys ≠ []
    run `(tactic| apply list_app_cons_ne_nil )
  | ~q($xs ++ [$x] = $ys ++ [$y]) =>
      -- xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y
    run `(tactic| apply list_inj_tail_app)
  | ~q($x :: $xs = $y :: $ys) =>
    -- x :: xs = y :: ys -> x = y /\ xs = ys
    run `(tactic| apply list_cons_eq.mpr)
  | _ =>
    let hyps ← getHypothesesProp
    for (name, ty) in hyps do
      let matched ← match ty with
      | ~q($xs ++ $ys = [$a]) =>
        -- xs ++ ys = [a] -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = [])
        applyIn name `(list_app_eq_unit)
        return true
      | ~q([$a] = $xs ++ $ys) =>
        -- [a] = xs ++ ys -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = [])
        applyIn name `(list_eq_unit_app)
        return true
      | ~q([] = $xs ++ ($y :: $ys)) =>
        -- [] = xs ++ y :: ys -> False
        _ ← mkHyp (toString name) `(list_nil_ne_app_cons _ _ _ $name)
        run `(tactic| contradiction )
        return true
      | ~q($xs ++ ($y :: $ys) = []) =>
        -- xs ++ y :: ys = [] -> False
        _ ← mkHyp (toString name) `(list_app_cons_ne_nil _ _ _ $name)
        run `(tactic| contradiction )
        return true
      | ~q($xs ++ [$x] = $ys ++ [$y]) =>
        -- xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y
        applyIn name `(list_app_inj_tail)
        _ ← mkHyp (toString name ++ "Left") `(($name).left )
        _ ← mkHyp (toString name ++ "Right") `(($name).right )
        return true
      | ~q($x :: $xs = $y :: $ys) =>
        -- x :: xs = y :: ys -> x = y /\ xs = ys
        applyIn name `(list_cons_eq.mp)
        _ ← mkHyp (toString name ++ "Left") `(($name).left )
        _ ← mkHyp (toString name ++ "Right") `(($name).right )
        return true
      | _ =>
        return false
      if matched then
        -- matching one is enough
        return ()
    throwError "tactic 'list_single' did not match the goal or any hypotheses"

local elab "list_single_rewriter": tactic => newTactic do
  run `(tactic| (first
    | rw [list_app_assoc_singleton] at *
    | rw [← list_app_comm_cons] at *
  ))

local elab "list_single": tactic => newTactic do
  run `(tactic| (first
    | list_single_matcher
    | list_single_rewriter
  ))

example (H: xs ++ ys = [a]): (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  list_single
  assumption

example (H: [a] = xs ++ ys): (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  list_single
  assumption

example (y: α) (xs ys: List α): [] ≠ xs ++ (y :: ys) := by
  list_single

example (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  list_single

example (xs ys: List α) (y: α): ([] ≠ xs ++ (y :: ys)) := by
  list_single

example (xs ys: List α) (y: α): (xs ++ (y :: ys) ≠ []) := by
  list_single

example (as xs ys: List α) (z: α) (H: xs ++ (ys ++ [z]) = as): as = (xs ++ ys) ++ [z] := by
  list_single
  apply Eq.symm
  assumption

example (as xs ys: List α) (z: α) (H: (xs ++ ys) ++ [z] = as): as = xs ++ (ys ++ [z]) := by
  list_single
  apply Eq.symm
  assumption

example (x: α) (xs ys: List α): x :: (xs ++ ys) = (x :: xs) ++ ys := by
  list_single

example (x: α) (as xs ys: List α) (H: as = x :: (xs ++ ys)): (x :: xs) ++ ys = as := by
  list_single
  apply Eq.symm
  assumption

example (x y: α) (xs ys: List α) (H: x :: xs = y :: ys): x = y := by
  list_single
  assumption

example (x y: α) (xs ys zs: List α) (H: x = y) (H0: xs = zs) (H1: ys = zs): x :: xs = y :: ys := by
  list_single
  rw [H, H0, H1]
  apply And.intro <;> rfl

example (xs ys: List α) (x y: α) (H: xs ++ [x] = ys ++ [y]): x = y := by
  list_single
  assumption

example (xs ys zs: List α) (x y: α) (H: x = y) (H0: xs = zs) (H1: ys = zs): xs ++ [x] = ys ++ [y] := by
  list_single
  rw [H, H0, H1]
  apply And.intro <;> rfl

example (xs ys zs: List α) (y z: α) (H: xs ++ ys ++ [y] = zs ++ [z]): y = z := by
  list_single
  assumption

example (xs ys zs: List α) (y z: α) (H: xs ++ (ys ++ [y]) = zs ++ [z]): y = z := by
  list_single
  list_single
  assumption

-- In the goal and hypotheses, simplify at least these two theorems
-- list_app_inv_head: xs ++ ys = xs ++ zs -> ys = zs
-- list_app_inv_tail: xs ++ zs = ys ++ zs -> xs = ys
local elab "list_app" : tactic => newTactic do
  run `(tactic| simp )

example (xs ys zs: List α):
  xs ++ ys = xs ++ zs -> ys = zs := by
  list_app

example (xs ys zs: List α):
  ys ++ xs = zs ++ xs -> ys = zs := by
  list_app

example (xs ys zs: List α):
  ys = zs -> xs ++ ys = xs ++ zs := by
  list_app

example (xs ys zs: List α):
  ys = zs -> ys ++ xs = zs ++ xs := by
  list_app

local elab "wreck_exists" : tactic => newTactic do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    let matched ← match ty with
    | ~q(∃ x _y, $p x) =>
      let e ← fresh "e"
      let E ← fresh "E"
      run `(tactic| cases $name:ident <;> rename_i $name:ident <;> rename_i $e:ident)
      run `(tactic| cases $name:ident <;> rename_i $name:ident <;> rename_i $E:ident)
      return true
    | _ =>
      return false
    if matched then
      -- matching one is enough
      return ()
  throwError "tactic 'wreck_exists' did not match the goal or any hypotheses"

local elab "wreck_conj": tactic => newTactic do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    let matched ← match ty with
    | ~q($x /\ $y) =>
      _ ← mkHyp (toString name ++ "Left") `(($name).left )
      _ ← mkHyp (toString name ++ "Right") `(($name).right )
      run `(tactic| clear $name)
      return true
    | _ =>
      return false
    if matched then
      -- matching one is enough
      return ()
  throwError "tactic 'wreck_conj' did not match the goal or any hypotheses"

-- list_app_uncons:
--  Finds an hypotheses that it can deconstruct using the list_app_cons lemma:
--  ys ++ zs = x :: xs
--  into the two goals, which consist of the possible combinations, as in:
--  - ys = [] /\ zs = x :: xs
--  - .
local elab "list_app_uncons" : tactic => newTactic do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    let matched ← match ty with
    | ~q($ys ++ $zs = $x :: $xs ) =>
      applyIn name `(list_app_uncons)
      run `(tactic| cases $name:ident <;> rename_i $name:ident)
      run `(tactic| any_goals wreck_exists)
      run `(tactic| try all_goals wreck_conj)
      run `(tactic| try all_goals simp [*])
      return true
    | ~q($x :: $xs = $ys ++ $zs) =>
      applyIn name `(symm)
      applyIn name `(list_app_uncons)
      run `(tactic| cases $name:ident <;> rename_i $name:ident)
      run `(tactic| any_goals wreck_exists)
      run `(tactic| try all_goals wreck_conj)
      run `(tactic| try all_goals simp [*])
      return true
    | _ =>
      return false
    if matched then
      -- matching one is enough
      return ()
  throwError "tactic 'list_app_uncons' did not match the goal or any hypotheses"

example (xs ys: List α) (x y: α):
  xs ++ ys = [x,y] ->
  (xs = [] /\ ys = [x,y])
  \/ (xs = [x] /\ ys = [y])
  \/ (xs = [x,y] /\ ys = []) := by
  intro H
  list_app_uncons
  list_single
  cases H with
  | inl H =>
    apply Or.inl
    assumption
  | inr H =>
    apply Or.inr
    assumption

example (xs ys: List α) (x y: α):
  xs ++ ys = [x,y,z] ->
  (xs = [] /\ ys = [x,y,z])
  \/ (xs = [x] /\ ys = [y,z])
  \/ (xs = [x,y] /\ ys = [z])
  \/ (xs = [x,y,z] /\ ys = []) := by
  intro H
  list_app_uncons
  list_app_uncons
  list_single
  assumption

-- garbage_collect_rfl removes hypotheses of the form x = x
local elab "garbage_collect_rfl" : tactic => newTactic do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    let matched ← match ty with
    | ~q($x = $y) =>
      if ← Lean.Meta.isExprDefEq x y then
        run `(tactic| clear $name)
        return true
      else
        return false
    | _ =>
      return false
    if matched then
      -- matching one is enough
      return ()
  throwError "tactic 'garbage_collect_rfl' did not match the goal or any hypotheses"

-- Tactic Combinators
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#tactic-combinators

-- or tactics
-- first | t₁ | t₂ | ... | tₙ

-- repeat tactic
-- repeat (first | t1 | ... | tₙ)

elab "balistic" : tactic => newTactic do
  run `(tactic| repeat (first
    | garbage_collect_rfl
    | list_empty
    | list_single
    | list_app_uncons
    | wreck_conj
  ) <;> (try assumption)
    <;> subst_vars
    <;> (try simp)
    <;> (try exact ⟨rfl, rfl⟩)
    <;> (try contradiction)
  )

example: ∀ (x y: List α) (a: α),
    [] ≠ x ++ a :: y := by
intro x y a
intro H -- TODO: add list_cons_neq to balistic and try to remove this intro
balistic

example: ∀ (x y:List α) (a: α),
  x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [] := by
intro x y a
intro H
balistic

-- An example we have done before, but now with balistic
example:
  ∀ (xs ys: List α) (x y: α),
  xs ++ ys = [x, y] ->
  (xs = [] /\ ys = [x, y])
  \/ (xs = [x] /\ ys = [y])
  \/ (xs = [x, y] /\ ys = []) := by
intro xs ys x y H
balistic

-- An example we have done before, but now with balistic and simp
example:
  ∀ (xs ys: List α) (x y: α),
  xs ++ ys = [x,y] ->
  (xs = [] /\ ys = [x,y])
  \/ (xs = [x] /\ ys = [y])
  \/ (xs = [x,y] /\ ys = []) := by
intro xs ys x y H
balistic

-- An example we have done before, but now with balistic and simp
example: ∀ (x y: α) (xs ys: List α),
    xs ++ ys = [x,x,y] ->
    (xs = [] /\ ys = [x,x,y])
    \/ (xs = [x] /\ ys = [x,y])
    \/ (xs = [x,x] /\ ys = [y])
    \/ (xs = [x,x,y] /\ ys = []) := by
intro x y xs ys H
balistic

-- An example we have done before, but now with balistic and simp
-- This required auto 10 in Coq.
example: ∀ (x y: α) (xs ys: List α),
    xs ++ ys = [x,x,x,y] ->
    (xs = [] /\ ys = [x,x,x,y])
    \/ (xs = [x] /\ ys = [x,x,y])
    \/ (xs = [x,x] /\ ys = [x,y])
    \/ (xs = [x,x,x] /\ ys = [y])
    \/ (xs = [x,x,x,y] /\ ys = []) := by
intro x y xs ys H
balistic

example: ∀ (x: α) (y: α) (xs: List α) (ys: List α),
  x :: xs = [y] ++ ys ->
  x = y /\ xs = ys := by
intro x y xs ys H
balistic

example: ∀ (x y z: α),
    [x, y, z] = [x, y] ++ [z] := by
intro x y z
balistic

example: ∀ (x y: α) (xs ys zs xs': List α),
  x ≠ y ->
  xs ++ ys ++ zs = xs' ++ [x] ->
  zs ≠ [y] := by
intro x y xs ys zs xs' xy H
intro zsy
subst_vars
balistic

example:
  ∀ (x y: α) (_nxy: x ≠ y) (_xy: y = x), False := by
intro x y nxy xy
have xy' := Eq.symm xy -- TODO: contradiction should be smarter
contradiction

example:
  ∀ (x y: α) (_xy: x ≠ y) (xs: List α),
  xs ++ [x] ++ [y] ≠ [y] ++ [x] := by
intro x y xy xs H
balistic

example:
  ∀ (x y: α) (_xy: x ≠ y) (xs: List α),
  xs ++ [x] ++ [y] ≠ [y] ++ [y] ++ [y] ++ [x] := by
intro x y nxy xs h
balistic

example:
  ∀ (x y: α) (_xy: x ≠ y) (xs: List α),
  [y] ++ [y] ++ xs ≠ [x] := by
intro x y xy xs h
balistic
cases h <;> balistic

example:
  ∀ (xs: List α) (x: α),
  xs ++ [x] ≠ [] := by
intro xs x
balistic
