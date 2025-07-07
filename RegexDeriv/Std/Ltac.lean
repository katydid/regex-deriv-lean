import Lean.Meta.Tactic.Util
import Qq
open Qq

-- Execute `x` using the main goal local context and instances -
-- This is necessary to make sure that the context is properly updated for future tactics.
-- This way the state is affected by the tactic for reading from the local context by the next tactic.
-- Place this at the start of extra tactic's do notation block.
-- For example:
-- ```
--   local elab "mytacticname" : tactic => newTactic do
--     let goal ← getGoalProp
--     ...
-- ```
def newTactic (x : Lean.Elab.Tactic.TacticM α) : Lean.Elab.Tactic.TacticM α :=
  Lean.Elab.Tactic.withMainContext x

-- Check if the expression is a Prop and if so return it as a Q(Prop) that can be used in a pattern match.
private def castToProp (e: Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Q(Prop)) := do
  Qq.checkTypeQ (u := Lean.levelOne) e q(Prop)

-- getHypothesesProp returns the hypotheses as an array of tuples of (Hypothesis name, Q(Prop))
-- This way the hypothesis Q(Prop) can be used in a pattern match and
-- the name can be used to refer to the hypothesis in other tactics
def getHypothesesProp : Lean.Elab.Tactic.TacticM (Array (Lean.Syntax.Ident × Q(Prop))) := do
  let mut res := #[]
  for localDecl in ← Lean.MonadLCtx.getLCtx do
    if let some typ ← castToProp localDecl.type then
      let name := Lean.mkIdent localDecl.userName
      res := res.push (name, typ)
  return res

-- a tactic that prints the hypotheses and their types
elab "print_hypotheses" : tactic => do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    Lean.logInfo m!"{name}: {ty}"

example (_H1: 1 = 1) (_H2: 2 = 2): True := by
  -- uncomment to print: print_hypotheses
  simp

-- a tactic that prints the hypotheses, but only if they match a pattern
local elab "example_print_rfl_hypotheses_prop" : tactic => do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    if let ~q($x = $y) := ty then
      if ← Lean.Meta.isExprDefEq x y then
        Lean.logInfo m!"{name} is rfl"

example (_H1 : x = 5) (_H2 : 2 = 2) (_H3: y = y) (H4: 5 = 4): False := by
  -- uncomment to print: example_print_rfl_hypotheses_prop
  contradiction

def getHypotheses : Lean.Elab.Tactic.TacticM (Array (Lean.Syntax.Ident × Lean.Expr)) := do
  let mut res := #[]
  for localDecl in ← Lean.MonadLCtx.getLCtx do
    let name := Lean.mkIdent localDecl.userName
    res := res.push (name, localDecl.type)
  return res

-- use match_expr instead of Qq
-- see examples in https://github.com/leanprover/lean4/blob/a5162ca7489bfdbf1a2851cffd8fdcca9d2b9b56/src/Lean/Elab/Tactic/Omega/Frontend.lean#L431
local elab "example_print_rfl_hypotheses" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match_expr ty with
    | Eq _ x y =>
      if ← Lean.Meta.isExprDefEq x y then
        Lean.logInfo m!"{name} is rfl"
    | _ =>
      continue

example (_G1 : x > 5) (_G2 : 2 = 2) (_G3: y = y) (G4: 5 = 4): False := by
  -- uncomment to print: example_print_rfl_hypotheses
  contradiction

-- run is shorthand for evalTactic (← t).
def run (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic)): Lean.Elab.Tactic.TacticM Unit := do
  let t' ← t
  Lean.Elab.Tactic.evalTactic t'

-- an example tactic that applies a hypothesis to the goal if it matches a pattern
local elab "example_apply_hypothesis" : tactic => do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    if let ~q((((($a : Prop)) → $b) : Prop)) := ty then
      run `(tactic| apply $name )

example {A B: Prop} (P: A -> B) (a: A): B := by
  example_apply_hypothesis
  assumption

-- Returns the main goal as a Q(Prop), such that it can be used in a pattern match.
def getGoalProp : Lean.Elab.Tactic.TacticM Q(Prop) := do
  let goal ← Lean.Elab.Tactic.getMainTarget
  match ← castToProp goal with
  | some qType => return qType
  | none => throwError "goal is not a proposition"

-- An example to check whether the goal is already an hypothesis
local elab "example_assumption_tactic" : tactic => do
  let goal ← getGoalProp
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    if ← Lean.Meta.isExprDefEq ty goal then
      run `(tactic| exact $name )

example (Hx: x) (_Hy: y): x := by
  example_assumption_tactic

private theorem anda (a: Prop): a -> (a /\ a) := by
  intro a
  apply And.intro
  case left => assumption
  case right => assumption

-- An example to show how we can create a new tactic that only applies a lemma, if it matches the goal
elab "example_apply" : tactic => do
  match ← getGoalProp with
  -- Reference for pattern matching: https://github.com/gebner/quote4/blob/master/examples/conjs.lean
  | ~q($x /\ $y) => do
    if ← Lean.Meta.isExprDefEq x y then
      -- x /\ x -> x
      run `(tactic| apply anda )
  | _ => return ()

example (H: x): x /\ x := by
  example_apply
  example_assumption_tactic

-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : String) : m Lean.Syntax.Ident := do
  let lctx ← Lean.MonadLCtx.getLCtx
  let name := lctx.getUnusedName (Lean.Name.mkSimple suggestion)
  return Lean.mkIdent name

-- Removes quotes from the start of a string
def unquote (s: String): String :=
  s.dropWhile (λ c => c.isWhitespace || c == '"' || c == '`')

-- mkHyp makes a new hypothesis
--  let name ← fresh suggestion
--  evalTactic ← `(tactic| have $name := $t )
def mkHyp (suggestion: String) (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `term)): Lean.Elab.Tactic.TacticM Lean.Ident := Lean.Elab.Tactic.withMainContext do
  let t' ← t
  let suggestion' := unquote suggestion
  let name ← fresh <| unquote suggestion'
  run `(tactic| have $name := $t' )
  return name

-- an example that tries to apply a bunch to tactics to specific patterns
local elab "example_combo_tactic" : tactic => do
  let goal ← getGoalProp
  let hyps ← getHypothesesProp
  if let ~q($x /\ $y) := goal then
    if ← Lean.Meta.isExprDefEq x y then
    -- x /\ x -> x
    run `(tactic| apply anda )
  for (name, ty) in hyps do
    match ty with
    | ~q($x = $y) =>
      -- rewrite x = y everywhere
      run `(tactic| rw [ $name:term ] at * )
    | ~q($x :: $xs = []) =>
      -- x :: xs = [] -> False
      run `(tactic| contradiction )
    | ~q(($x : Nat) < $y) =>
      -- x < y -> x + 1 <= y
      let hsucc ← mkHyp "Hsucc" `(Nat.succ_lt_succ $name)
      _ ← mkHyp "HLe" `(Nat.le_of_lt_succ $hsucc)
    | _ => return ()

example (H : x = y) (Y: y): x /\ x := by
  example_combo_tactic
  example_assumption_tactic

example (x: Nat) (Hz: x = z) (H: z < y): (x + 1 <= y /\ x + 1 <= y):= by
  example_combo_tactic
  example_assumption_tactic

-- applyIn takes a hypothesis name and tactic and apply the tactic to the hypothesis and place the result in the same hypothesis
def applyIn (name: Lean.Ident) (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `term)): Lean.Elab.Tactic.TacticM Unit := Lean.Elab.Tactic.withMainContext do
  let t' ← t
  run `(tactic| have $name := $t' $name )
  let tempName: Lean.Ident ← fresh "H0"
  let tempBinder ← `(Lean.binderIdent| $tempName:ident)
  run `(tactic| rename_i $tempBinder)
  run `(tactic| clear $tempName)
  return ()

local elab "example_applyin_tactic" : tactic => do
  let hyps ← getHypothesesProp
  for (name, ty) in hyps do
    match ty with
    | ~q((((($a : Prop)) → $b)) /\ ($a')) =>
      if ← Lean.Meta.isExprDefEq a a' then
        let hleft ← mkHyp (toString name ++ "Left") `(($name).left )
        let hright ← mkHyp (toString name ++ "Right") `(($name).right )
        applyIn hright `($hleft)
    | _ => return ()

example (P: (A -> B) /\ A): B := by
  example_applyin_tactic
  assumption

-- Other References of using quote4 and other tactics:
--  - https://github.com/leanprover-community/mathlib4/blob/7e2613afa5a47788e24f31a386e4dfad92b40289/Mathlib/Tactic/Set.lean#L58
--  - https://github.com/leanprover-community/mathlib4/blob/2d97a156aa63b50456ed3e5a7d6af3096ac7958e/Mathlib/Tactic/Tauto.lean
--  - https://github.com/leanprover-community/mathlib4/blob/bac7310cc18d6ed292606d26ccb5fb9ffc697c7a/Mathlib/Tactic/Slice.lean
--  - https://github.com/siddhartha-gadgil/LeanAide
