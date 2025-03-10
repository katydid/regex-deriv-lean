-- Thank you to Damiano Testa
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343

import Lean.Util.CollectAxioms
import Mathlib.Tactic.DeclarationNames

/-!
#  The "detectClassical" linter

The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/

open Lean Elab Command

namespace Katydid.Std.Linter

/--
The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "enable the detectClassical linter"
}

/--
The `linter.verbose.detectClassical` option is a flag to make the `detectClassical` linter emit
a confirmation on declarations that depend *not* on the `Classical.choice` axiom.
-/
register_option linter.verbose.detectClassical : Bool := {
  defValue := false
  descr := "enable the verbose setting for the detectClassical linter"
}

namespace DetectClassical

@[inherit_doc Katydid.Std.Linter.linter.detectClassical]
def detectClassicalLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.detectClassical (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let d := (stx.getPos?.getD default)
  let nmsd := (← Mathlib.Linter.getNamesFrom d)
  let nms := nmsd.filter (! ·.getId.isInternal)
  let verbose? := Linter.getLinterValue linter.verbose.detectClassical (← getOptions)
  for constStx in nms do
    let constName := constStx.getId
    let axioms ← collectAxioms constName
    if axioms.isEmpty then
      if verbose? then
        logInfoAt constStx m!"'{constName}' does not depend on any axioms"
      return
    if !axioms.contains `Classical.choice then
      if verbose? then
        logInfoAt constStx
          m!"'{constName}' is non-classical and depends on axioms: {axioms.toList}"
    else
      Linter.logLint linter.detectClassical constStx
        m!"'{constName}' depends on 'Classical.choice' on axioms: {axioms.toList}"

initialize addLinter detectClassicalLinter

end DetectClassical

end Katydid.Std.Linter
