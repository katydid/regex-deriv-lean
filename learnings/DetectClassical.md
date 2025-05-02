# Detecting the use of Classical.Choice

If you do not want to use the Law of Excluded Middle in the proofs of your theorems, you need to make sure that you do not use the axiom `Classical.Choice`.

Note that any computable definition does not use Classical.Choice.
Only if a `def` is marked with `noncomputable` does possibly use Classical.Choice, for example:

```lean
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some (Classical.choice h) else none
```

Theorems are more lax and do not distinguish between theorems that use the Law of Exluded Middle and those that do not.
If we want to enforce this, we need to build our own detector.

## Building a Detector

In your `lakefile.lean` you will need to hook up the detector, via packageLinters lean options.
Here is an example:

```lean
import Lake
open Lake DSL

package mypackage

abbrev packageLinters : Array LeanOption := #[
  ⟨`weak.linter.detectClassical, true⟩
]

abbrev packageLeanOptions :=
  packageLinters

@[default_target]
lean_lib Mypackage where
  leanOptions := packageLeanOptions
  moreServerOptions := packageLinters
```

In your `Mypackage.lean` you will need to import your detector:

```lean
import Myproject.Linter.DetectClassical
import ...
```

In your the folder `Myproject/Linter` you will need to create a file called `DetectClassical.lean`:

```lean
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

namespace Myproject.Linter

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

@[inherit_doc Myproject.Linter.linter.detectClassical]
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

end Myproject.Linter
```

## Use the Detector

Now that the detector is created, you will want to use it.

Simply, import it inside the files where you want to detect the use of classical:

```lean
import Myproject.Linter.DetectClassical
```

Then run `lake build` and the warnings and you will see warning of the following form:

```
warning: ././././Myproject/Myfile.lean:518:6: 'Myfile.mytheorem' depends on 'Classical.choice' on axioms: [propext, Quot.sound, Classical.choice]
note: this linter can be disabled with `set_option linter.detectClassical false`
```

You will also see the same warnings in VSCode when hovering on theorems with a yellow swiggle.

## References

* [Zulip Chat on restricting axioms](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms)
* [Example of noncomputable def](https://github.com/leanprover/lean4/blob/d26d7973ad39eab976ed351255ee30f038439944/src/Init/Data/Option/Lemmas.lean#L585)