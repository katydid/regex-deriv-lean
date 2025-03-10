import Lake
open Lake DSL

package katydid

abbrev packageLinters : Array LeanOption := #[
  ⟨`weak.linter.detectClassical, true⟩
]

abbrev packageLeanOptions :=
  packageLinters

@[default_target]
lean_lib Katydid where
  leanOptions := packageLeanOptions
  moreServerOptions := packageLinters

-- dependencies std4, quote4 are obtained transitively through mathlib4
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
