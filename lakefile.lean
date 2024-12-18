import Lake

open Lake DSL

abbrev leanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

package compfiles where
  leanOptions := leanOptions ++ #[⟨`weak.linter.style.multiGoal, true⟩]
  moreServerOptions := leanOptions ++ #[⟨`linter.style.multiGoal, true⟩]

@[default_target]
lean_lib ProblemExtraction

@[default_target]
lean_lib Compfiles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

@[default_target]
lean_exe extractProblems where
  root := `scripts.extractProblems
  supportInterpreter := true

@[default_target]
lean_exe checkSolution where
  root := `scripts.checkSolution
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "main"
