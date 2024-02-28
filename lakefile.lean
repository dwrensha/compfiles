import Lake

open Lake DSL

package compfiles where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

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

@[default_target]
lean_exe tryTacticAtEachStep where
  root := `scripts.tryTacticAtEachStep
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "5bd4e6631ac675bfb63ab821d9823f1f3a1f1a2c"
