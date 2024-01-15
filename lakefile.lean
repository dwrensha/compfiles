import Lake

open Lake DSL

package compfiles

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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "1d3b4790261b440e9fdcb04f52c39143d0992f45"
