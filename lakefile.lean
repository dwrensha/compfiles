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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "ae010c182d61a5a73d1abc6254057e49a1b8f390"
