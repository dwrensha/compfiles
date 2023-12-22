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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "cf8e23a62939ed7cc530fbb68e83539730f32f86"
