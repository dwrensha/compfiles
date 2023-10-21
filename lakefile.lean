import Lake

open Lake DSL

package compfiles

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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "30c94754f9063d6bc090079e2527087f224f5d6d"
