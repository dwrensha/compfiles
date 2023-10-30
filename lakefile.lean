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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "61e8e6811a490a7edea6d6a095bfcccbb5c18b0c"
