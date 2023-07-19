import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "4eb7e8403cb392879e4f7cf987050c103a20cd1c"
