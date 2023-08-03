import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "74ee5fbebe317f9f8f9c185a96e45d1e8cdd4371"
