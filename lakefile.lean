import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "d93a0a4d5d3c5f6e89a1b904d3fc09ac2b743950"
