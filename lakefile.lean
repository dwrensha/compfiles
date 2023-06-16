import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "2edc8bf32ccf16fde8f412b6f759abedf7011157"
