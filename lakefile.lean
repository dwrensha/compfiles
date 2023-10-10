import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

@[default_target]
lean_exe buildWebpage where
  root := `scripts.buildWebpage
  supportInterpreter := true

@[default_target]
lean_exe extractProblems where
  root := `scripts.extractProblems
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "3f4910debcdd03d6ca9f9063b698a36fd2e3c211"
