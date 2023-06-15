import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "cc2bef43c33ef0bd119cf8f8c696466bb194d331"
