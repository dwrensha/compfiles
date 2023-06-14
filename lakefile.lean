import Lake

open Lake DSL

package mathpuzzles

@[default_target]
lean_lib MathPuzzles

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "282f8074f945290b63998f2fd7e72aa93caa5796"
