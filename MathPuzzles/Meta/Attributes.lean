import Lean.Elab.Command
import Lean.Meta.Basic
import Mathlib.Tactic.LabelAttr

/-!
Attributes to aid in "problem extraction".

For the math problems that we archive, we aim to include proofs in-line.
That presents a problem, however, if someone wants to try solving the
problems without seeing the solutions.
Therefore, we have "problem extraction" -- a means of stripping solutions.

During problem extraction, all declarations are removed
except those that have been tagged with one of the below attributes.
-/

open Lean Elab

/--
Indicates that a theorem is a problem statement. During problem extraction,
the proof is replaced by a `sorry`.
-/
register_label_attr problem_statement

/--
Indicates that a declaration is required to set up a problem statement.
During problem extraction, the declaration is kept completely intact.
-/
register_label_attr problem_setup

/--
Indicates that a declaration represents data that is intended to
be filled in as part of a solution.
During problem extraction, the body is replaced by a `sorry`.
During judging, a human will inspect the filled-in body
to see whether it is reasonable.
-/
register_label_attr solution_data
