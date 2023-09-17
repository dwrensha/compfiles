import Lean.Elab.Command
import Lean.Meta.Basic
import Mathlib.Tactic.LabelAttr
import Std.Lean.NameMapAttribute

/-!
Attributes to aid in "problem extraction".

For the math problems that we archive, we aim to include proofs in-line.
That presents a problem, however, if someone wants to try solving the
problems without seeing the solutions.
Therefore, we have "problem extraction" -- a means of stripping solutions.

During problem extraction, all declarations are removed
except those that have been tagged with one of the below attributes.
-/

namespace MathPuzzles.Meta

open Lean Elab

/--
Indicates that a declaration is required to set up a problem statement.
During problem extraction, the declaration is kept completely intact.
-/
syntax (name := problemSetup) "#[problem_setup]" command : command

/--
Indicates that a declaration represents data that is intended to
be filled in as part of a solution.
During problem extraction, the body is replaced by a `sorry`.
During judging, a human will inspect the filled-in body
to see whether it is reasonable.
-/
syntax (name := solutionData) "#[solution_data]" command : command

--------------------------------

structure Entry where
(module : Name)
(string : String)

abbrev ProblemExtractionExtension :=
  SimplePersistentEnvExtension Entry (Array Entry)

initialize problemExtractionExtension : ProblemExtractionExtension ←
  registerSimplePersistentEnvExtension {
    name := `problem_extraction
    addImportedFn := fun arrays =>
      arrays.foldl (init := ∅) fun acc as =>
        as.foldl (init := acc) fun acc' a => acc'.push a
    addEntryFn    := fun s n => s.push n
    toArrayFn     := fun es => es.toArray
  }

def matchDecl : Syntax → Command.CommandElabM (String.Pos × String.Pos)
| `(command| $_:declModifiers theorem%$thm $_:declId $_:declSig :=%$colEq $_:term) => do
    let .some startPos := thm.getPos? | throwError "thm syntax has no pos"
    let .some endPos := colEq.getTailPos? | throwError "colEq syntax has no pos"
    pure ⟨startPos, endPos⟩
| `(command| $_:declModifiers def%$df $_:declId $_:optDeclSig :=%$colEq $_:term) => do
    let .some startPos := df.getPos? | throwError "df syntax has no pos"
    let .some endPos := colEq.getTailPos? | throwError "colEq syntax has no pos"
    pure ⟨startPos, endPos⟩
| _ => throwError "no match"

elab_rules : command
| `(command| #[problem_setup] $cmd:command) => do
  let .some startPos := cmd.raw.getPos? | throwError "cmd syntax has no pos"
  let .some endPos := cmd.raw.getTailPos? | throwError "cmd syntax has no tail pos"
  let mod := (←getEnv).header.mainModule
  let src := (←read).fileMap.source
  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod, s!"{Substring.mk src startPos endPos}"⟩

--  for some weird reason, this alternate way of updating the state fails
--  to persist the data:
--  let st := ext.getState env
--  let st' := st.push ⟨filename, startPos, endPos⟩
--  setEnv (ext.setState env st')

  Lean.Elab.Command.elabCommand cmd

elab_rules : command
| `(command| #[solution_data] $cmd:command) => do
  let ⟨startPos, endPos⟩ ← matchDecl cmd
  let mod := (←getEnv).header.mainModule
  let src := (←read).fileMap.source
  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod,
    s!"/- #[solution_data] -/\n{Substring.mk src startPos endPos} sorry"⟩
  Lean.Elab.Command.elabCommand cmd

syntax (name := showExtraction) "#show_problem_extraction" : command

elab_rules : command
| `(command| #show_problem_extraction) => do
  let ext := problemExtractionExtension
  let env ← getEnv
  let st := ext.getState env
  IO.println s!"st.size = {st.size}"
  for ⟨filename, _⟩ in st do
     IO.println s!"{filename}"

/--
Indicates that a theorem is a problem statement. During problem extraction,
the proof is replaced by a `sorry`.
-/
syntax (name := problem) declModifiers "problem " declId ppIndent(declSig) declVal : command

elab_rules : command
| `(command| $dm:declModifiers problem $di:declId $ds:declSig $dv:declVal) => do
  let src := (←read).fileMap.source

  let pfx  := match dm.raw.getPos?, dm.raw.getTailPos? with
  | .some dmStartPos, .some dmEndPos => s!"{Substring.mk src dmStartPos dmEndPos}\n"
  | _,_ => ""

  let .some sStartPos := di.raw.getPos? | throwError "di syntax has no pos"
  let .some sEndPos := ds.raw.getTailPos? | throwError "ts syntax has no pos"

  let mod := (←getEnv).header.mainModule

  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod,
    s!"{pfx}theorem {Substring.mk src sStartPos sEndPos} := sorry"⟩
  let cmd ← `(command | $dm:declModifiers theorem $di $ds $dv)
  Lean.Elab.Command.elabCommand cmd
