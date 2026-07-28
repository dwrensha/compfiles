module

public import ProblemExtraction.Core
public meta import ProblemExtraction.Core

/-!
Special commands to aid in "problem extraction".

For the math problems that we archive, we aim to include proofs in-line.
Sometimes, however, we want to present the problems without giving away
information about the solutions.
Therefore, we have "problem extraction" -- a means of stripping solutions.

During problem extraction, all declarations are removed
except those that have been tagged with one of the below command wrappers.
-/

public meta section

namespace ProblemExtraction

open Lean Elab

/-- Top-level command to mark that a file should participate in problem extraction.
This should be at the top of the file (after imports); content above it is ignored
during problem extraction (except for imports). -/
syntax (name := problemFile) "problem_file " (term)? : command

def elabProblemFile (tk : Syntax) (md : Option (TSyntax `term)) : Command.CommandElabM Unit := do
  let .some startPos := (match md with
    | .some md => md.raw.getTailPos?
    | .none => tk.getTailPos?) | throwError "problem_file syntax has no tail pos"
  let src := (←read).fileMap.source
  let startPos := ⟨startPos.byteIdx + 1⟩ -- HACK: add one to consume unwanted newline

  let mod := (←getEnv).header.mainModule
  modifyEnv fun env =>
    problemExtractionExtension.addEntry env ⟨mod, EntryVariant.file src startPos⟩
  modifyEnv fun env =>
    solutionExtractionExtension.addEntry env ⟨mod, EntryVariant.file src startPos⟩

  let mut mdv ← match md with
  | some stx => Lean.Elab.Command.liftTermElabM do
    unsafe Lean.Elab.Term.evalTerm ProblemFileMetadata (mkConst ``ProblemFileMetadata) stx
  | .none => pure {}

  let mdv' :=
    if mdv.authors.isEmpty
    then { mdv with authors := parseAuthors src }
    else mdv

  let mdv' := { mdv' with copyrightHeader := parseCopyrightHeader src }

  modifyEnv fun env => problemMetadataExtension.addEntry env ⟨mod, mdv'⟩

elab_rules : command
| `(command| problem_file%$tk) => elabProblemFile tk none
| `(command| problem_file%$tk $md) => elabProblemFile tk md

/-- Starts a group of commands that will be discarded by problem extraction. -/
syntax (name := snipBegin) "snip " &"begin" : command

/-- Ends a group of commands that will be discarded by problem extraction. -/
syntax (name := snipEnd) "snip " &"end" : command

elab_rules : command
| `(command| snip%$tk0 begin%$tk1) => do
  let .some startPos := tk0.getPos? | throwError "snip syntax has no start pos"
  let .some endPos := tk1.getTailPos? | throwError "snip syntax has no tail pos"
  let startPos := ⟨startPos.byteIdx - 1⟩ -- HACK: subtract one to consume unwanted newline

  let mod := (←getEnv).header.mainModule
  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod, EntryVariant.snip_begin startPos⟩

  modifyEnv fun env => solutionExtractionExtension.addEntry env
    ⟨mod, EntryVariant.replace ⟨startPos, endPos, ""⟩⟩

| `(command| snip%$tk1 end%$tk2) => do
  let .some startPos := tk1.getPos? | throwError "snip syntax has no start pos"
  let .some endPos := tk2.getTailPos? | throwError "snip syntax has no end pos"
  let endPos := ⟨endPos.byteIdx + 1⟩ -- HACK: add one to consume unwanted newline

  let mod := (←getEnv).header.mainModule
  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod, EntryVariant.snip_end endPos⟩

  modifyEnv fun env => solutionExtractionExtension.addEntry env
    ⟨mod, EntryVariant.replace ⟨startPos, endPos, ""⟩⟩

/--
A synonym for `theorem`. Indicates that a declaration is a problem statement.
During problem extraction, the proof is replaced by a `sorry`.
-/
syntax (name := problem) declModifiers "problem " declId ppIndent(declSig) declVal : command

elab_rules : command
| `(command| $dm:declModifiers problem%$pb $di:declId $ds:declSig $dv:declVal) => do
  let mod := (←getEnv).header.mainModule

  let (.some pStartPos, .some pEndPos) := (pb.getPos?, pb.getTailPos?)
   | throwError "failed to get problem syntax"

  modifyEnv fun env => problemExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨pStartPos, pEndPos, "theorem"⟩⟩

  modifyEnv fun env => solutionExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨pStartPos, pEndPos, "theorem"⟩⟩

  let (.some vStartPos, .some vEndPos) := (dv.raw.getPos?, dv.raw.getTailPos?)
   | throwError "failed to get declVal syntax"

  modifyEnv fun env => problemExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨vStartPos, vEndPos, ":= sorry"⟩⟩

  let cmd ← `(command | $dm:declModifiers theorem $di:declId $ds:declSig $dv:declVal)
  Lean.Elab.Command.elabCommand cmd

/--
A synonym for `abbrev`. Marks data that is intended to be filled in as part of
a solution. During problem extraction, the body of the decl is replaced by a `sorry`.
During judging, a human will inspect the filled-in body
to see whether it is reasonable.
-/
syntax (name := determine)
  declModifiers "determine " declId ppIndent(optDeclSig) declVal : command

elab_rules : command
| `(command| $dm:declModifiers determine%$dt $di:declId $ds:optDeclSig $dv:declVal) => do
  let mod := (←getEnv).header.mainModule

  let (.some dStartPos, .some dEndPos) := (dt.getPos?, dt.getTailPos?)
   | throwError "failed to get problem syntax"

  modifyEnv fun env => problemExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨dStartPos, dEndPos, "/- determine -/ abbrev"⟩⟩

  modifyEnv fun env => solutionExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨dStartPos, dEndPos, "/- determine -/ abbrev"⟩⟩

  let (.some vStartPos, .some vEndPos) := (dv.raw.getPos?, dv.raw.getTailPos?)
   | throwError "failed to get declVal syntax"

  modifyEnv fun env => problemExtractionExtension.addEntry env ⟨mod,
    EntryVariant.replace ⟨vStartPos, vEndPos, ":= sorry"⟩⟩

  let cmd ← `(command | set_option linter.unusedVariables false in
    $dm:declModifiers abbrev $di:declId $ds:optDeclSig $dv:declVal)
  Lean.Elab.Command.elabCommand cmd

  match di with
  | `(Lean.Parser.Command.declId | $i:ident) =>
    let name ← Lean.resolveGlobalConstNoOverload i
    modifyEnv fun env => determineDeclsExtension.addEntry env name
  | _ => throwError "explicit universes in `determine` are currently unsupported"

/--
Prints the current contents of the Problem Extraction extension.
-/
syntax (name := showExtraction) "#show_problem_extraction" : command

elab_rules : command
| `(command| #show_problem_extraction) => do
  let ext := problemExtractionExtension
  let env ← getEnv
  let st := ext.getState env
  IO.println s!"ProblemExtraction st.size = {st.size}"
  for ⟨filename, _⟩ in st do
     IO.println s!"{filename}"

  let st := determineDeclsExtension.getState env
  IO.println s!"Determine decls:"
  for n in st do
     IO.println s!"{n}"
