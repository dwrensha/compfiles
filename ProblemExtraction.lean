import Lean.Elab.Command
import Lean.Meta.Basic
import Std.Lean.NameMapAttribute

/-!
Special commands to aid in "problem extraction".

For the math problems that we archive, we aim to include proofs in-line.
Sometimes, however, we want to present the problems without giving away
information about the solutions.
Therefore, we have "problem extraction" -- a means of stripping solutions.

During problem extraction, all declarations are removed
except those that have been tagged with one of the below command wrappers.
-/

namespace ProblemExtraction

open Lean Elab

structure Replacement where
  startPos : String.Pos
  endPos : String.Pos
  newValue : String
deriving Inhabited

inductive EntryVariant where
  /-- full file text and the position where extraction should start-/
  | file : String → String.Pos → EntryVariant

  /-- substring replacement. positions are relative to the full file -/
  | replace : Replacement → EntryVariant

  | snip_begin : String.Pos → EntryVariant
  | snip_end : String.Pos → EntryVariant

/-- An entry in the state of the Problem Extraction environment extension -/
structure Entry where
/-- The module where the entry originated. -/
(module : Name)
/-- Lean code to be included in the extracted problem file. -/
(variant : EntryVariant)

abbrev ExtractionExtension := SimplePersistentEnvExtension Entry (Array Entry)

initialize problemExtractionExtension : ExtractionExtension ←
  registerSimplePersistentEnvExtension {
    name := `problem_extraction'
    addImportedFn := fun arrays =>
      arrays.foldl (init := ∅) fun acc as =>
        as.foldl (init := acc) fun acc' a => acc'.push a
    addEntryFn    := fun s n => s.push n
  }

initialize solutionExtractionExtension : ExtractionExtension ←
  registerSimplePersistentEnvExtension {
    name := `solution_extraction'
    addImportedFn := fun arrays =>
      arrays.foldl (init := ∅) fun acc as =>
        as.foldl (init := acc) fun acc' a => acc'.push a
    addEntryFn    := fun s n => s.push n
  }

abbrev DetermineDeclsExtension := SimplePersistentEnvExtension Name (Array Name)

initialize determineDeclsExtension : DetermineDeclsExtension ←
  registerSimplePersistentEnvExtension {
    name := `determine_decls'
    addImportedFn := fun arrays =>
      arrays.foldl (init := ∅) fun acc as =>
        as.foldl (init := acc) fun acc' a => acc'.push a
    addEntryFn    := fun s n => s.push n
  }

/-- Top-level command to mark that a file should participate in problem extraction.
This should be at the top of the file (after imports); content above it is ignored
during problem extraction (except for imports). -/
syntax (name := problemFile) "problem_file" : command

elab_rules : command
| `(command| problem_file%$tk) => do
  let .some startPos := tk.getTailPos? | throwError "problem_file syntax has no tail pos"
  let src := (←read).fileMap.source
  let startPos := ⟨startPos.byteIdx + 1⟩ -- HACK: add one to consume unwanted newline

  let mod := (←getEnv).header.mainModule
  modifyEnv fun env =>
    problemExtractionExtension.addEntry env ⟨mod, EntryVariant.file src startPos⟩
  modifyEnv fun env =>
    solutionExtractionExtension.addEntry env ⟨mod, EntryVariant.file src startPos⟩

/-- Commands between `snip begin` and `snip end` will be discarded by problem extraction. -/
syntax (name := snipBegin) "snip begin" : command
syntax (name := snipEnd) "snip end" : command

elab_rules : command
| `(command| snip begin%$tk1) => do
  let .some startPos := tk1.getPos? | throwError "snip syntax has no start pos"
  let .some endPos := tk1.getTailPos? | throwError "snip syntax has no tail pos"
  let startPos := ⟨startPos.byteIdx - 1⟩ -- HACK: subtract one to consume unwanted newline

  let mod := (←getEnv).header.mainModule
  let ext := problemExtractionExtension
  modifyEnv fun env => ext.addEntry env ⟨mod, EntryVariant.snip_begin startPos⟩

  modifyEnv fun env => solutionExtractionExtension.addEntry env
    ⟨mod, EntryVariant.replace ⟨startPos, endPos, ""⟩⟩

| `(command| snip end%$tk2) => do
  let .some startPos := tk2.getPos? | throwError "snip syntax has no start pos"
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

  let cmd ← `(command | $dm:declModifiers theorem $di $ds $dv)
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

  let cmd ← `(command | $dm:declModifiers abbrev $di:declId $ds:optDeclSig $dv:declVal)
  Lean.Elab.Command.elabCommand cmd

  match di with
  | `(Lean.Parser.Command.declId | $i:ident) =>
    let name ← Lean.Elab.resolveGlobalConstNoOverloadWithInfo i
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

/--
Helper function for extractProblems.
-/
private def findModuleImports
    {m : Type → Type} [Monad m] [MonadError m] (env : Environment) (md : Name) :
    m (Array Import) := do
  let moduleNames := env.header.moduleNames
  let mut idx := 0
  for m1 in moduleNames do
    if m1 = md
    then return (env.header.moduleData.get! idx).imports
    else idx := 1 + idx
  throwError s!"module {md} not found"

def extractFromExt {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m]
    (ext : ExtractionExtension) : m (NameMap String) := do
  let env ← getEnv
  let st := ext.getState env

  let mut inProgress : NameMap (String × String.Pos × String) := mkNameMap _
  for ⟨module, variant⟩ in st do
    match variant with
    | .file s p =>
        inProgress := inProgress.insert module ⟨s, p, ""⟩
    | .replace ⟨startPos, endPos, s⟩ =>
      match inProgress.find? module with
      | .some ⟨src, cur, acc⟩ =>
         inProgress := inProgress.insert module
            ⟨src, endPos, acc ++ (Substring.mk src cur startPos).toString ++ s⟩
      | .none => pure ()
    | .snip_begin pos =>
      match inProgress.find? module with
      | .some ⟨src, cur, acc⟩ =>
         inProgress := inProgress.insert module
            ⟨src, pos, acc ++ (Substring.mk src cur pos).toString⟩
      | .none => pure ()
    | .snip_end pos =>
      match inProgress.find? module with
      | .some ⟨src, _, acc⟩ =>
         inProgress := inProgress.insert module ⟨src, pos, acc⟩
      | .none => pure ()

  let mut result := mkNameMap _
  for ⟨module, ⟨src, endPos, acc⟩⟩ in inProgress do
    let mut imports := ""
    for im in ← findModuleImports env module do
      if im.module ≠ "Init" && im.module ≠ `ProblemExtraction
      then imports := imports ++ s!"import {im}\n"

    result := result.insert module
      (imports ++ acc ++ (Substring.mk src endPos src.endPos).toString)

  pure result

/--
Using the data in the problem extraction environment extension,
constructs a map from module name to problem source code.
-/
def extractProblems {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (NameMap String) :=
  extractFromExt problemExtractionExtension

/--
Using the data in the solution extraction environment extension,
constructs a map from module name to solution source code.
-/
def extractSolutions {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (NameMap String) :=
  extractFromExt solutionExtractionExtension
