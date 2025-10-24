import Lean.Elab.Command
import Lean.Elab.Eval
import Lean.Meta.Basic
import Batteries.Data.String.Basic
import Batteries.Lean.NameMapAttribute
import Lean

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
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  newValue : String
deriving Inhabited

inductive EntryVariant where
  /-- full file text and the position where extraction should start-/
  | file : String → String.Pos.Raw → EntryVariant

  /-- substring replacement. positions are relative to the full file -/
  | replace : Replacement → EntryVariant

  | snip_begin : String.Pos.Raw → EntryVariant
  | snip_end : String.Pos.Raw → EntryVariant

/-- An entry in the state of the Problem Extraction environment extension -/
structure Entry where
/-- The module where the entry originated. -/
(module : Name)
/-- Lean code to be included in the extracted problem file. -/
(variant : EntryVariant)

abbrev ExtractionExtension := SimplePersistentEnvExtension Entry (Array Entry)

initialize problemExtractionExtension : ExtractionExtension ←
  registerSimplePersistentEnvExtension {
    name := `problem_extraction
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

initialize solutionExtractionExtension : ExtractionExtension ←
  registerSimplePersistentEnvExtension {
    name := `solution_extraction
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

abbrev DetermineDeclsExtension := SimplePersistentEnvExtension Name (Array Name)

initialize determineDeclsExtension : DetermineDeclsExtension ←
  registerSimplePersistentEnvExtension {
    name := `determine_decls
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

inductive ProblemTag where
| Algebra : ProblemTag
| NumberTheory : ProblemTag
| Combinatorics : ProblemTag
| Geometry : ProblemTag
| Inequality : ProblemTag
deriving Ord

def ProblemTag.toNat (t : ProblemTag) : Nat := match t with
| .Algebra => 0
| .NumberTheory => 1
| .Combinatorics => 2
| .Geometry => 3
| .Inequality => 4

instance : ToString ProblemTag where
  toString := fun p => match p with
    | .Geometry => "geometry"
    | .Inequality => "inequality"
    | .Combinatorics => "combinatorics"
    | .NumberTheory => "number theory"
    | .Algebra => "algebra"

structure ProblemFileMetadata where
  tags : List ProblemTag := []

  --- If the formalized solution was imported from somewhere else,
  --- then this field should contain the URL of that source.
  importedFrom : Option String := .none

  --- Names of the people who wrote the solution. By default, this
  --- is automatically populated via the file's copyright header.
  authors : List String := []

  --- Names of the people who wrote the solution. This field
  --- is automatically populated via the file's copyright header,
  --- which is assumed to be everything before the first 'import'.
  copyrightHeader : String := ""

structure ProblemMetadataEntry where
  module : Name
  metadata : ProblemFileMetadata

abbrev ProblemMetadataExtension :=
  SimplePersistentEnvExtension ProblemMetadataEntry (Array ProblemMetadataEntry)

initialize problemMetadataExtension : ProblemMetadataExtension ←
  registerSimplePersistentEnvExtension {
    name := `problem_metadata
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

def parseAuthors (src : String) : List String := Id.run do
  let lines := src.splitOn "\n"
  for l in lines do
    if l.startsWith "Authors: "
    then
      return (l.stripPrefix "Authors: ").splitToList (fun c => c = ',')
  return []

def parseCopyrightHeader (src : String) : String := Id.run do
  let lines := src.splitOn "\n"
  let mut result := ""
  for l in lines do
    if l.startsWith "import"
    then break
    else
      result := result ++ l ++ "\n"
  return result

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

  let cmd ← `(command | set_option linter.unusedVariables false in $dm:declModifiers abbrev $di:declId $ds:optDeclSig $dv:declVal)
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
    then return (env.header.moduleData[idx]!).imports
    else idx := 1 + idx
  throwError s!"module {md} not found"

def extractFromExt {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m]
    (ext : ExtractionExtension) : m (NameMap String) := do
  let env ← getEnv
  let st := ext.getState env

  let mut inProgress : NameMap (String × String.Pos.Raw × String) := mkNameMap _
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
      if im.module.toString ≠ "Init" && im.module ≠ `ProblemExtraction
      then imports := imports ++ s!"import {im.module}\n"

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

/--
Using the data in the solution extraction environment extension,
constructs a map from module name to problem metadata
-/
def extractMetadata {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (NameMap ProblemFileMetadata) := do
  let env ← getEnv
  let st := problemMetadataExtension.getState env
  let mut result := mkNameMap _
  for ⟨module, md⟩ in st do
    result := result.insert module md
  return result
