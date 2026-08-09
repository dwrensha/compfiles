module

public import Lean.Elab.Command
public import Lean.Elab.Eval
public import Lean.Meta.Basic
public import Batteries.Data.String.Basic
public import Batteries.Lean.NameMapAttribute
public import Std.Data.Iterators.Combinators
public import Lean

/-!
Core data structures and extraction functions used by the problem-extraction commands.
-/

@[expose] public section

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
    | .Geometry => "Geometry"
    | .Inequality => "Inequality"
    | .Combinatorics => "Combinatorics"
    | .NumberTheory => "Number Theory"
    | .Algebra => "Algebra"

structure ProblemFileMetadata where
  tags : List ProblemTag := []

  --- If the problem formalization was imported from somewhere else,
  --- then this field should contain the URL of that source.
  problemImportedFrom : Option String := .none

  --- If the formalized solution was imported from somewhere else,
  --- then this field should contain the URL of that source.
  solutionImportedFrom : Option String := .none

  -- List of URLs to videos relevant to the solution, for example recordings
  -- of livestreams.
  videos : List String := []

  --- Names of the people who wrote the solution. By default, this
  --- is automatically populated via the file's copyright header.
  authors : List String := []

  --- Everything in the file up to but not including the module header.
  --- This is automatically populated during extraction.
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

def parseAuthors (src : String) : List String :=
  src.split "\n"
    |>.findSome? (·.dropPrefix? "Authors: ")
    |>.map (·.toString.splitToList (· = ','))
    |>.getD []

def parseCopyrightHeader (src : String) : String :=
  src.splitOn "\n"
    |>.takeWhile (fun l => !(l.startsWith "module" || l.startsWith "import" || l.startsWith "public import"))
    |>.map (·.append "\n")
    |> String.join

/--
Helper function for `extractFromExt`.
-/
def findModuleImports
    {m : Type → Type} [Monad m] [MonadError m] (env : Environment) (md : Name) :
    m (Array Import) :=
  match env.getModuleIdx? md with
  | .some idx => return env.header.moduleData[idx]!.imports
  | .none => throwError s!"module {md} not found"

/-- Gets the declarations that originate in modules beneath `package`. -/
def getDeclsInPackage (package : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let decls := env.constants.map₂.toArray
  let modules := env.header.moduleNames.map (package.isPrefixOf ·)
  return decls ++ (env.constants.map₁.filter fun name _ => modules[env.const2ModIdx[name]!]!).toArray |>.map (·.1)

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
            ⟨src, endPos, acc ++ (Substring.Raw.mk src cur startPos).toString ++ s⟩
      | .none => pure ()
    | .snip_begin pos =>
      match inProgress.find? module with
      | .some ⟨src, cur, acc⟩ =>
         inProgress := inProgress.insert module
            ⟨src, pos, acc ++ (Substring.Raw.mk src cur pos).toString⟩
      | .none => pure ()
    | .snip_end pos =>
      match inProgress.find? module with
      | .some ⟨src, _, acc⟩ =>
         inProgress := inProgress.insert module ⟨src, pos, acc⟩
      | .none => pure ()

  let mut result := mkNameMap _
  for ⟨module, ⟨src, endPos, acc⟩⟩ in inProgress do
    let mut header := "module\n\n"
    for im in ← findModuleImports env module do
      if im.module.toString ≠ "Init" && im.module ≠ `ProblemExtraction
      then header := header ++ s!"{im}\n"
    header := header ++ "\npublic section\n\n"

    result := result.insert module
      (header ++ acc ++ (Substring.Raw.mk src endPos src.rawEndPos).toString)

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
