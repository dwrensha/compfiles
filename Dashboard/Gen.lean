import Batteries.Tactic.Lint.Frontend
import Lean.Meta.Basic

import Dashboard.Common
import Dashboard.Components.Base
import Dashboard.Contests.Cmo
import Dashboard.Contests.Imo
import Dashboard.Contests.PreCmo
import Dashboard.Contests.Usamo
import Dashboard.Models.Contests
import Dashboard.Pages.All
import Dashboard.Pages.Index
import ProblemExtraction
import SSG.Core

def extractModuleDoc (env : Lean.Environment) (m : Lean.Name) : String :=
  match Lean.getModuleDoc? env m with
  | some mda => String.join (mda.toList.map Lean.ModuleDoc.doc)
  | _ => ""

def collectProblemMeta (env : Lean.Environment)
  (problems : Lean.NameMap String)
  (solutions : Lean.NameMap String)
  (metadatas : Lean.NameMap ProblemExtraction.ProblemFileMetadata)
  : Lean.Core.CoreM <| Lean.NameMap ProblemMeta := do
  let mut result := Lean.mkNameMap _
  for ⟨name, md⟩ in metadatas do
    let ps := problems.get! name
    let ss := solutions.get! name
    let mut proved := true
    let decls ← Batteries.Tactic.Lint.getDeclsInPackage name
    for d in decls do
      let axioms ← Lean.collectAxioms d
      for a in axioms do
        if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound]) then
          proved := false
    result := result.insert name {
      metadata := md
      informal := extractModuleDoc env name
      problemSrc := ps
      solutionSrc := ss
      proved := proved
    }
  return result

-- TODO: split this into collect ⇒ Data ⇒ generate
--  maybe serialize and reuse when no content change
unsafe def generateAll (config : SConfig) : IO (List Page) := do
  let module := `Compfiles
  let mut allPages : List Page := []
  IO.println "Extracting Problems..."
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module}] {} (trustLevel := 1024) #[] True True
  let ctx : Lean.Core.Context := {fileName := "", fileMap := default}
  let state := {env}
  let mut mds ← Prod.fst <$> (Lean.Core.CoreM.toIO · ctx state) do
    pure <| ← collectProblemMeta env
      (← ProblemExtraction.extractProblems)
      (← ProblemExtraction.extractSolutions)
      (← ProblemExtraction.extractMetadata)
  IO.println s!"Extracted {mds.size} Problems."
  let mut tagFormalizedCounts : Array Nat := Array.mk [0, 0, 0, 0, 0]
  let mut tagSolvedCounts : Array Nat := Array.mk [0, 0, 0, 0, 0]
  let mut numProved : Nat := 0
  let mut mdsArray : Array <| Lean.Name × ProblemMeta := Array.mk []
  for ⟨name, md⟩ in mds do
    mdsArray := mdsArray.push ⟨name, md⟩
    for tag in md.metadata.tags do
      tagFormalizedCounts :=
        tagFormalizedCounts.set! tag.toNat (((tagFormalizedCounts[tag.toNat]!)) + 1)
      if md.proved then tagSolvedCounts :=
        tagSolvedCounts.set! tag.toNat (((tagSolvedCounts[tag.toNat]!)) + 1)
      pure ()
    if md.proved then numProved := numProved + 1
    pure ()
  let bucket (s : String) : Nat :=
    if s.startsWith "Compfiles.Imo" then 0
    else if s.startsWith "Compfiles.Usa" then 1
    else 2
  mdsArray := mdsArray.qsort fun n₁ n₂ ↦
    let s₁ := n₁.1.toString
    let s₂ := n₂.1.toString
    let b₁ := bucket s₁
    let b₂ := bucket s₂
    if b₁ ≠ b₂ then b₁ < b₂ else s₁ < s₂
  allPages := (← All.generate config numProved mdsArray) :: allPages
  allPages := allPages ++ (← Imo.genAll config mds)
  allPages := allPages ++ (← Usamo.genAll config mds)
  allPages := allPages ++ (← Cmo.genAll config mds)
  allPages := allPages ++ (← PreCmo.genAll config mds)
  allPages := (← Index.generate config tagFormalizedCounts
    tagSolvedCounts numProved mds) :: allPages
  return allPages
