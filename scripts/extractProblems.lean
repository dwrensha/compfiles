import Batteries.Data.String.Basic
import Batteries.Lean.Util.Path
import Batteries.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Lean.Meta.Basic

import ProblemExtraction

open Lean Core Elab

def olean_path_to_extracted_path (dst_dir : System.FilePath)
    (olean_path : System.FilePath) : System.FilePath :=
  let olean_path_components := olean_path.components.dropWhile (· = ".")
  assert!(olean_path_components.take 4 = [".lake", "build", "lib", "Compfiles"])
  let sfx : String := ".olean"
  let olean_path' := (System.mkFilePath (olean_path_components.drop 4)).toString
  assert!(sfx.data.isSuffixOf olean_path'.data)
  dst_dir.join ((olean_path'.stripSuffix sfx) ++ ".lean")

unsafe def main (_args : List String) : IO Unit := do
  let problem_dir := "_extracted/problems/"
  let solution_dir := "_extracted/solutions/"
  IO.FS.createDirAll problem_dir
  IO.FS.createDirAll solution_dir

  let module := `Compfiles
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do

      let mst ← ProblemExtraction.extractProblems
      for ⟨m, problem_src⟩ in mst do
        let p ← findOLean m
        IO.println s!"MODULE: {m}"
        let extracted_path := olean_path_to_extracted_path problem_dir p

        -- TODO mkdir if necessary?
        let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
        h.putStr problem_src
        h.flush

      let mst ← ProblemExtraction.extractSolutions
      for ⟨m, src⟩ in mst do
        let p ← findOLean m
        let extracted_path := olean_path_to_extracted_path solution_dir p

        -- TODO mkdir if necessary?
        let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
        h.putStr src
        h.flush

      pure ()
