import Std.Data.String.Basic
import Std.Lean.Util.Path
import Std.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Lean.Meta.Basic

import ProblemExtraction

open Lean Core Elab

def olean_path_to_extracted_path (dst_dir : System.FilePath)
    (olean_path : System.FilePath) : System.FilePath :=
  let olean_path := olean_path.toString
  let pfx := "./.lake/build/lib/Compfiles/"
  let sfx := ".olean"
  assert!(pfx.isPrefixOf olean_path)
  assert!(sfx.data.isSuffixOf olean_path.data)
  dst_dir.join
    (((olean_path.stripPrefix pfx).stripSuffix sfx) ++ ".lean")

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
