import Std.Data.String.Basic
import Std.Lean.Util.Path
import Std.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Lean.Meta.Basic

import ProblemExtraction

open Lean Core Elab

def olean_path_to_extracted_path (path : System.FilePath) : System.FilePath :=
  let path := path.toString
  let pfx := "./build/lib/Compfiles/"
  let sfx := ".olean"
  assert!(pfx.isPrefixOf path)
  assert!(sfx.data.isSuffixOf path.data)
  "_extracted/" ++
    ((path.stripPrefix pfx).stripSuffix sfx) ++ ".lean"

unsafe def main (_args : List String) : IO Unit := do
  IO.FS.createDirAll "_extracted"

  let module := `Compfiles
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let mst ← Compfiles.Meta.extractProblems
      for ⟨m, problem_src⟩ in mst do
        let p ← findOLean m
        IO.println s!"MODULE: {m}"
        let extracted_path := olean_path_to_extracted_path p

        -- TODO mkdir if necessary
        let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
        h.putStr problem_src
        h.flush

      pure ()
