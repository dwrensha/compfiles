import Std.Data.String.Basic
import Std.Lean.Util.Path
import Std.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import MathPuzzles.Meta.ProblemExtraction
import Lean.Meta.Basic

open Lean Core Elab

def olean_path_to_extracted_path (path: String) : String :=
  let pfx := "./build/lib/MathPuzzles/"
  let sfx := ".olean"
  assert!(pfx.isPrefixOf path)
  assert!(sfx.data.isSuffixOf path.data)
  "_extracted/" ++
    ((path.stripPrefix pfx).stripSuffix sfx) ++ ".lean"

unsafe def main (_args : List String) : IO Unit := do
  IO.FS.createDirAll "_extracted"

  let module := `MathPuzzles
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let mst ← MathPuzzles.Meta.extractProblems

      let pkg := `MathPuzzles
      let modules := env.header.moduleNames.filter (pkg.isPrefixOf ·)

      for m in modules do
        if m ≠ pkg && m ≠ `MathPuzzles.Meta.ProblemExtraction then do
          let p ← findOLean m
          IO.println s!"MODULE: {m}"
          let extracted_path := olean_path_to_extracted_path p.toString

          match mst.find? m with
          | .some problem_src => do
            -- TODO mkdir if necessary
            let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
            h.putStrLn problem_src
            h.flush
          | .none => pure ()

      pure ()
