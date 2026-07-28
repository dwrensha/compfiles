module

public import Batteries.Data.String.Basic
public import Batteries.Tactic.Lint
public import Lean.Environment
public import Mathlib.Data.String.Defs
public import Lean.Meta.Basic

public import ProblemExtraction

public section

open Lean Core Elab

def olean_path_to_extracted_path (dst_dir : System.FilePath)
    (olean_path : System.FilePath) : IO System.FilePath := do
  let olean_path_components := olean_path.components.dropWhile (· = ".")
  let cwd ← IO.currentDir
  let relative_olean_path_components := olean_path_components.drop (cwd.components.length)
  assert!(relative_olean_path_components.take 5 = [".lake", "build", "lib", "lean", "Compfiles"])
  let sfx : String := ".olean"
  let olean_path' := (System.mkFilePath (relative_olean_path_components.drop 5)).toString
  assert!(sfx.toList.isSuffixOf olean_path'.toList)
  return dst_dir.join ((olean_path'.dropSuffix sfx).toString ++ ".lean")

unsafe def main (_args : List String) : IO Unit := do
  let problem_dir := "_extracted/problems/"
  let solution_dir := "_extracted/solutions/"
  IO.FS.createDirAll problem_dir
  IO.FS.createDirAll solution_dir

  let module := `Compfiles
  initSearchPath (← findSysroot)

  Lean.enableInitializersExecution
  let env ← importModules #[{module}] {} (trustLevel := 1024)
    (leakEnv := true) (loadExts := true) (level := .exported)
  let ctx := {fileName := "", fileMap := default}
  let state := {env}
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let mst ← ProblemExtraction.extractProblems
    for ⟨m, problem_src⟩ in mst do
      let p ← findOLean m
      IO.println s!"MODULE: {m}"
      let extracted_path ← olean_path_to_extracted_path problem_dir p

      -- TODO mkdir if necessary?
      let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
      h.putStr problem_src
      h.flush

    let mst ← ProblemExtraction.extractSolutions
    for ⟨m, src⟩ in mst do
      let p ← findOLean m
      let extracted_path ← olean_path_to_extracted_path solution_dir p

      -- TODO mkdir if necessary?
      let h ← IO.FS.Handle.mk extracted_path IO.FS.Mode.write
      h.putStr src
      h.flush

    pure ()
