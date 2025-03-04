import Mathlib.Data.String.Defs
import Batteries.Data.String.Basic
import Batteries.Tactic.Lint
import Lean.Environment
import Lean.Elab.Print
import Lean.Meta.Basic
import Lean.Replay

import ProblemExtraction

open Lean Core Elab

def LEAN_PATH : String := "./.lake/packages/batteries/.lake/build/lib:./.lake/packages/Qq/.lake/build/lib:./.lake/packages/aesop/.lake/build/lib:./.lake/packages/proofwidgets/.lake/build/lib:./.lake/packages/importGraph/.lake/build/lib:./.lake/packages/mathlib/.lake/build/lib"

def workDir : System.FilePath := "_check"

def copyFile (src : System.FilePath) (dst : System.FilePath) : IO Unit := do
  IO.FS.writeFile dst (←IO.FS.readFile src)

def compileFile (file : System.FilePath) (outputFile : System.FilePath) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #[file.toString, "-o", outputFile.toString]
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
  }
  let exitCode ← child.wait
  if exitCode != 0
  then panic! s!"compilation failed {exitCode}"
  pure ()

structure CompileProblemResult where
  lean_file : System.FilePath
  olean_file : System.FilePath
  determineDecls : List Name

-- We need to use silly continuation-passing style so that we can continue to
-- refer to names from the module. Otherwise, we get segfaults.
unsafe def compileProblem (problem_id : String) (act : CompileProblemResult → IO Unit)
    : IO Unit := do
  initSearchPath (← findSysroot)

  let lean_file := workDir.join (problem_id ++ ".lean")
  let olean_file := workDir.join (problem_id ++ ".olean")

  let module := `Compfiles
  Lean.enableInitializersExecution
  withImportModules #[{module}] {} (trustLevel := 1024) fun env => do
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let mst ← ProblemExtraction.extractProblems
      let mut found_it : Bool := false
      for ⟨m, problem_src⟩ in mst do
        if m.toString = ("Compfiles." ++ problem_id) then do
          let h ← IO.FS.Handle.mk lean_file IO.FS.Mode.write
          h.putStr problem_src
          h.flush
          found_it := true
      if !found_it
      then panic! s!"no such problem {problem_id}"

    let s := ProblemExtraction.determineDeclsExtension.getState env
    compileFile lean_file olean_file
    act ⟨lean_file, olean_file, s.toList⟩

unsafe def verifyTypesAndAxioms (problem_mod : Name) (solution_mod : Name)
    : IO Unit := do
  searchPathRef.set (workDir :: compile_time_search_path%)

  withImportModules #[{module := problem_mod}] {} (trustLevel := 1024) fun prob_env =>
    withImportModules #[{module := solution_mod}] {} (trustLevel := 1024) fun sol_env => do
      let prob_ctx := {fileName := "", fileMap := default}
      let prob_state := {env := prob_env}
      let prob_infos ← Prod.fst <$> (CoreM.toIO · prob_ctx prob_state) do
        let mut infos : RBMap Name ConstantInfo Name.quickCmp := {}
        let decls ← Batteries.Tactic.Lint.getDeclsInPackage problem_mod
        for d in decls do
          if not d.isInternal then
            infos := infos.insert d (← getConstInfo d)
        pure infos

      let sol_ctx := {fileName := "", fileMap := default}
      let sol_state := {env := sol_env}
      Prod.fst <$> (CoreM.toIO · sol_ctx sol_state) do
        let decls ← Batteries.Tactic.Lint.getDeclsInPackage solution_mod
        let mut prob_infos := prob_infos
        for d in decls do
          if not d.isInternal then
           if let .some prob_const := prob_infos.find? d then
            prob_infos := prob_infos.erase d
            let sol_const ← getConstInfo d
            Lean.Meta.MetaM.run' do
              if not (←Lean.Meta.isDefEq prob_const.type sol_const.type) then
                let te ← Lean.PrettyPrinter.ppExpr prob_const.type
                let ge ← Lean.PrettyPrinter.ppExpr sol_const.type
                throwError s!"{d} not defEq. Expected\n{te},\nbut got\n{ge}."

            for a in ← Lean.collectAxioms d do
               if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound]) then
                 throwError s!"prohibited axiom: {a}"
        for ⟨k, _⟩ in prob_infos do
          throwError s!"no decl found for {k}"
      pure ()
  pure ()

-- copied from lean4checker (https://github.com/leanprover/lean4checker/)
unsafe def replayFromImports (module : Name) : IO Unit := do
  searchPathRef.set (workDir :: compile_time_search_path%)
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports
    |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
  let env ← finalizeImport s #[{module}] {} 0
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions
  region.free

unsafe def printDetermineVals (determineDecls : List Name) (solution_mod : Name)
    : IO Unit := do
  searchPathRef.set (workDir :: compile_time_search_path%)

  withImportModules #[{module := solution_mod}] {} (trustLevel := 1024) fun sol_env => do
    let sol_ctx := {fileName := "", fileMap := default}
    let sol_state := {env := sol_env}
    Prod.fst <$> (CoreM.toIO · sol_ctx sol_state) do
      let decls ← Batteries.Tactic.Lint.getDeclsInPackage solution_mod
      for d in decls do
        if determineDecls.contains d then
          let sol_const ← getConstInfo d
          match sol_const.value? with
          | none => throwError s!"determine {d} has no value"
          | some v =>
              let tm ← Lean.Meta.MetaM.run' do
                  Lean.PrettyPrinter.ppExpr v
              IO.println s!"determine {d} := {tm}"
          pure ()


unsafe def main (args : List String) : IO Unit := do
  if args.length != 2
  then do
    IO.println "usage: checkSolution PROBLEM_ID SOLUTION_FILE"
    IO.Process.exit 1

  let problem_id := args[0]!
  let problem_mod := Name.mkSimple problem_id

  let solution_id := problem_id ++ "_solution"
  let solution_mod := Name.mkSimple solution_id

  IO.FS.createDirAll workDir

  -- 1. extract problem, take note of any `determine`
  -- 2. compile problem to olean

  IO.println "* compiling problem into olean ..."
  compileProblem problem_id fun r => do

  -- 3. compile solution to olean
  --    (need to copy it to ./_check/solution.lean first)

  IO.println "* compiling solution into olean ..."
  let solution_lean_file := workDir.join (solution_id ++ ".lean")
  let solution_olean_file := workDir.join (solution_id ++ ".olean")
  copyFile (args[1]!) solution_lean_file
  compileFile solution_lean_file solution_olean_file

  -- 4. For each decl in problem olean, verify that it
  --    exists in the solution olean, with exactly the same signature,
  --    and that it the solution version does not use any disallowed axioms.
  IO.println "* verifying types and axioms ..."
  verifyTypesAndAxioms problem_mod solution_mod

  -- 5. verify that solution olean does not do environment hacking
  IO.println "* replaying environment ..."
  replayFromImports solution_mod

  -- 6. print any `determine` terms, to be inspected by human judge.
  IO.println "* collecting any 'determine' declarations ..."
  printDetermineVals r.determineDecls solution_mod

  IO.println "* verified!"
