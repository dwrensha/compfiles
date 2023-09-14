import Std.Data.String.Basic
import Std.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Mathlib.Tactic.LabelAttr
import MathPuzzles.Meta.Attributes
import MathPuzzles.Meta.Frontend
import Lean.Meta.Basic

open Lean Core Elab Command Std.Tactic.Lint

structure PuzzleInfo where
  name : String
  solutionUrl : String
  problemUrl : String
  proved : Bool


def olean_path_to_github_url (path: String) : String :=
  let pfx := "./build/lib/"
  let sfx := ".olean"
  assert!(pfx.isPrefixOf path)
  assert!(sfx.data.isSuffixOf path.data)
  "https://github.com/dwrensha/math-puzzles-in-lean4/blob/main/" ++
    ((path.stripPrefix pfx).stripSuffix sfx) ++ ".lean"

open System in
instance : ToExpr FilePath where
  toTypeExpr := mkConst ``FilePath
  toExpr path := mkApp (mkConst ``FilePath.mk) (toExpr path.1)


elab "compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

def HEADER : String :=
 "<!DOCTYPE html><html><head> <meta name=\"viewport\" content=\"width=device-width\">" ++
 "<title>Math Puzzles in Lean 4</title>" ++
 "</head>"

def getStubDecl (name : Name) (ty : Expr) : MetaM String := do
  let msg ← withoutModifyingEnv <| withoutModifyingState do
    let sig ← addMessageContext <| MessageData.ofPPFormat { pp := fun
                | some ctx => ctx.runMetaM <| PrettyPrinter.ppSignature name
                | none     => unreachable!
              }
    let cmd := if ← Meta.isProp ty then "theorem" else "def"
    m!"{cmd} {sig} := sorry\n".toString
  pure msg

def matchDecl : Syntax → CoreM (String.Pos × String.Pos)
| `(command| $_:declModifiers theorem%$thm $_:declId $_:declSig :=%$colEq $_:term) => do
    let .some startPos := thm.getPos? | throwError "thm syntax has no pos"
    let .some endPos := colEq.getTailPos? | throwError "colEq syntax has no pos"
    pure ⟨startPos, endPos⟩
| `(command| $_:declModifiers def%$df $_:declId $_:optDeclSig :=%$colEq $_:term) => do
    let .some startPos := df.getPos? | throwError "df syntax has no pos"
    let .some endPos := colEq.getTailPos? | throwError "colEq syntax has no pos"
    pure ⟨startPos, endPos⟩
| _ => throwError "no match"

def matchProblemSetup (stx: Syntax) : CoreM (String.Pos × String.Pos) := do
  let .some endPos := stx.getTailPos? | throwError "no end pos"
  match stx with
  | `(command| $_:declModifiers abbrev%$ab $_:ident $_:declVal) => do
      let .some startPos := ab.getPos? | throwError "ab syntax has no pos"
      pure ⟨startPos, endPos⟩
  | `(command| $_:declModifiers def%$df $_:declId $_:optDeclSig $_:declVal) => do
      let .some startPos := df.getPos? | throwError "df syntax has no pos"
      pure ⟨startPos, endPos⟩
  | `(command| $_:declModifiers structure%$st $_:declId $[$ids:bracketedBinder]* where
               $[$_:structCtor]? $_:structFields) => do
      let .some startPos := st.getPos? | throwError "st syntax has no pos"
      pure ⟨startPos, endPos⟩
  | `(command| $_:declModifiers inductive%$st $_:declId $_:optDeclSig where
               $[$_:ctor]* $[$_:computedFields]? $_:optDeriving) => do
      let .some startPos := st.getPos? | throwError "st syntax has no pos"
      pure ⟨startPos, endPos⟩

  | _ => throwError "no match"


unsafe def main (_args : List String) : IO Unit := do
  IO.println "hello world"
  IO.FS.createDirAll "_site"
  IO.FS.createDirAll "_site/problems"

  let module := `MathPuzzles
  searchPathRef.set compileTimeSearchPath

  withImportModules [{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let ⟨problem_statements,_⟩ ←
        Lean.Meta.MetaM.run (Mathlib.Tactic.LabelAttr.labelled `problem_statement)
      IO.println f!"problem statements: {problem_statements}"
      let ⟨problem_setups,_⟩ ←
        Lean.Meta.MetaM.run (Mathlib.Tactic.LabelAttr.labelled `problem_setup)
      IO.println f!"problem setups: {problem_setups}"
      let ⟨solution_datas,_⟩ ←
        Lean.Meta.MetaM.run (Mathlib.Tactic.LabelAttr.labelled `solution_data)
      IO.println f!"solution_datas: {solution_datas}"

      let mut infos : List PuzzleInfo := []
      let pkg := `MathPuzzles
      let modules := env.header.moduleNames.filter (pkg.isPrefixOf ·)
      let baseurl := ((← IO.getEnv "GITHUB_PAGES_BASEURL").getD "")

      for m in modules do
        if m ≠ pkg && m ≠ `MathPuzzles.Meta.Attributes then do
          let p ← findOLean m
          let src ← Lean.Elab.IO.moduleSource m
          let solutionUrl := olean_path_to_github_url p.toString
          IO.println s!"MODULE: {m}"
          let steps ← Lean.Elab.IO.compileModule m
          IO.println f!"number of steps = {steps.length}"
          let problem_file := s!"problems/{m}.lean"
          let problemUrl := s!"{baseurl}{problem_file}"
          let h ← IO.FS.Handle.mk ("_site/" ++ problem_file) IO.FS.Mode.write
          match steps with
          | s :: _ =>
            for im in s.before.header.imports do
              if im.module ≠ "Init" && im.module ≠ `MathPuzzles.Meta.Attributes
              then h.putStrLn s!"import {im}"
            h.putStrLn ""
          | [] => pure ()
          for s in steps do
             let csrc : String ← match s.stx.getPos?, s.stx.getTailPos? with
             | .some pos, .some tailPos =>
                pure s!"{(Substring.mk src pos tailPos).toString}\n"
             | _, _ => throwError "failed to get source positions"
             if s.diff.length = 0
             then
               if "/-!".isPrefixOf csrc
               then h.putStrLn csrc
               else if "/-".isPrefixOf csrc || "--".isPrefixOf csrc
                    then pure ()
                    else
                      -- this includes things like `variables` and `namespace`
                      h.putStrLn csrc
             else
               for c in s.diff do
                 let name := c.toConstantVal.name

                 if problem_statements.contains name
                 then -- keep the type and replace the body with `sorry`
                      let ⟨startPos, endPos⟩ ← matchDecl s.stx
                      let decl1 := s!"{(Substring.mk src startPos endPos)} sorry\n"
                      h.putStrLn decl1
                 else if problem_setups.contains name
                 then -- keep everything, but strip the attribute
                      let ⟨startPos, endPos⟩ ← matchProblemSetup s.stx
                      let decl1 := s!"{(Substring.mk src startPos endPos)}\n"
                      h.putStrLn decl1
                 else if solution_datas.contains name
                 then -- keep the type and replace the body with `sorry`
                      let ⟨startPos, endPos⟩ ← matchDecl s.stx
                      let decl1 := s!"{(Substring.mk src startPos endPos)} sorry\n"
                      h.putStrLn s!"/- @[solution_data] -/\n{decl1}"
                 pure ()
          h.flush
          let mut proved := true
          let decls ← getDeclsInPackage m
          for d in decls do
            let c ← getConstInfo d
            match c.value? with
            | none => pure ()
            | some v => do
                 if v.hasSorry then proved := false
          infos := ⟨m.toString.stripPrefix "MathPuzzles.",
                    solutionUrl, problemUrl, proved⟩ :: infos
      -- now write the file
      let num_proved := (infos.filter (·.proved)).length
      let commit_sha := ((← IO.getEnv "GITHUB_SHA").getD "GITHUB_SHA_env_var_not_found")
      let commit_url :=
        s!"https://github.com/dwrensha/math-puzzles-in-lean4/commit/{commit_sha}"

      let h ← IO.FS.Handle.mk "_site/index.html" IO.FS.Mode.write
      h.putStr HEADER
      h.putStr "<body>"
      h.putStr $ "<p>This is a dashboard for the " ++
         "<a href=\"https://github.com/dwrensha/math-puzzles-in-lean4\">" ++
         "Math Puzzles in Lean 4</a> repository.</p>"
      h.putStr s!"<p>(Generated by commit <a href=\"{commit_url}\">{commit_sha}</a>.)<p>"
      h.putStr s!"<p>{num_proved} / {infos.length} problems have a complete solution.<p>"
      h.putStr "<ul>"
      for info in infos.reverse do
        h.putStr "<li>"
        h.putStr s!"<a href=\"{info.solutionUrl}\">"
        if info.proved then
          h.putStr "✅  "
        else
          h.putStr "❌  "
        h.putStr "</a>"
        h.putStr s!"<a href=\"{info.problemUrl}\">{info.name}</a>"
        h.putStr "</li>"
      h.putStr "</ul>"
      h.putStr "</body></html>"
      pure ()
