import Lean
import Lean.Server.InfoUtils
import Std.Lean.Util.Path
import Mathlib.Data.String.Defs

open Lean Elab System

namespace Lean.Elab.TacticInfo

-- We borrow some stuff from
-- https://github.com/semorrison/lean-training-data/blob/master/TrainingData/InfoTree/Basic.lean
-- and
-- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none


/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true


end Lean.Elab.TacticInfo

def visitTacticInfo (tryTacticStx : Syntax) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSubstantive then return ()
  let src := ci.fileMap.source
  let stx := ti.stx
  match stx.getHeadInfo? with
  | .some (.synthetic ..) =>
     -- Not actual concrete syntax the user wrote. Ignore.
    return ()
  | _ =>  pure ()
  let some sp := stx.getPos? | return ()
  let some ep := stx.getTailPos? | return ()
  let s := Substring.mk src sp ep
  println! "{s}"
  for g in ti.goalsBefore do
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := { mctx := mctx })
    --IO.println x
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
                      <| Tactic.run g (Tactic.evalTactic tryTacticStx)
    try
      let ((mvars, _tstate), _mstate) ← dotac.run {} { mctx := mctx }
      let msgs := (← liftM (m := CoreM) get).messages
      if mvars.length == 0
      then
        for msg in msgs.toList do
          println! "msg: {←msg.data.toString}"

      let traceState := (← liftM (m := CoreM) get).traceState
      for t in traceState.traces.toList do
        println! "trace: {←t.msg.toString}"

      pure ()
    catch _e =>
      --println! "caught: {←e.toMessageData.toString}"
      pure ()

    pure ()

  println! "-------------------------"

def visitInfo (tryTacticStx : Syntax) (env : Environment) (ci : ContextInfo)
    (info : Info) (acc : List (IO Unit))
    : List (IO Unit) :=
  match info with
  | .ofTacticInfo ti =>
    (ci.runMetaM default
     (do setEnv env
         try visitTacticInfo tryTacticStx ci ti
         catch e =>
            println! "caught: {←e.toMessageData.toString}")) :: acc
  | _ => acc

def traverseForest (tryTacticStx : Syntax) (steps : List (Environment × InfoState)) : List (IO Unit) :=
  let t := steps.map fun (env, infoState) ↦
    (infoState.trees.toList.map fun t ↦
      (Lean.Elab.InfoTree.foldInfo (visitInfo tryTacticStx env) [] t).reverse)
  t.join.join

partial def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let env := (←get).commandState.env
  let done ← Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env, infoState)]
  else
    return (env, infoState) :: (←processCommands)

def parseTactic (env : Environment) (str : String) : IO Syntax := do
  let inputCtx := Parser.mkInputContext str "<argument>"
  let tokens := Parser.Module.updateTokens (Parser.getTokenTable env)
  let s := Parser.tacticParser.fn.run
              inputCtx {env := env, options := {}} tokens (Parser.mkParserState inputCtx.input)
  match s.errorMsg with
  | some errorMsg =>
    println! "parse error: {errorMsg}"
    panic! "parse error"
  | none =>
    pure (if s.stxStack.isEmpty then .missing else s.stxStack.back)

unsafe def processFile (tac : String) (path : FilePath) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let input ← IO.FS.readFile path
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  let tryTacticStx ← parseTactic env tac

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName path none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  for t in traverseForest tryTacticStx steps do
    try t
    catch e =>
      println! "caught top level: {e}"
  pure ()

def pathOfProbId (probId : String) : IO FilePath := do
  let path := FilePath.mk ("./Compfiles/" ++ probId ++ ".lean")
  let cwd ← IO.currentDir
  pure $ cwd / path

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [tac, probId] => processFile tac (← pathOfProbId probId)
  | _ => throw $ IO.userError "usage: tryTactic TACTIC PROBLEM"

