import Lean
import Lean.Server.InfoUtils
import Std.Lean.Util.Path
import Mathlib.Data.String.Defs
import Mathlib.Tactic.LibrarySearch

open Lean Elab System

namespace Lean.Elab.TacticInfo

-- We borrow some stuff from
-- https://github.com/semorrison/lean-training-data/blob/master/TrainingData/InfoTree/Basic.lean

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

def visitTacticInfo (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSubstantive then return ()
  let src := ci.fileMap.source
  let stx := ti.stx
  let some sp := stx.getPos? | return ()
  let some ep := stx.getTailPos? | return ()
  let s := Substring.mk src sp ep
  println! "parent decl : {ci.parentDecl?}"
  let env ← getEnv
  match ci.parentDecl? with
  | some pd => if env.contains pd
               then println! "environment already contains parent!"
  | none => pure ()
  println! "{s}"
  for g in ti.goalsBefore do
    let mctx := ti.mctxBefore
    let doprint : MetaM _ := Meta.ppGoal g
    let x ← doprint.run' (s := { mctx := mctx })
    IO.println x
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
                      <| Tactic.run g (Tactic.evalTactic (←`(tactic| exact?)))
    try
      let ((mvars, _tstate), _mstate) := ←(dotac).run
          {} { mctx := mctx }
      let msgs := (← liftM (m := CoreM) get).messages
      println! "mvars after exact: {mvars.length}"
      for msg in msgs.toList do
        println! "msg: {←msg.data.toString}"
      let _ := (← liftM (m := CoreM) (set { (← liftM (m := CoreM) get) with messages := {}}))

      let traceState := (← liftM (m := CoreM) get).traceState
      for t in traceState.traces.toList do
        println! "trace: {←t.msg.toString}"

      pure ()
    catch e =>
      println! "caught: {←e.toMessageData.toString}"
      pure ()

    pure ()

  println! "-------------------------"

def visitInfo (ci : ContextInfo) (info : Info) (pre : MetaM Unit) : MetaM Unit := do
  pre
  match info with
  | .ofTacticInfo ti =>
    try visitTacticInfo ci ti
    catch e =>
            println! "caught: {←e.toMessageData.toString}"
  | _ => pure ()

def traverseForest (steps : List (Environment × InfoState)) : MetaM Unit := do
  for (env, infoState) in steps do
    setEnv env
    for t in infoState.trees do
      Lean.Elab.InfoTree.foldInfo visitInfo (pure ()) t


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

unsafe def processFile (path : FilePath) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  println! path
  let input ← IO.FS.readFile path
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName path none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _s) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  let options := Options.empty.insert `maxHeartbeats (DataValue.ofNat 0)

  let _ ← (traverseForest steps).toIO
            {fileName := s!"{path}", fileMap := FileMap.ofString input,
             options := options}
            {env := env,
             -- Avoid clashing with saved mvars in the InfoTree.
             -- TODO: extract the NameGenerator processCommands so that we don't
             -- need to pick an arbitrary large number here.
             ngen := {idx := 1000000}
            }
  pure ()

def pathOfProbId (probId : String) : IO FilePath := do
  let path := FilePath.mk ("./Compfiles/" ++ probId ++ ".lean")
  let cwd ← IO.currentDir
  pure $ cwd / path

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [probId] => processFile (← pathOfProbId probId)
  | _ => throw $ IO.userError "Invalid arguments"

