/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Elab.Command
public import Lean.Elab.DeclUtil
public import Lean.Elab.Import
public import Lean.Parser
public import LeanReadme.Extract
public import LeanReadme.Report

set_option linter.missingDocs true
set_option doc.verso true

open Lean Lean.Elab Lean.Elab.Command Lean.Meta Lean.Parser

public section

namespace LeanReadme

/-- The main module name used while elaborating README code. -/
def mainModuleName : Name := `readme

/-- Builds a command elaboration context at a position in the given input. -/
private def mkCommandContext (inputCtx : Parser.InputContext) (pos : String.Pos.Raw) : Command.Context where
  fileName := inputCtx.fileName
  fileMap := inputCtx.fileMap
  cmdPos := pos
  snap? := none
  cancelTk? := none

/-- Runs a {name}`CommandElabM` action against a state, returning the updated state. -/
def runCmd (action : CommandElabM Unit) (ctx : Command.Context) (st : Command.State) :
    IO Command.State := do
  match (← EIO.toIO' ((action ctx).run st)) with
  | .ok (_, st') => return st'
  | .error e =>
    -- Turn an elaboration exception into a logged error in the state.
    let msg : Lean.Message := {
      fileName := ctx.fileName, pos := ctx.fileMap.toPosition ctx.cmdPos,
      severity := .error, data := e.toMessageData
    }
    return { st with messages := st.messages.add msg }

/-- Environment for a header-less Lean file ({lit}`Init` imported). -/
def bareEnv (extraImports : Array Import := #[]) : IO Environment := do
  let imports : Array Import :=
    #[{ module := `Init }, { module := `Init, isMeta := true }] ++ extraImports
  let env ← importModules imports (opts := {}) (loadExts := true) (level := .private)
  return env.setMainModule mainModuleName

/-- Builds the initial command state from the prefix file, or a bare module environment. -/
def initialState (prefixPath : System.FilePath) (extraImports : Array Import := #[]) :
    IO Command.State := do
  unsafe Lean.enableInitializersExecution
  if !(← prefixPath.pathExists) then
    return Command.mkState (← bareEnv extraImports) {} {}
  let src ← IO.FS.readFile prefixPath
  let src := src.crlfToLf
  let inputCtx := mkInputContext src prefixPath.toString (normalizeLineEndings := false)
  let (header, parserState, msgs) ← parseHeader inputCtx
  let imports := HeaderSyntax.imports header ++ extraImports
  let (env, msgs) ← processHeaderCore (HeaderSyntax.startPos header) imports false
    (opts := {}) (messages := msgs) inputCtx (mainModule := mainModuleName)
    (headerStx? := header)
  let mut st := Command.mkState env msgs {}
  -- Run any commands after the header.
  let mut ps := parserState
  while !inputCtx.atEnd ps.pos do
    let scope := st.scopes.head!
    let pmctx : ParserModuleContext := {
      env := st.env, options := scope.opts,
      currNamespace := scope.currNamespace, openDecls := scope.openDecls
    }
    let startPos := ps.pos
    let (cmd, ps', pmsgs) := parseCommand inputCtx pmctx ps st.messages
    st := { st with messages := pmsgs }
    ps := ps'
    if Parser.isTerminalCommand cmd then break
    st ← runCmd (elabCommandTopLevel cmd) (mkCommandContext inputCtx startPos) st
  return st

/-- Severity tallies for a batch of messages: {lit}`(hasError, hasWarning)`. -/
private def tally (msgs : Array Lean.Message) : (Bool × Bool) :=
  msgs.foldl (init := (false, false)) fun (e, w) m =>
    match m.severity with
    | .error => (true, w)
    | .warning => (e, true)
    | .information => (e, w)

private def stopInputCtxAt (inputCtx : Parser.InputContext) (stop : String.Pos.Raw) : Option Parser.InputContext :=
  if h : stop ≤ inputCtx.inputString.rawEndPos then
    some <| Parser.mkInputContext inputCtx.inputString inputCtx.fileName (normalizeLineEndings := false) (endPos := stop) (endPos_valid := h)
  else none

/-- Restricts the input context to a code block's byte range. -/
private def boundedBlockInput (inputCtx : Parser.InputContext) (blk : Block) :
    IO Parser.InputContext := do
  let some boundedCtx := stopInputCtxAt inputCtx blk.stopByte
    | throw <| IO.userError "internal error: block stop byte beyond end of input"
  return boundedCtx

/-- Result of collecting and checking README command-block headers. -/
private structure HeaderScan where
  imports : Array Import := #[]
  firstImportLine? : Option Nat := none
  failed : Bool := false
  output : String := ""

/-- Moves a diagnostic from a block-local input context to its position in the README. -/
private def shiftHeaderMessage (blk : Block) (msg : Lean.Message) : Lean.Message :=
  let shift (pos : Position) := { pos with line := pos.line + blk.fenceLine }
  { msg with pos := shift msg.pos, endPos := msg.endPos.map shift }

/-- Collects imports from checked command blocks and reports malformed headers. -/
private def scanHeaders (inputCtx : Parser.InputContext) (blocks : Array Block) : IO HeaderScan := do
  let mut result : HeaderScan := {}
  for blk in blocks do
    if blk.flags.noCheck then
      continue
    if blk.flags.term then
      continue
    let raw : Substring.Raw := {
      str := inputCtx.inputString, startPos := blk.startByte, stopPos := blk.stopByte
    }
    let blockCtx := mkInputContext raw.toString inputCtx.fileName
      (normalizeLineEndings := false)
    let (header, _, messages) ← parseHeader blockCtx
    if messages.hasErrors then
      let mut output := result.output
      for msg in messages.toArray do
        output := output ++ (← shiftHeaderMessage blk msg |>.toString)
      result := { result with failed := true, output }
      continue
    let imports := HeaderSyntax.imports header (includeInit := false)
    if !imports.isEmpty then
      result := {
        result with
        imports := result.imports ++ imports
        firstImportLine? := result.firstImportLine?.orElse fun _ => some (blk.fenceLine + 1)
      }
  return result

/-- Returns the global byte position immediately after a command block's module header. -/
private def blockHeaderEnd (inputCtx : Parser.InputContext) (blk : Block) :
    IO String.Pos.Raw := do
  let raw : Substring.Raw := {
    str := inputCtx.inputString, startPos := blk.startByte, stopPos := blk.stopByte
  }
  let blockCtx := mkInputContext raw.toString inputCtx.fileName
    (normalizeLineEndings := false)
  let (_, parserState, _) ← parseHeader blockCtx
  return parserState.pos.offsetBy blk.startByte

/--
Parses and elaborates a term block in place, threading the command state; the term does not extend the environment.
-/
private def checkTerm (inputCtx : Parser.InputContext) (blk : Block) (st : Command.State) :
    IO Command.State := do
  let boundedCtx ← boundedBlockInput inputCtx blk
  let p := andthenFn whitespace (categoryParserFnImpl `term)
  let pmctx : ParserModuleContext := { env := st.env, options := {} }
  let s0 : ParserState :=
    { cache := initCacheForInput boundedCtx.inputString, pos := blk.startByte }
  let s := p.run boundedCtx pmctx (getTokenTable st.env) s0
  -- Take the bare parser-error text and its position; Message.toString adds the
  -- position prefix, so the data must not already carry one.
  let err? : Option (String.Pos.Raw × String) :=
    if let some (errPos, _, e) := s.allErrors[0]? then some (errPos, toString e)
    else if boundedCtx.atEnd s.pos then none
    else some (s.pos, "expected end of input")
  match err? with
  | some (errPos, msg) =>
    let m : Lean.Message := {
      fileName := inputCtx.fileName, pos := boundedCtx.fileMap.toPosition errPos,
      severity := .error, data := MessageData.ofFormat (.text msg)
    }
    return { st with messages := st.messages.add m }
  | none =>
    let stx := s.stxStack.back
    runCmd (liftTermElabM (discard <| Term.elabTermAndSynthesize stx none))
      (mkCommandContext boundedCtx blk.startByte) st

/--
Checks that a displayed theorem signature is definitionally equal to an imported declaration.

The signature elaboration follows `Mathlib.Tactic.Recall`, by Mac Malone and Kyle Miller.
-/
private def checkRecalledTheorem (cmd : Syntax) (target? : Option String) :
    CommandElabM Unit := withoutModifyingEnv do
  let decl := cmd[1]
  let declId := decl[1]
  let id := declId[0]
  let declName ← match target? with
    | some target => pure target.toName
    | none => resolveGlobalConstNoOverload id
  addConstInfo id declName
  let info ← getConstInfo declName
  unless (← getEnv).isImportedConst declName do
    throwErrorAt id "recalled declaration '{declName}' is not imported"
  let (binders, typeStx) := expandDeclSig decl[2]
  withScope (fun scope =>
      if target?.isSome then { scope with currNamespace := declName.getPrefix } else scope) do
    runTermElabM fun vars => do
      Term.withAutoBoundImplicit do
        Term.elabBinders binders.getArgs fun xs => do
          let xs ← Term.addAutoBoundImplicits xs none
          let type ← Term.elabType typeStx
          Term.synthesizeSyntheticMVarsNoPostponing
          let type ← mkForallFVars xs type
          let type ← mkForallFVars vars type (usedOnly := true)
          let mvs ← info.levelParams.mapM fun _ => mkFreshLevelMVar
          let expected := info.type.instantiateLevelParams info.levelParams mvs
          unless ← isDefEq expected type do
            throwError "type mismatch for recalled declaration '{declName}'{indentExpr type}\n\
              is not definitionally equal to{indentExpr expected}"

/-- Elaborates the commands of a command code block in place, threading the command state. -/
private def checkCommands (inputCtx : Parser.InputContext) (blk : Block) (st : Command.State) :
    IO Command.State := do
  let boundedCtx ← boundedBlockInput inputCtx blk
  let mut st := st
  let mut ps : ModuleParserState := { pos := ← blockHeaderEnd inputCtx blk }
  repeat
    if boundedCtx.atEnd ps.pos then break
    let scope := st.scopes.head!
    let pmctx : ParserModuleContext := {
      env := st.env, options := scope.opts,
      currNamespace := scope.currNamespace, openDecls := scope.openDecls
    }
    let startPos := ps.pos
    let messagesBeforeParse := st.messages
    let (cmd, ps', pmsgs) := parseCommand boundedCtx pmctx ps st.messages
    let isRecalledTheorem := blk.flags.recall &&
      cmd.isOfKind ``Lean.Parser.Command.declaration &&
      cmd[1].isOfKind ``Lean.Parser.Command.theorem
    st := { st with messages := if isRecalledTheorem then messagesBeforeParse else pmsgs }
    ps := ps'
    if Parser.isTerminalCommand cmd then break
    let action := if isRecalledTheorem then
      checkRecalledTheorem cmd blk.flags.recallTarget?
    else
      elabCommandTopLevel cmd
    st ← runCmd action (mkCommandContext boundedCtx startPos) st
  return st

/-- Applies a block's expected-message flags to the messages produced by that block. -/
private def blockOutcomeFromMessages
    (inputCtx : Parser.InputContext) (blk : Block) (msgs : Array Lean.Message) :
    IO BlockOutcome := do
  let (hasError, hasWarning) := tally msgs
  let mut outcome : BlockOutcome := {}
  -- Gate unexpected messages: render and fail.
  for m in msgs do
    let unexpected :=
      (m.severity == .error && !blk.flags.expectError) ||
      (m.severity == .warning && !blk.flags.expectWarning)
    if unexpected then
      let rendered ← m.toString
      let messages := outcome.messages.push { rendered }
      outcome := { outcome with failed := true, messages }
  -- Gate missing expected messages.
  let mkExpect (what : String) : Message := {
    rendered := s!"{inputCtx.fileName}:{blk.fenceLine}:0: error: expected {what}, but the block elaborated cleanly\n"
  }
  if blk.flags.expectError && !hasError then
    outcome := { outcome with failed := true, messages := outcome.messages.push (mkExpect "an error") }
  if blk.flags.expectWarning && !hasWarning then
    outcome := { outcome with failed := true, messages := outcome.messages.push (mkExpect "a warning") }
  return outcome

/-- Checks a single block, threading command state and applying flag gating. -/
def checkBlock (inputCtx : Parser.InputContext) (blk : Block) (st : Command.State) :
    IO (Command.State × BlockOutcome) := do
  if blk.flags.noCheck then
    return (st, {})
  let before := st.messages.toArray.size
  let st ← if blk.flags.term then checkTerm inputCtx blk st else checkCommands inputCtx blk st
  -- New messages produced by this block.
  let newMsgs := st.messages.toArray.extract before st.messages.toArray.size
  return (st, ← blockOutcomeFromMessages inputCtx blk newMsgs)


/-- Aggregate result of checking one Markdown file. -/
structure FileResult where
  /-- The Markdown file that was checked. -/
  path : System.FilePath
  /-- The number of code blocks checked. -/
  blockCount : Nat := 0
  /-- Whether any block failed. -/
  failed : Bool := false
  /-- The accumulated message and summary text. -/
  output : String := ""
deriving Inhabited

/-- Checks every Lean block in the given file, using the prefix file for the prelude. -/
def checkFile (prefixPath file : System.FilePath) : IO FileResult := do
  let raw ← IO.FS.readFile file
  let src := raw.crlfToLf
  match extract src with
  | .error (.unterminated ln) =>
    return {
      path := file, failed := true,
      output := s!"{file}:{ln}:0: error: unterminated code fence\n"
    }
  | .ok blocks =>
    let inputCtx := mkInputContext src file.toString (normalizeLineEndings := false)
    let header ← scanHeaders inputCtx blocks
    if header.failed then
      return {
        path := file, blockCount := blocks.size, failed := true,
        output := header.output ++ s!"{file}: {blocks.size} code blocks checked, FAILED\n"
      }
    let init : Except IO.Error Command.State ← try
      pure <| .ok (← initialState prefixPath header.imports)
    catch e =>
      pure <| .error e
    if let .error e := init then
      return {
        path := file, blockCount := blocks.size, failed := true,
        output := s!"{file}:{header.firstImportLine?.getD 1}:0: error: {e}\n\
          {file}: {blocks.size} code blocks checked, FAILED\n"
      }
    let .ok st := init | unreachable!
    let mut st := st
    let mut out := ""
    let mut failed := false
    for msg in st.messages.toArray do
      if msg.severity != .information then
        failed := true
      out := out ++ (← msg.toString)
    for blk in blocks do
      let (st', outcome) ← checkBlock inputCtx blk st
      st := st'
      if outcome.failed then failed := true
      for d in outcome.messages do out := out ++ d.rendered
    let summary := s!"{file}: {blocks.size} code blocks checked, {if failed then "FAILED" else "OK"}\n"
    return { path := file, blockCount := blocks.size, failed, output := out ++ summary }
