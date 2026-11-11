/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import Lean
import CAS.Tactic.ProofCarrier

/-! Compile a documentation session, isolate expected failures, and export Lean's own hover data.
This executable is a documentation tool, not an import of the CAS library. -/

open Lean Elab

private partial def headToken : Syntax → String
  | .atom _ value => value
  | .ident _ _ name _ => name.eraseMacroScopes.toString
  | .node _ _ args => args.foldl (fun head arg ↦ if head.isEmpty then headToken arg else head) ""
  | .missing => ""

private def hover (ctx : ContextInfo) (info : Info) : IO (Option Json) := do
  let stx := info.stx
  let some start := stx.getPos? | return none
  let some stop := stx.getTailPos? | return none
  if start >= stop then return none
  let mut text := ""
  let kind ← match info with
    | .ofTermInfo term =>
      -- Identifier ranges keep nested application information from obscuring individual names.
      if !stx.isIdent then return none
      let written := (ctx.fileMap.source.toRawSubstring.extract start stop).toString
      unless written == stx.getId.eraseMacroScopes.toString do return none
      text ← term.runMetaM ctx do
        let type ← Meta.ppExpr (← Meta.inferType term.expr)
        let mut result := s!"{stx.getId} : {type}"
        if let .const name _ := term.expr then
          if let some doc ← findDocString? (← getEnv) name then
            result := result ++ "\n\n" ++ doc
        return result
      pure "term"
    | .ofTacticInfo tactic =>
      let written := (ctx.fileMap.source.toRawSubstring.extract start stop).toString
      let token := headToken stx
      if token.isEmpty || !written.startsWith token then return none
      let before ← ({ ctx with mctx := tactic.mctxBefore } : ContextInfo).ppGoals tactic.goalsBefore
      let after ← ({ ctx with mctx := tactic.mctxAfter } : ContextInfo).ppGoals tactic.goalsAfter
      text := s!"Before\n{before}\n\nAfter\n{after}"
      pure "tactic"
    | .ofFieldInfo field =>
      text ← ctx.runMetaM field.lctx do
        let type ← Meta.ppExpr (← Meta.inferType field.val)
        let doc ← findDocString? (← getEnv) field.fieldName
        return s!"{field.fieldName} : {type}" ++ (doc.map ("\n\n" ++ ·)).getD ""
      pure "term"
    | .ofCommandInfo command =>
      let some doc ← ctx.runCoreM (findDocString? ctx.env command.stx.getKind) | return none
      text := (doc.splitOn "\n\n").head!.trimAscii.toString
      pure "command"
    | _ => return none
  return some <| Json.mkObj [("start", toJson start.byteIdx), ("end", toJson stop.byteIdx),
    ("kind", toJson kind), ("text", toJson text)]

private partial def hovers (tree : InfoTree) (ctx? : Option ContextInfo := none) :
    IO (Array Json) := do
  match tree with
  | .hole _ => return #[]
  | .context ctx tree => hovers tree (ctx.mergeIntoOuter? ctx?)
  | .node info children =>
    let mut result := #[]
    if let some ctx := ctx? then
      -- Partial information from a failing example need not have an inferable type.
      try
        if let some item ← hover ctx info then result := result.push item
      catch _ => pure ()
    for child in children do
      result := result ++ (← hovers child (info.updateContext? ctx?))
    return result

private def names (env : Environment) : NameSet :=
  env.constants.map₂.foldl (init := {}) fun found name _ ↦ found.insert name

private def audit (before : NameSet) (env : Environment) : IO Unit := do
  let added := env.constants.map₂.foldl (init := #[]) fun names name _ ↦
    if before.contains name then names else names.push name
  let ctx : ContextInfo := { env, fileMap := default, ngen := {} }
  let closures ← ctx.runMetaM {} (CAS.Tactic.ProofCarrier.axiomClosures added)
  for name in added, axioms in closures do
    if axioms.contains ``sorryAx then
      throw <| IO.userError s!"documentation declaration {name} depends on sorryAx"

private def compile (cells : Array Json) : Frontend.FrontendM (Array Json × Array Json) := do
  let mut output := #[]
  let mut messages := #[]
  for cell in cells do
    let finish := (cell.getObjValAs? Nat "end").toOption.getD 0
    let expectedError := (cell.getObjValAs? String "mode").toOption == some "error"
    let saved ← Frontend.getCommandState
    let before := names saved.env
    repeat
      let input ← Frontend.getInputContext
      let parser ← Frontend.getParserState
      if (input.fileMap.toPosition parser.pos).line > finish then break
      let done ← Frontend.processCommand
      let state ← Frontend.getCommandState
      for message in state.messages.reportedPlusUnreported do
        messages := messages.push (← message.toJson)
      for tree in state.infoState.trees do
        output := output ++ (← hovers (tree.substitute state.infoState.assignment))
      Frontend.setCommandState { state with messages := {}, infoState := {} }
      if done then break
    let current ← Frontend.getCommandState
    if expectedError then
      -- Restore scopes, attributes, declarations and caches, retaining only diagnostics.
      Frontend.setCommandState { saved with messages := current.messages, infoState := {} }
    else
      audit before current.env
      Frontend.setCommandState { current with infoState := {} }
  return (output, messages)

unsafe def main (args : List String) : IO Unit := do
  let [inputPath, cellsPath, outputPath] := args
    | throw <| IO.userError "usage: CheckPage.lean INPUT CELLS OUTPUT"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile inputPath
  let cells ← IO.ofExcept <| Json.parse (← IO.FS.readFile cellsPath) >>= Json.getArr?
  let context := Parser.mkInputContext input inputPath
  let (header, parserState, messages) ← Parser.parseHeader context
  let options := ({} : Options).setBool `Elab.async false
    |>.setBool `pp.unicode.fun true |>.setBool `autoImplicit false
    |>.setBool `relaxedAutoImplicit false |>.setBool `cega.nativeCertificates false
  let (env, messages) ← processHeader header options messages context
  let state := { (Command.mkState env messages options) with infoState.enabled := true }
  let ((output, messages), _) ← (compile cells).run { inputCtx := context } |>.run
    { commandState := state, parserState, cmdPos := parserState.pos }
  IO.FS.writeFile outputPath <| (Json.mkObj [("messages", toJson messages),
    ("hovers", toJson output)]).compress
