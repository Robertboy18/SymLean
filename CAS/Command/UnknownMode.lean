/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Data.EditDistance
public meta import CAS.Command.FunctionTable

/-!
# Unknown `#cas` modes

`#cas [Simplify] x` names no mode, since the mode is `simplify`. The form
`casUnknownModeCommand` takes a bracket whose first word is no mode word of a `#cas` form in
scope and reports the mode words nearest to it, where Lean's parser would list every mode word.
A word that names a function of the call table, such as `gamma` in `#cas [gamma] (5/2)`, gets the
commands that evaluate the function instead.

## Implementation notes

The mode words are read off the parser itself, as the tokens that parsing `#cas [` expects
(`modeWords`), so every `#cas` form in scope contributes its words and there is no list to keep
in step with the modes. A mode word is refused at its own position (`unknownModeWord`), so the
forms that know it keep their own parse errors. The nearest words are those at the least edit
distance, ignoring case, at most five (`nearestWords`); the distance is the Levenshtein distance
of Lean core (`EditDistance.levenshtein`).
-/

public meta section

namespace CAS.Command.UnknownMode

open Lean Parser Elab Command PrettyPrinter Syntax.MonadTraverser

/-- The mode words of the `#cas` forms of `env`: the tokens that parsing `#cas [` expects. -/
def modeWords (env : Environment) : Array String := Id.run do
  let input := "#cas ["
  let s := (andthenFn whitespace (categoryParserFnImpl `command)).run
    (mkInputContext input "<input>") { env, options := {} } (getTokenTable env)
    (mkParserState input)
  let some error := s.errorMsg | return #[]
  let mut words := #[]
  for expected in error.expected do
    let chars := expected.toList
    unless chars.head? = some '\'' ∧ chars.getLast? = some '\'' do continue
    let word := chars.drop 1 |>.dropLast
    unless word.head?.any Char.isAlpha ∧ word.all (fun c ↦ c.isAlphanum ∨ c = '_') do continue
    let word := String.ofList word
    unless words.contains word do words := words.push word
  return words

/-- An identifier that is no mode word of a `#cas` form; a mode word fails at its position. -/
def unknownModeWord : Parser where
  info := identNoAntiquot.info
  fn c s :=
    let startPos := s.pos
    let s := identFn c s
    if s.hasError then s else
    match s.stxStack.back with
    | .ident _ rawVal _ _ =>
        if (modeWords c.env).contains rawVal.toString then
          s.mkUnexpectedTokenError "a word that is no mode word" startPos
        else s
    | _ => s

private partial def bracketTokensLoop (c : ParserContext) (commandColumn depth : Nat)
    (s : ParserState) : ParserState :=
  let pos := s.pos
  if c.atEnd pos ∨ (c.fileMap.toPosition pos).column ≤ commandColumn then s else
  let size := s.stackSize
  let next := tokenFn [] c s
  if next.hasError then next.restore size pos else
  match next.stxStack.back with
  | .atom _ "]" =>
      if depth = 0 then next.restore size pos
      else bracketTokensLoop c commandColumn (depth - 1) next
  | .atom _ token =>
      bracketTokensLoop c commandColumn (if token.endsWith "[" then depth + 1 else depth) next
  | _ => bracketTokensLoop c commandColumn depth next

/--
The tokens of a mode bracket after its word, up to the `]` that closes the bracket, which stays
unread. A token that is not to the right of the column of the command ends them.
-/
def bracketTokens : Parser where
  fn c s :=
    let size := s.stackSize
    let commandColumn := (c.savedPos?.map fun pos ↦ (c.fileMap.toPosition pos).column).getD 0
    (bracketTokensLoop c commandColumn 0 s).mkNode nullKind size

/-- The formatter of `unknownModeWord`: the identifier formatter `identNoAntiquot.formatter`. -/
@[combinator_formatter unknownModeWord]
def unknownModeWord.formatter : Formatter := Formatter.identNoAntiquot.formatter

/-- The parenthesizer of `unknownModeWord`: the identifier parenthesizer
`identNoAntiquot.parenthesizer`. -/
@[combinator_parenthesizer unknownModeWord]
def unknownModeWord.parenthesizer : Parenthesizer := Parenthesizer.identNoAntiquot.parenthesizer

/-- The formatter of `bracketTokens`: each argument of the node is formatted as an identifier when
it is one and as an atom otherwise. -/
@[combinator_formatter bracketTokens]
def bracketTokens.formatter : Formatter := do
  let stx ← getCur
  Formatter.visitArgs <| stx.getArgs.size.forM fun _ _ ↦ do
    if (← getCur).isIdent then Formatter.identNoAntiquot.formatter
    else Formatter.visitAtom .anonymous

/-- The parenthesizer of `bracketTokens`: each argument of the node is visited as a token. -/
@[combinator_parenthesizer bracketTokens]
def bracketTokens.parenthesizer : Parenthesizer := do
  let stx ← getCur
  Parenthesizer.visitArgs <| stx.getArgs.size.forM fun _ _ ↦ Parenthesizer.visitToken

/-- The words of `words` nearest to `word` in edit distance, ignoring case, at most five. -/
def nearestWords (word : String) (words : Array String) : Array String := Id.run do
  let key := word.toLower
  let scored := words.map fun candidate ↦
    let cutoff := max key.length candidate.length
    ((EditDistance.levenshtein key candidate.toLower cutoff).getD cutoff, candidate)
  let some best := (scored.map (·.1)).toList.min? | return #[]
  let nearest := ((scored.filter (·.1 = best)).map (·.2)).qsort (· < ·)
  return nearest.extract 0 5

private def listText (items : Array String) : String :=
  match items.toList.reverse with
  | [] => ""
  | [item] => item
  | last :: rest => ", ".intercalate rest.reverse ++ " and " ++ last

/--
A `#cas` bracket whose first word is no mode word, such as `#cas [Simplify] x`; the error names
the nearest mode words, or the commands that evaluate a function of the call table.
-/
syntax (name := casUnknownModeCommand) (priority := low)
  withPosition("#cas" optConfig "[" unknownModeWord bracketTokens ("]")? (colGt term)?) : command

/-- The elaborator of `casUnknownModeCommand`, which always fails. When the bracket word names
functions of the call table (`FunctionTable.named` with `pref := true`), the error lists the
commands that evaluate them, adding `import CASHex.NumberTheory` when one needs it; otherwise the
error names the nearest mode words (`nearestWords`). -/
@[command_elab casUnknownModeCommand]
def elabUnknownMode : CommandElab := fun stx ↦ do
  let word := stx[3]
  let functions := FunctionTable.named word.getId.toString (pref := true)
  unless functions.isEmpty do
    let suffix := if functions.any (·.needsHex) then " with `import CASHex.NumberTheory`" else ""
    throwErrorAt word m!"`{word}` is no mode of `#cas`; write \
      {FunctionTable.orList (functions.flatMap FunctionTable.commands)}{suffix}"
  let nearest := nearestWords word.getId.toString (modeWords (← getEnv))
  let names := listText (nearest.map fun name ↦ s!"`{name}`")
  throwErrorAt word m!"`{word}` is no mode of `#cas`; the nearest \
    {if nearest.size = 1 then "mode is" else "modes are"} {names}"

end CAS.Command.UnknownMode
