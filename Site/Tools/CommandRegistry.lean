/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import Lean

/-!
# The command registry

Print, as JSON, every syntax form of the `command`, `tactic` and `conv`
categories whose first token is `#cas`, `cas`, `cas?`, `cas_nf`, `cega` or
`cega?`, in the environment of the modules named on the command line (`CAS` and
`CAS.Numerics.Tactic`, which `CAS` does not import, by default). Each entry
gives the syntax kind, the category, the module and line that declare it, its
docstring, the tactic it is an alternative form of and the documentation
extensions of a tactic, and the syntax itself, rendered from the parser
description that Lean registered. The forms of the `cegaIntervalBinding`
category, which the numerical modes use for `x in [a, b]`, are listed as well.
`cas` and `cega` take their arguments from the categories `casArgs` and
`cegaArgs`: each is listed as its bare form and, as an alternative form, once
with each production of its category. `cas?` and `cega?`, which take the same
arguments, are listed as declared. The bare form `#cas e` of the command,
whose parser first checks that no mode bracket follows `#cas`, is listed as
`#cas term`.

The registry also lists the call table: the functions that `#cas e` evaluates
as calls, such as `#cas (gamma x)`, which are the declarations whose type is
`CAS.Command.CallableFunction`. Each entry gives the declaration, the name of
the function, its usage, its number of arguments, the forms that accept the
call (`bare` for `#cas e`, `expand` for `#cas [expand] e`, `numeric` for
`#cas [N d] e`), whether it needs `import CASHex.NumberTheory`, the module and
line that declare it, and its docstring. A declaration of that type whose
value is not a structure instance written with literals stops the tool with
an error that names it.

The website checks its reference pages against this registry:
`Site/Tools/build.sh` runs

```
lake env lean --run Site/Tools/CommandRegistry.lean > _out/CommandRegistry.json
```

from the repository root, and `Site/Tools/sitegen.py` fails when a form or a
call has no reference page, or a page names one that the registry lacks.
-/

open Lean

namespace SymLean.Site.Registry

/-- The first tokens of the forms the reference documents. -/
def leadingTokens : List String := ["#cas", "cas", "cas?", "cas_nf", "cega", "cega?"]

/-- The categories searched for those forms, and the helper category of the
numerical modes. -/
def categories : List Name := [`command, `tactic, `conv, `cegaIntervalBinding]

/-- The categories of the arguments of `cas` and `cega`. -/
def argumentCategories : List String := ["casArgs", "cegaArgs"]

/-- One piece of a rendered syntax: a token the user types, or a nonterminal. -/
inductive Piece where
  | token (text : String)
  | nonterminal (text : String)

/-- Whether a parser is the check of the bare form `#cas e` that no mode
bracket follows `#cas`. -/
def isModeBracketCheck : Name → Bool
  | .str _ "notModeBracket" => true
  | _ => false

/-- The pieces of a parser description, in order. Pretty-printing hints,
position checks and the check of the bare form `#cas e` that no mode bracket
follows contribute nothing; repetition and options are rendered in the
notation of Lean's `syntax` command. A nested node of Lean's own syntax, such
as a location or a simp lemma, is rendered by its name. -/
partial def pieces : ParserDescr → Array Piece
  | .const name =>
    match name with
    | `ident => #[.nonterminal "ident"]
    | `num => #[.nonterminal "num"]
    | `str => #[.nonterminal "str"]
    | `scientific => #[.nonterminal "scientific"]
    | name =>
      if (name.toString.startsWith "pp") || name == `colGt || name == `colGe ||
          name == `checkColGt || name == `checkWsBefore || name == `checkNoWsBefore ||
          isModeBracketCheck name then
        #[]
      else #[.nonterminal name.toString]
  | .unary name p =>
    let inner := pieces p
    match name with
    | `optional => #[.token "("] ++ inner ++ #[.token ")?"]
    | `many => #[.token "("] ++ inner ++ #[.token ")*"]
    | `many1 => #[.token "("] ++ inner ++ #[.token ")+"]
    | _ => inner
  | .binary `andthen p q => pieces p ++ pieces q
  | .binary `orelse p q => #[.token "("] ++ pieces p ++ #[.token "<|>"] ++ pieces q ++ #[.token ")"]
  | .binary _ p q => pieces p ++ pieces q
  | .node kind _ p =>
    if kind.getRoot == `Lean then
      #[.nonterminal (match kind with
        | .str _ last => last
        | kind => kind.toString)]
    else pieces p
  | .trailingNode _ _ _ p => pieces p
  | .symbol value => #[.token value.trimAscii.toString]
  | .nonReservedSymbol value _ => #[.token value.trimAscii.toString]
  | .unicodeSymbol value _ _ => #[.token value.trimAscii.toString]
  | .cat name _ => #[.nonterminal name.toString]
  | .parser name =>
    if isModeBracketCheck name then #[]
    else
      #[.nonterminal (match name with
        | .str _ last => last
        | name => name.toString)]
  | .nodeWithAntiquot name kind p =>
    if kind.getRoot == `Lean then #[.nonterminal name] else pieces p
  | .sepBy p sep _ _ =>
    let sep := sep.trimAscii.toString
    if sep == "," then pieces p ++ #[.token ",*"]
    else #[.token "("] ++ pieces p ++ #[.token sep, .token ")*"]
  | .sepBy1 p sep _ _ =>
    let sep := sep.trimAscii.toString
    if sep == "," then pieces p ++ #[.token ",+"]
    else #[.token "("] ++ pieces p ++ #[.token sep, .token ")+"]

/-- The JSON form of a rendered syntax. -/
def piecesJson (ps : Array Piece) : Json :=
  .arr <| ps.map fun
    | .token text => json% {"token": $text}
    | .nonterminal text => json% {"nonterminal": $text}

/-- The first token of a rendered syntax, if it starts with one. -/
def firstToken? (ps : Array Piece) : Option String :=
  match ps[0]? with
  | some (Piece.token text) => some text
  | _ => none

/-- The kinds of one category, sorted by name. -/
def kindsOf (env : Environment) (category : Name) : Array Name :=
  match (Parser.parserExtension.getState env).categories.find? category with
  | some cat =>
    (cat.kinds.foldl (init := #[]) fun acc kind _ ↦ acc.push kind).qsort
      (fun a b ↦ a.toString < b.toString)
  | none => #[]

/-- The pieces of the syntax of `kind`, if it is a syntax kind. -/
unsafe def kindPieces? (env : Environment) (kind : Name) : IO (Option (Array Piece)) := do
  let some info := env.find? kind | return none
  unless info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr do
    return none
  let descr ← match env.evalConst ParserDescr {} kind with
    | .ok descr => pure descr
    | .error err => throw <| IO.userError s!"cannot evaluate the parser of {kind}: {err}"
  -- The top-level node is the form itself.
  return some <| match descr with
    | .node _ _ p | .trailingNode _ _ _ p => pieces p
    | descr => pieces descr

/-- The module that declares `name`, or the empty string if the environment
does not say. -/
def moduleOf (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.moduleNames[idx.toNat]?.map toString).getD ""
  | none => ""

/-- The line that declares `name`, or 0 if the environment does not say. -/
def lineOf (env : Environment) (name : Name) : Nat :=
  match declRangeExt.find? (level := .server) env name with
  | some ranges => ranges.range.pos.line
  | none => 0

/-- The registry entry of the form `ps` declared by `kind`. -/
def entry (env : Environment) (kind : Name) (category : Name) (ps : Array Piece)
    (alternativeOf : String) : IO Json := do
  let doc := (← findSimpleDocString? env kind).getD ""
  let extensions := Parser.Tactic.Doc.getTacticExtensions env kind
  return json% {
    "kind": $(kind.toString),
    "category": $(category.toString),
    "module": $(moduleOf env kind),
    "line": $(lineOf env kind),
    "doc": $doc,
    "alternativeOf": $alternativeOf,
    "extensions": $(extensions.toList),
    "syntax": $(piecesJson ps)
  }

/-- The argument category of a tactic `t (args)?` other than a reporting twin `t?`. -/
def argumentCategory? (ps : Array Piece) : Option String :=
  match ps.toList with
  | [.token head, .token "(", .nonterminal args, .token ")?"] =>
    if argumentCategories.contains args && !head.endsWith "?" then some args else none
  | _ => none

/-- The registry entries of one category. -/
unsafe def entries (env : Environment) (category : Name) : IO (Array Json) := do
  let mut out := #[]
  for kind in kindsOf env category do
    let some ps ← kindPieces? env kind | continue
    let helper := category == `cegaIntervalBinding
    unless helper || (firstToken? ps).any (leadingTokens.contains ·) do continue
    let alternativeOf : String :=
      ((Parser.Tactic.Doc.alternativeOfTactic env kind).map toString).getD ""
    match argumentCategory? ps, ps[0]? with
    | some args, some head =>
      out := out.push (← entry env kind category #[head] alternativeOf)
      for argument in kindsOf env args.toName do
        let some argumentPieces ← kindPieces? env argument | continue
        out := out.push (← entry env argument category (#[head] ++ argumentPieces) kind.toString)
    | _, _ => out := out.push (← entry env kind category ps alternativeOf)
  return out

/-- The functions of the call table, the declarations of type
`CAS.Command.CallableFunction`, sorted by name. -/
def callNames (env : Environment) : Array Name :=
  (env.constants.fold (init := (#[] : Array Name)) fun acc name info ↦
    if !name.isInternalDetail && info.type.isConstOf `CAS.Command.CallableFunction then
      acc.push name
    else acc).qsort (fun a b ↦ a.toString < b.toString)

/-- The string that `e` is, if it is a literal. -/
def stringLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- The natural number that `e` is, if it is a numeral. -/
def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => e.nat?

/-- The forms of a list of `CAS.Command.CallForm` constructors, each by the
last component of its name, if the list is written out. -/
partial def callForms? (e : Expr) : Option (List String) :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    match e.appFn!.appArg!.consumeMData with
    | .const (.str parent form) _ =>
      if parent == `CAS.Command.CallForm then (form :: ·) <$> callForms? e.appArg! else none
    | _ => none
  else none

/-- Stop the tool on the function `decl` of the call table, which the
registry cannot read. -/
def callError {α : Type} (decl : Name) (problem : String) : IO α :=
  throw <| IO.userError s!"the call table entry {decl} {problem}"

/-- The registry entry of the function `decl` of the call table, read from the
arguments of the `CAS.Command.CallableFunction.mk` application its value is. -/
def callEntry (env : Environment) (decl : Name) : IO Json := do
  let some info := env.find? decl | callError decl "is not in the environment"
  let some value := info.value? | callError decl "is not a definition"
  let value := value.consumeMData
  let args := value.getAppArgs
  unless value.getAppFn.isConstOf `CAS.Command.CallableFunction.mk && args.size == 6 do
    callError decl "is not a structure instance of CAS.Command.CallableFunction"
  let some name := stringLit? args[0]! | callError decl "has no literal name"
  let some usage := stringLit? args[1]! | callError decl "has no literal usage"
  let some arity := natLit? args[2]! | callError decl "has no literal arity"
  let some forms := callForms? args[3]! | callError decl "has no literal list of forms"
  let flag := args[4]!.consumeMData
  let needsHex ←
    if flag.isConstOf ``Bool.true then pure true
    else if flag.isConstOf ``Bool.false then pure false
    else callError decl "has no literal needsHex"
  let words := (usage.splitOn " ").filter fun word ↦ !word.isEmpty
  unless words.head? == some name && words.length == arity + 1 do
    callError decl s!"has the usage {usage}, which does not fit its name {name} and arity {arity}"
  let doc := (← findSimpleDocString? env decl).getD ""
  return json% {
    "decl": $(decl.toString),
    "name": $name,
    "usage": $usage,
    "arity": $arity,
    "forms": $forms,
    "needsHex": $needsHex,
    "module": $(moduleOf env decl),
    "line": $(lineOf env decl),
    "doc": $doc
  }

/-- Print the registry of the modules named in `args`. -/
unsafe def run (args : List String) : IO UInt32 := do
  let modules := if args.isEmpty then [`CAS, `CAS.Numerics.Tactic] else args.map String.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })).toArray {} (trustLevel := 1024)
    (loadExts := true)
  let mut all := #[]
  for category in categories do
    all := all ++ (← entries env category)
  let calls ← (callNames env).mapM (callEntry env)
  IO.println <| (json% {
    "modules": $(modules.map toString),
    "forms": $(Json.arr all),
    "calls": $(Json.arr calls)
  }).pretty
  return 0

end SymLean.Site.Registry

/-- See the module documentation. -/
unsafe def main (args : List String) : IO UInt32 :=
  SymLean.Site.Registry.run args
