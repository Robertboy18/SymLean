/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Elab.Term

/-!
# Checked `include_str`

The facet `SymLean.embeddedInputs` of `lakefile.lean` tracks the files of `include_str` by a text
search for the keyword followed by a string literal. The elaborator here is what lets that search
find the files that Lean reads. It runs before Lean's and accepts an
`include_str` only when the keyword and its path are the text of the module's file at that place
and the path is one string literal, ordinary or raw, with only whitespace and comments before it.
It then reads the file of that literal, relative to the module's directory, as Lean's elaborator
does, except that the literal is not elaborated as a `System.FilePath`, so that no coercion can
change the path. Any other `include_str` is an error that says what to write: one whose path is
another term, such as `"a" ++ ".json"` or a literal that a notation extends; one that a macro or
notation produces, whose text is not in the module that uses it; and one that code elaborates
against a text other than the module's file, as a command that parses and elaborates a string
does. Outside the language server the text is compared with the module's file on disk; in the
server, whose text need not be saved, it is not, and no build reads it there.

## What the build tracks

Every `include_str` that this elaborator accepts is a literal written right after the keyword in
the module's file, which the search finds. In a library that lists the facet, the facet stops the
build at a module that contains `include_str`, if only in a comment, without loading this module
through its public imports, so that every module that can expand its macros and notations loads
the check too; at a module that loads another module of the workspace whose text can produce
`include_str` elsewhere (in a string, a syntax quotation or a command other than a declaration)
without loading this module; and at a module that has or loads code naming the syntax kind or an
elaborator of `include_str` (`includeStr`, `elabIncludeStr`, `checkIncludeStr`), which could
replace or remove this check. In such a library, a file that Lean reads through `include_str` is
therefore tracked, or the build stops. What stays outside is code that reads a file on purpose by
other means: code that reads it itself, with `IO.FS.readFile` say, builds the syntax of
`include_str` at run time from pieces of text, or elaborates it under a file name and a file map
of its own; and macros from outside the workspace, that is, Lean's own, none of which produces
`include_str`.
-/

public meta section

namespace CAS

open Lean Elab Term

/-- Whether `gap` is whitespace and comments only, as the search of the facet skips them: spaces,
tabs and line breaks, line comments, and block comments, doc comments included, nested, with the
character after the opening dash part of the opening. -/
partial def gapOnly : List Char → Bool
  | [] => true
  | c :: rest =>
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then gapOnly rest
    else match c, rest with
      | '-', '-' :: rest => gapOnly (rest.dropWhile (· != '\n'))
      | '/', '-' :: _ :: rest => (blockEnd rest 1).any gapOnly
      | _, _ => false
where
  /-- The text after the block comment whose opening is `depth` levels deep. -/
  blockEnd : List Char → Nat → Option (List Char)
    | [], _ => none
    | '-' :: '/' :: rest, depth => if depth ≤ 1 then some rest else blockEnd rest (depth - 1)
    | '/' :: '-' :: rest, depth => blockEnd rest (depth + 1)
    | _ :: rest, depth => blockEnd rest depth

/-- The check of `include_str` described in the module docstring: the contents of the file of a
plain string literal written right after the keyword in the current file, and an error for any
other `include_str`. -/
@[term_elab Lean.includeStr]
def checkIncludeStr : TermElab := fun stx _ ↦ do
  let text := (← getFileMap).source
  -- Whether the text of the current file from `start` to `stop` is `value`.
  let written (start stop : String.Pos.Raw) (value : String) : Bool :=
    String.Pos.Raw.extract text start stop == value
  let (inFile, path?) := match stx[0], stx[1] with
    | .atom (.original _ keyStart gap keyStop) keyword, path =>
      let inFile := keyword == "include_str" && written keyStart keyStop keyword &&
        gap.startPos == keyStop
      match path with
      | .node _ kind #[.atom (.original _ start _ stop) literal] =>
        if kind == strLitKind && gap.stopPos == start && written start stop literal &&
            gapOnly (String.Pos.Raw.extract text keyStop start).toList then
          (inFile, Syntax.decodeStrLit literal)
        else (inFile, none)
      | _ => (inFile, none)
    | _, _ => (false, none)
  unless inFile do
    throwError "this include_str comes from a macro or notation, so the build cannot track its \
      file; write include_str \"path\", with a plain string literal, at the use"
  let some path := path?
    | throwError "the path of include_str must be a plain string literal right after the \
        keyword, as in include_str \"data.json\", so that the build can track the file"
  let fileName := (← readThe Core.Context).fileName
  -- The text must be the module's file, so that the facet's search of the file finds this path.
  unless Elab.inServer.get (← getOptions) do
    let onDisk ← try some <$> IO.FS.readFile fileName catch _ => pure none
    unless onDisk.any fun disk ↦ text == disk || text == disk.crlfToLf do
      throwError "this include_str is elaborated against a text other than the file \
        {fileName}, as code that parses and elaborates a string does, so the build cannot track \
        its file; write include_str \"path\" in the module's file"
  let some directory := (System.FilePath.mk fileName).parent
    | throwError "cannot compute parent directory of `{fileName}`"
  return mkStrLit (← IO.FS.readFile (directory / path))

end CAS
