module

public import CAS.IncludeStr
public meta import Lean.Elab.Term

/-! The line below has the keyword, a word and a string literal. An elaborator gives the keyword
and the literal their places in it, with the word in the gap between them, which the check refuses:
the facet's search, which skips only whitespace and comments after the keyword, would not find
the path.

    include_str word "data.txt"
-/

open Lean Elab Term in
run_elab do
  let text := (← getFileMap).source
  let anchor := "include_str word " ++ "\"data.txt\""
  let keyStart := (text.splitOn anchor).head!.utf8ByteSize
  let keyStop := keyStart + "include_str".utf8ByteSize
  let start := keyStart + "include_str word ".utf8ByteSize
  let stop := start + "\"data.txt\"".utf8ByteSize
  let none' : Substring.Raw := "".toRawSubstring
  let keyword := Syntax.atom (.original none' ⟨keyStart⟩ ⟨text, ⟨keyStop⟩, ⟨start⟩⟩ ⟨keyStop⟩)
    "include_str"
  let literal := Syntax.node .none strLitKind
    #[Syntax.atom (.original none' ⟨start⟩ none' ⟨stop⟩) "\"data.txt\""]
  let kind := Name.mkStr2 "Lean" ("include" ++ "Str")
  discard <| elabTerm (Syntax.node .none kind #[keyword, literal]) none
