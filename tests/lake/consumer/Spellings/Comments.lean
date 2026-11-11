module

public import CAS.IncludeStr

/-!
Comments whose opening marks run into their text: a block comment and a doc comment whose texts
start with a slash.
-/

/-/- the comment ends at the first -/

/-- The text of `slashdash.txt`, after a block comment whose text starts with a slash. -/
public def slashDash : String := include_str "data/slashdash.txt"

/--/ the docstring of "docSlash, whose text starts with a slash -/
public def docSlash : String := include_str "data/docslash.txt"
