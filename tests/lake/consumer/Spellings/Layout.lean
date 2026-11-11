module

public import CAS.IncludeStr

/-! Paths that end at a keyword on the next line or at a closing parenthesis. -/

/-- The text of `do-block.txt`, read in a `do` block whose next line starts with a keyword. -/
public def doBlock : IO String := do
  let text := include_str "data/do-block.txt"
  return text

/-- The text of `parenthesized.txt`, whose parentheses end the path before the identifier on the
next line. -/
public def parenthesized : IO String := do
  let text := (include_str "data/parenthesized.txt")
  pure text
