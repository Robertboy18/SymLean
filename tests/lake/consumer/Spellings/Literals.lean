module

public import CAS.IncludeStr

/-! Character literals and quotes in interpolated strings before an `include_str`. -/

/-- Character literals with escapes, the quote among them. -/
public def letters : List Char := ['\x41', '\u0041', 'A', '"']

/-- The text of `chars.txt`. -/
public def chars : String := include_str "data/chars.txt"

/-- A quote alone in the braces of an interpolated string. -/
public def quote : String := s!"{'"'}"

/-- The text of `quote.txt`. -/
public def quoted : String := include_str "data/quote.txt"

/-- A string with an escaped quote in the braces of an interpolated string. -/
public def escapedQuote : String := s!"{"\""}"

/-- The text of `escaped-quote.txt`. -/
public def escapedQuoted : String := include_str "data/escaped-quote.txt"
