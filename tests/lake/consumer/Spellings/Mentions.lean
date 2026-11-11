module

public import CAS.IncludeStr

/-!
Mentions of `include_str` outside code. The search tracks the one in this comment,
include_str "comment.txt", and the one in the line comment below, which only adds a file that
does not exist; the module still builds.
-/

-- include_str "line-comment.txt"

/-- A string that mentions the keyword before an escaped quote, which the search does not take
for a path. -/
public def mention : String := "include_str \"string.txt\""

/-- Quotes in an interpolated string, the one alone escaped. -/
public def quotes : String := s!"{'\"'} {"a" ++ "b"}"
