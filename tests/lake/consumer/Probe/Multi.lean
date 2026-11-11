module

public import CAS.IncludeStr

/-- The text of `multi.txt`, its path on the next line after a comment. -/
public def multi : String := include_str -- the file next to this module
  "multi.txt"
