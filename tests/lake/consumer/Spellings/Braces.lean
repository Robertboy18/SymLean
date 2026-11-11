module

public import CAS.IncludeStr

/-! Plain strings with braces, which Lean does not read as interpolated strings. -/

/-- Whether `s` starts with an opening brace. -/
public def check (s : String) : Except String Unit :=
  if s.startsWith "{" then .ok () else .error "expected {"

/-- The text of `payload.txt`. -/
public def payload : String := include_str "data/payload.txt"

/-- Whether `s` ends with a closing brace. -/
public def closed (s : String) : Bool := s.endsWith "}"

/-- An opening brace. -/
public def lb : String := "{"

/-- The text of `between.txt`, between two strings with one brace each. -/
public def between : String := include_str "data/between.txt"

/-- A closing brace. -/
public def rb : String := "}"

/-- A plain string that holds the keyword in braces. -/
public def keyword : String := "{include_str}"
