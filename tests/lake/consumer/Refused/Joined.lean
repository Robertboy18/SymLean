module

public import CAS.IncludeStr

/-- Lean's own spelling of a path in parts, which is not one literal. -/
public def joined : String := include_str "." / "data.txt"
