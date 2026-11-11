module

public import CAS.IncludeStr

/-- A notation that expands to `include_str`, refused at its use. -/
notation "embed! " path => include_str path

public def notationUse : String := embed! "data.txt"
