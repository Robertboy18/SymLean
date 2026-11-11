module

public import CAS.IncludeStr

/-- A macro that expands to `include_str`, refused at its use. -/
macro "embed! " path:str : term => `(include_str $path)

public def macroUse : String := embed! "data.txt"
