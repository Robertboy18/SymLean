module

/-- A use of `include_str` in a declaration, which Lean elaborates in this module: a module that
loads this one need not load the check. -/
public def direct : String := include_str "direct.txt"
