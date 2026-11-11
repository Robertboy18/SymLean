module

public import CAS.IncludeStr

/-- The text of `single.txt`, embedded on one line. -/
public def single : String := include_str "single.txt"
