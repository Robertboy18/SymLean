module

public import CAS.IncludeStr

/-- The text of `top.txt`, which `run.sh` writes. -/
public def topData : String := include_str "top.txt"
