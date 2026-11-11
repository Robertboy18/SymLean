module

public import CAS.IncludeStr

/-- `p then s` appends `s` to the path `p`. -/
public def appendPath (p : System.FilePath) (s : String) : System.FilePath :=
  System.FilePath.mk (p.toString ++ s)

@[inherit_doc] infixl:65 " then " => appendPath

public def joinedByThen : String := include_str "data" then ".txt"
