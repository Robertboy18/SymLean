module

public import CAS.IncludeStr

/-- `p <+> s` appends `s` to the path `p`. -/
public def appendPath (p : System.FilePath) (s : String) : System.FilePath :=
  System.FilePath.mk (p.toString ++ s)

@[inherit_doc] infixl:65 " <+> " => appendPath

public def operator : String := include_str "data" <+> ".txt"
