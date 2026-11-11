module

public import CAS.IncludeStr

/-- A coercion that makes a string a function to paths, so that Lean reads `"data" do pure ()`
as a path. -/
public instance : CoeFun String (fun _ ↦ Id Unit → System.FilePath) where
  coe s := fun _ ↦ System.FilePath.mk (s ++ ".txt")

public def coerced : String := include_str "data" do pure ()
