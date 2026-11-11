module

public import CAS.IncludeStr

/-- A coercion that would turn any string into the path `decoy.txt`: the check reads the file of
the literal itself, so this module embeds `coerced`, as the build tracks. -/
local instance : Coe String System.FilePath where
  coe _ := System.FilePath.mk "decoy.txt"

public def coerced : String := include_str "coerced"
