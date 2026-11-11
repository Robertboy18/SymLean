module

import Macros.Restore

/-- A module that loads `Macros.Restore`, which registers an elaborator for the syntax kind
`Lean.includeStr`: the facet refuses it. -/
public def restored : Nat := 0
