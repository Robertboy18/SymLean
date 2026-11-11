module

public import CAS.IncludeStr

/-! Paths followed by a field of a structure instance or a `where` clause on the next line. -/

public structure Pair where
  x : String
  y : String

public def pair : Pair :=
  { x := include_str "data/struct-x.txt"
    y := include_str "data/struct-y.txt" }

public def pairWhere : Pair where
  x := include_str "data/where-a.txt"
  y := include_str "data/where-b.txt"
