module

public import CAS.IncludeStr

/-- The sum of `a` and `b`, written with a user token that holds a comment mark. -/
public def pm (a b : Nat) : Nat := a + b

@[inherit_doc] infixl:65 " +/- " => pm

public def x : Nat := 1 +/- 2

/-- The text of `plusminus.txt`. -/
public def plusMinus : String := include_str "plusminus.txt"

public def close : String := "-/"
