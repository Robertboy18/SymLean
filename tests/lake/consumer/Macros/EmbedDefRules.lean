module

/-! The same command by `syntax` and `macro_rules`. -/

public section

syntax "embedDefRulesForeign " ident str : command

macro_rules
  | `(embedDefRulesForeign $n $p) => `(public def $n : String := include_str $p)

end
