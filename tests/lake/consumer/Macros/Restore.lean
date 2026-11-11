module

public meta import Lean.Elab.BuiltinTerm

/-! Lean's elaborator of `include_str`, registered again: a library that tracks its files must not
load this module. -/

public meta section

open Lean Elab Term

@[term_elab Lean.includeStr] def restoreForeign : TermElab := elabIncludeStr

end
