module

public import CAS.IncludeStr
public meta import Lean.Elab.BuiltinTerm

/-! Lean's own elaborator of `include_str`, registered again after the check, which it would then
precede: the facet refuses the module, which names the syntax kind of `include_str`. -/

public meta section

open Lean Elab Term

@[term_elab Lean.includeStr] def restoreBuiltin : TermElab := elabIncludeStr

end

public def overridden : String := include_str ("data" ++ ".txt")
