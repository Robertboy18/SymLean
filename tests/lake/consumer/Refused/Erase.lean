module

public import CAS.IncludeStr

/-! The check removed: the facet refuses the module, which names it. -/

attribute [-term_elab] CAS.checkIncludeStr

public def erased : String := include_str ("data" ++ ".txt")
