module

public meta import Lean.Elab.Term
public import CAS.IncludeStr

/-- An elaborator that builds the syntax of `include_str` from its kind, `Lean.includeStr`, which
the facet refuses: code that names the kind can add, replace or remove an elaborator of it. -/
syntax (name := embedFile) "embedFile! " str : term

open Lean Elab Term in
@[term_elab embedFile] public meta def elabEmbedFile : TermElab := fun stx expected ↦
  elabTerm (Syntax.node .none ``Lean.includeStr #[mkAtom "include_str", stx[1]]) expected

public def elaboratedUse : String := embedFile! "data.txt"
