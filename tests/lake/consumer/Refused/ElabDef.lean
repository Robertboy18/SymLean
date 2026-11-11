module

public meta import Lean.Elab.Term
public import CAS.IncludeStr

/-! An elaborator that elaborates the `include_str` of a syntax quotation, for `ElabUse.lean`. -/

syntax (name := embedThree) "embedThree! " str : term

open Lean Elab Term in
@[term_elab embedThree] public meta def elabEmbedThree : TermElab := fun stx expected ↦ do
  elabTerm (← `(include_str $(⟨stx[1]⟩))) expected
