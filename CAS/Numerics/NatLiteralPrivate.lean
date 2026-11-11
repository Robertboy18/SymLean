/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.NatLiteral

/-!
# Natural literals from privately imported definitions

`nat_literal_priv% e` is `nat_literal% e` with `e` elaborated as in a private declaration: `e` may
name definitions of modules imported without `public`. The literal it stores refers to none of
them, so a data module can compute its tables from heavy definitions while its importers load only
the literals.

## Implementation notes

Only the evaluation runs under `withoutExporting`, inside `withLiteralEnv` as for
`nat_literal%`; the definition that receives the value is then added outside it by
`mkCompactNatLiteral` and made irreducible, exactly as `nat_literal%` does. Its body is a closed
literal, so neither the kernel nor compiled code needs the private definitions afterwards, and
nothing relates the literal to `e` until a proof does.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `nat_literal_priv% e` stores the value of the closed natural-number term `e`, elaborated as in
a private declaration. -/
syntax (name := natLiteralPriv) "nat_literal_priv% " term:max : term

/-- Elaborate `nat_literal_priv%`: evaluate the term without exporting and return a named
irreducible literal. -/
@[term_elab natLiteralPriv] def elabNatLiteralPriv : TermElab := fun stx _ ↦ do
  let `(nat_literal_priv% $term) := stx | throwUnsupportedSyntax
  let value ← withoutExporting (withLiteralEnv (evalNatTerm term))
  let name ← mkAuxDeclName `_natLiteral
  let result ← mkCompactNatLiteral name value
  setReducibilityStatus name .irreducible
  return result

end CAS.Numerics
