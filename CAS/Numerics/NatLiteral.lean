/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.CompactLiteral

/-!
# Natural literals computed during elaboration

`nat_literal% e` evaluates the closed natural-number term `e` during elaboration and returns
its value as a named irreducible auxiliary definition holding one natural literal. The tables
of a certificate can then be written as the definitions that produce them, without a data
file: a packed table `t` is `nat_literal% (packSlots w n f)`, and a finite check of
`slot w i t = f i` identifies the stored entries with their definition. The literal itself
establishes nothing; only that check does.

## Implementation notes

`evalNatTerm` runs `e` inside `withLiteralEnv` with the compiled code of the definitions it
names, so the modules defining them are imported with `meta import`, and the value is stored by
`mkCompactNatLiteral`: compiled code reads a literal of at least `2 ^ 4096` from a string of
decimal fields ([CompactLiteral](CompactLiteral.lean)). We make the definition irreducible, so
elaboration never unfolds it, while kernel checks read it unchanged instead of recomputing the
table in every declaration. Each such literal is kept small enough that one shift is cheap (a
few hundred kilobits), and a table spread over several literals selects one by a balanced
`cond` tree on a natural index, as `json_slot_blocks%` builds ([SlotBlocks](SlotBlocks.lean)),
rather than by `![...]`, whose kernel reduction costs about half a millisecond per lookup.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `nat_literal% e` stores the value of the closed natural-number term `e`. -/
syntax (name := natLiteral) "nat_literal% " term:max : term

/-- Elaborate `nat_literal%`: evaluate the term and return a named irreducible literal. -/
@[term_elab natLiteral] def elabNatLiteral : TermElab := fun stx _ ↦ do
  let `(nat_literal% $term) := stx | throwUnsupportedSyntax
  let value ← withLiteralEnv (evalNatTerm term)
  let name ← mkAuxDeclName `_natLiteral
  let result ← mkCompactNatLiteral name value
  -- The literal stays data during elaboration; kernel and compiled checks read its body.
  setReducibilityStatus name .irreducible
  return result

end CAS.Numerics
