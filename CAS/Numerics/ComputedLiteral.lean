/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.CompactLiteral
public meta import CAS.Numerics.CompactLiteral

/-!
# Natural-number literals computed during elaboration

`computed_nat% t` evaluates the closed natural-number term `t` with compiled code while the
declaration is elaborated and stands for the resulting literal; from `2 ^ 4096` on it stands for
a named auxiliary definition holding the literal, which compiled code reads from a string of
decimal fields ([CompactLiteral](CompactLiteral.lean)). Large tables computed from
certified definitions can so be stored in the build artifacts of one module without being
written into the sources.

## Implementation notes

The elaborator runs `evalNatTerm` inside `withLiteralEnv`, so the compact literals that `t`
reads come from their definitions and not from their digits. Unlike `nat_literal%`, it writes a
value below `2 ^ 4096` as a raw literal in place, without an auxiliary definition, and leaves the
auxiliary definition of a larger value at the default reducibility. Only the evaluation runs
compiled code, and it only proposes the number: the literal is data and establishes no claim,
so an equation between `t` and the literal must be proved, for instance by `cega`, before
consumers rely on it, and the kernel checks that proof.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `computed_nat% t` is the literal value of the closed natural-number term `t`. -/
syntax (name := computedNat) "computed_nat% " term:max : term

/-- Elaborate `computed_nat% t` to the literal value of `t`. -/
@[term_elab computedNat]
def elabComputedNat : TermElab := fun stx _ ↦ do
  match stx with
  | `(computed_nat% $term) => do
      let value ← withLiteralEnv (evalNatTerm term)
      if value < 2 ^ compactLiteralBits then return mkRawNatLit value
      mkCompactNatLiteral (← mkAuxDeclName `_computedNat) value
  | _ => throwUnsupportedSyntax

end CAS.Numerics
