/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

/-!
# The nonvanishing discharger of the arithmetic route

`field_simp` clears a denominator only when it can prove it nonzero. The target and
hypotheses may use different simp normal forms: `dist a b ≠ 0` becomes `a ≠ b`, and
`‖v‖ ≠ 0` becomes `v ≠ 0`. `cas_nonvanishing`, the `field_simp` discharger of the arithmetic
and polynomial-equation routes, recovers the denominator's nonvanishing from either form.

## Implementation notes

We first try `positivity`, `assumption`, and `linarith`; then we split powers, products and
quotients structurally (`pow_ne_zero`, `mul_ne_zero`, `div_ne_zero`), because the denominator
may be `(t * dist a b) ^ n` with a symbolic exponent that `simp` cannot split itself; and on an
atom we finally run `simp_all`, which rewrites the atom's nonvanishing statement into the same
normal form as the hypotheses and closes it from them. The trailing `fail` keeps `simp_all` from
being the last alternative of `first`, so that its partial progress on a goal it cannot close is
rolled back rather than leaked into the enclosing tactic state.

If simplification reaches the recursion limit, the discharger restores the goal and
reports an ordinary failure, allowing `field_simp` to continue without that nonzero fact.
This can happen with an equation whose right-hand side contains its left-hand side.
Heartbeat exhaustion is propagated. The discharger proves nothing that its constituents do not
prove; it only decides where to look.
-/

public meta section

namespace CAS.Tactic

open Lean Elab Tactic

/--
Discharge a nonvanishing side goal `e ≠ 0` from the local context: `positivity`,
`assumption`, `linarith`, structural splitting of powers, products and quotients, and
`simp_all` on atoms. Used as the `field_simp` discharger of the arithmetic and
polynomial-equation routes.
-/
syntax (name := casNonvanishing) "cas_nonvanishing" : tactic

elab_rules : tactic
  | `(tactic| cas_nonvanishing) => do
    let saved ← saveState
    tryCatchRuntimeEx (evalTactic (← `(tactic|
      first
        | positivity
        | assumption
        | linarith
        | (apply pow_ne_zero; cas_nonvanishing)
        | (apply mul_ne_zero <;> cas_nonvanishing)
        | (apply div_ne_zero <;> cas_nonvanishing)
        | (simp_all; done)
        | fail "cas_nonvanishing could not prove the nonvanishing side goal"))) fun error ↦ do
      saved.restore
      if error.isMaxRecDepth then
        throwError "cas_nonvanishing could not prove the nonvanishing side goal"
      throw error

end CAS.Tactic
