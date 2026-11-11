/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Assumptions
public import CAS.ClosedForm.Canonical -- shake: keep: quoted in `symbolic_eq` syntax

/-!
# Symbolic algebra automation

`symbolic_alg_zero_side` and `symbolic_eq` close goals `expr.eval ρ = 0` and
`lhs.eval ρ = rhs.eval ρ` about verified expressions by computation; an equality is reduced to
the zero test of `lhs - rhs`. They are internal building blocks of the public `cas` tactic, whose
raw symbolic fallback runs them, with its list of definitions to unfold when one is given; they
do not search for routes and report nothing.

## Main definitions

* `symbolic_alg_zero_side`: close `expr.eval ρ = 0`.
* `symbolic_eq`: close `lhs.eval ρ = rhs.eval ρ` by running the zero test on `lhs - rhs`.

The bracketed forms `symbolic_alg_zero_side [defs]` and `symbolic_eq [defs]` first rewrite the
goal with `simp only` and the listed lemmas, such as local definitions to unfold.

## Implementation notes

Each tactic tries three normal forms in turn and certifies the one that reaches literal `0` with
`decide +kernel`, so that the kernel, not the elaborator, evaluates the normalizer and its
rational coefficient arithmetic. The unconditional normalizer `Alg.normalize` comes first and
needs no side conditions (`Alg.eval_eq_zero_of_normalize_eq_zero`,
`Alg.eval_eq_of_normalize_sub_eq_zero`). The fraction normal form `Alg.zeroCheck` comes next: it
clears the denominators outside the arguments of elementary functions, including that of a lone
quotient such as `x / x`, and its `Alg.SideHolds` obligations are left to `symbolic_assumptions`
(`Alg.ZeroCheck.eval_eq_zero_of_expr_eq_zero`, `Alg.ZeroCheck.eval_eq_of_zeroCheck_sub_eq_zero`).
The multivariate canonical form `Alg.canonicalForm` is the last resort
(`Alg.eval_eq_zero_of_canonicalForm_eq_zero`, `Alg.eval_eq_of_canonicalForm_sub_eq_zero`): it
canonicalizes the arguments of the elementary functions bottom-up, so that atoms such as
`exp ((x^2 - y^2)/(x - y))` and `exp (x + y)` are identified under `x - y ≠ 0`, and its
obligations go to `symbolic_assumptions` as well. In every case the kernel only computes a
normal form and compares it with `0`; the proof is the evaluation theorem of that normal form,
so nothing about the gcd search inside `Alg.canonicalForm` has to be proved.
-/

public meta section

namespace CAS

open scoped BigOperators
open Lean Elab Tactic

/-- `symbolic_alg_zero_side` closes a symbolic zero goal `Verified.Expr.eval e ρ = 0` with the
verified normalizers.

The unconditional normalizer is tried first. If it does not reach `0`, the fraction normal form
runs and its denominator obligations are handed to `symbolic_assumptions`, which proves them from
the local context; the multivariate canonical form is tried last in the same way. -/
syntax (name := symbolicAlgZeroSide) "symbolic_alg_zero_side" : tactic

macro_rules
  | `(tactic| symbolic_alg_zero_side) =>
      `(tactic|
        (change Verified.Expr.eval _ _ = 0
         first
           | exact Verified.Expr.Alg.eval_eq_zero_of_normalize_eq_zero _ _ (by decide +kernel)
           | refine Verified.Expr.Alg.ZeroCheck.eval_eq_zero_of_expr_eq_zero _ _ ?_
               (by decide +kernel)
             symbolic_assumptions
           | refine Verified.Expr.Alg.eval_eq_zero_of_canonicalForm_eq_zero _ _ ?_
               (by decide +kernel)
             symbolic_assumptions))

@[inherit_doc symbolicAlgZeroSide, tactic_alt symbolicAlgZeroSide]
syntax "symbolic_alg_zero_side " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| symbolic_alg_zero_side [$defs,*]) =>
      `(tactic|
        ((try simp only [$defs,*])
         symbolic_alg_zero_side))

/-- `symbolic_alg_zero_side [l₁, l₂]` first rewrites the goal with the listed simp lemmas, such as
definitions to unfold, and then runs `symbolic_alg_zero_side`. -/
tactic_extension symbolicAlgZeroSide

/-- `symbolic_eq` closes a symbolic equality goal by running the zero test on `lhs - rhs`.

This is the equality-facing companion to `symbolic_alg_zero_side`: the user states the natural
equality, the unconditional normalizer is tried first, then the fraction normal form and finally
the multivariate canonical form, each with its `symbolic_assumptions`-discharged obligations. -/
syntax (name := symbolicEq) "symbolic_eq" : tactic

macro_rules
  | `(tactic| symbolic_eq) =>
      `(tactic|
        (change Verified.Expr.eval _ _ = Verified.Expr.eval _ _
         first
           | exact Verified.Expr.Alg.eval_eq_of_normalize_sub_eq_zero _ _ _ (by decide +kernel)
           | refine Verified.Expr.Alg.ZeroCheck.eval_eq_of_zeroCheck_sub_eq_zero _ _ _ ?_
               (by decide +kernel)
             symbolic_assumptions
           | refine Verified.Expr.Alg.eval_eq_of_canonicalForm_sub_eq_zero _ _ _ ?_
               (by decide +kernel)
             symbolic_assumptions))

@[inherit_doc symbolicEq, tactic_alt symbolicEq]
syntax "symbolic_eq " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| symbolic_eq [$defs,*]) =>
      `(tactic|
        ((try simp only [$defs,*])
         symbolic_eq))

/-- `symbolic_eq [l₁, l₂]` first rewrites the goal with the listed simp lemmas, such as definitions
to unfold, and then runs `symbolic_eq`. -/
tactic_extension symbolicEq

end CAS
