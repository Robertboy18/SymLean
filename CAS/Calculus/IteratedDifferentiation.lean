/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Euclidean

/-!
# Iterated symbolic differentiation

Applying `Verified.Expr.diff` `n` times to a one-variable expression computes Mathlib's
`iteratedDerivWithin n` on any set with unique derivatives where the symbolic derivatives of
orders below `n` are valid. Nothing here uses interval arithmetic or quadrature, so the exact
modes (Taylor coefficients in `CAS.Calculus.Series`) and the validated numerical backends (the
derivative sign test of `CAS.Calculus.FindRoot`, Simpson's rule in
`CAS.Continuum.Quadrature.BatchSimpson`) work with the same symbolic derivative.

## Main definitions

* `Verified.Expr.iteratedDiff`: the `n`-fold symbolic derivative in one variable.
* `Verified.Expr.univariateEval`: a one-coordinate expression read as a function `ℝ → ℝ`.
* `Verified.Expr.ValidIteratesOn`: validity on a set of the symbolic derivatives of orders
  `0, ..., n - 1`.

## Main results

* `Verified.Expr.hasDerivAt_univariateEval`: at a valid point the first symbolic derivative is
  the derivative of `univariateEval`.
* `Verified.Expr.iteratedDerivWithin_univariateEval_eq`: at a point of a set with unique
  derivatives on which `n` levels are valid, the `n`-th derivative within the set is the value
  of `iteratedDiff 0 n`.
* `Verified.Expr.contDiffOn_univariateEval`: on a set with unique derivatives, validity of
  `n + 1` levels gives `ContDiffOn ℝ n expr.univariateEval s`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Apply the checked symbolic derivative `n` times in one variable. -/
def iteratedDiff {ι : Type*} [DecidableEq ι] (v : ι) :
    ℕ → Verified.Expr ι → Verified.Expr ι
  | 0, expr => expr
  | n + 1, expr => iteratedDiff v n expr |>.diff v

/-- Zero symbolic derivative iterations leave an expression unchanged. -/
@[simp] theorem iteratedDiff_zero {ι : Type*} [DecidableEq ι]
    (v : ι) (expr : Verified.Expr ι) :
    expr.iteratedDiff v 0 = expr :=
  rfl

/-- A successor iteration differentiates the result of the preceding iterations. -/
@[simp] theorem iteratedDiff_succ {ι : Type*} [DecidableEq ι]
    (v : ι) (n : ℕ) (expr : Verified.Expr ι) :
    expr.iteratedDiff v (n + 1) = (expr.iteratedDiff v n).diff v :=
  rfl

/--
Taking one symbolic derivative before iterating is the same as advancing the
iteration count by one.

In this orientation a recursive certificate construction can prove validity of the
original expression and then recurse on its first derivative.
-/
theorem diff_iteratedDiff {ι : Type*} [DecidableEq ι]
    (v : ι) (n : ℕ) (expr : Verified.Expr ι) :
    (expr.diff v).iteratedDiff v n = expr.iteratedDiff v (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (·.diff v) ih

/-- Interpret a one-coordinate symbolic expression as an ordinary real function. -/
noncomputable def univariateEval (expr : Verified.Expr (Fin 1)) (x : ℝ) : ℝ :=
  expr.eval !₂[x]

/--
A one-variable expression that does not mention its sole variable has the same
value at every input.
-/
theorem eval_eq_eval_zero_of_not_containsVar (expr : Verified.Expr (Fin 1))
    (h : Verified.Expr.containsVar (0 : Fin 1) expr = false) (x : ℝ) :
    expr.eval (!₂[x]) = expr.eval (!₂[(0 : ℝ)]) := by
  convert eval_eq_eval_update_of_not_containsVar (!₂[(0 : ℝ)] : Fin 1 → ℝ) 0 expr h x using 2
  funext i
  fin_cases i
  simp

/--
Validity of every intermediate symbolic derivative on a specified real
domain. This is the local form needed for functions that may have singularities
away from the interval under study.

The condition stops at `k < n`: computing derivative `n` needs validity of
the expressions at levels `0, ..., n - 1`, but not of the final value itself.
-/
def ValidIteratesOn (expr : Verified.Expr (Fin 1)) (n : ℕ) (s : Set ℝ) : Prop :=
  ∀ k < n, ∀ x ∈ s,
    (expr.iteratedDiff (0 : Fin 1) k).ValidAt !₂[x]

/-- Validity through more derivative levels implies validity through fewer levels. -/
theorem ValidIteratesOn.mono {expr : Verified.Expr (Fin 1)}
    {m n : ℕ} {s : Set ℝ}
    (hvalid : expr.ValidIteratesOn n s) (hmn : m ≤ n) :
    expr.ValidIteratesOn m s :=
  fun k hk ↦ hvalid k (hk.trans_le hmn)

/-- The verified first symbolic derivative is the ordinary scalar derivative. -/
theorem hasDerivAt_univariateEval (expr : Verified.Expr (Fin 1)) (x : ℝ)
    (hvalid : expr.ValidAt !₂[x]) :
    HasDerivAt expr.univariateEval
      ((expr.diff (0 : Fin 1)).eval !₂[x]) x := by
  have hpoint (y : ℝ) : (0 : ℝ^1) + y • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) = !₂[y] := by
    ext i
    fin_cases i
    simp
  convert hasDerivAt_eval_add_smul_single expr 0 0 x (by simpa only [hpoint] using hvalid) using 1
  · exact funext fun y ↦ by simp [univariateEval, hpoint]
  · rw [hpoint]

/--
Evaluation of the repeated symbolic derivative equals Mathlib's
`iteratedDerivWithin` on any domain where all intermediate expressions are
valid.
-/
theorem iteratedDerivWithin_univariateEval_eq
    (expr : Verified.Expr (Fin 1)) (n : ℕ)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hvalid : expr.ValidIteratesOn n s) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n expr.univariateEval s x =
      (expr.iteratedDiff (0 : Fin 1) n).eval !₂[x] := by
  induction n generalizing x with
  | zero => simp [univariateEval]
  | succ n ih =>
    have hfun : Set.EqOn (iteratedDerivWithin n expr.univariateEval s)
        (univariateEval (expr.iteratedDiff (0 : Fin 1) n)) s :=
      fun y hy ↦ ih (hvalid.mono n.le_succ) hy
    rw [iteratedDerivWithin_succ, derivWithin_congr hfun (hfun hx)]
    exact (hasDerivAt_univariateEval _ x
      (hvalid n n.lt_succ_self x hx)).hasDerivWithinAt.derivWithin (hs x hx)

/--
Validity of the first `n + 1` symbolic derivatives implies that the denoted
one-variable function is `Cⁿ` on a set with unique derivatives.

The additional validity level is used to prove differentiability, hence
continuity, of the `n`-th symbolic derivative; computing a formal derivative
alone would not give smoothness.
-/
theorem contDiffOn_univariateEval
    (expr : Verified.Expr (Fin 1)) (n : ℕ)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hvalid : expr.ValidIteratesOn (n + 1) s) :
    ContDiffOn ℝ n expr.univariateEval s := by
  refine contDiffOn_of_differentiableOn_deriv fun m hm ↦ ?_
  have hmn : m ≤ n := by exact_mod_cast hm
  have hsymbolic : DifferentiableOn ℝ (expr.iteratedDiff (0 : Fin 1) m).univariateEval s :=
    fun x hx ↦ (hasDerivAt_univariateEval _ x
      (hvalid m (Nat.lt_succ_of_le hmn) x hx)).differentiableAt.differentiableWithinAt
  exact hsymbolic.congr fun x hx ↦
    iteratedDerivWithin_univariateEval_eq expr m hs (hvalid.mono (hmn.trans n.le_succ)) hx

end Verified.Expr

end CAS
