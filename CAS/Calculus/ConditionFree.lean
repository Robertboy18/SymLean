/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.IteratedDifferentiation

/-!
# Expressions without side conditions

An expression built from numerals, `π`, `e`, the variable, `+`, `-`, `*`, natural powers,
`sin`, `cos` and `exp` has no domain condition (`conditionFree`). Its symbolic derivative is
again of that kind (`conditionFree_diff`), so it is valid with all its derivatives on the whole
line: it is `Cⁿ` for every `n` (`contDiff_of_conditionFree`) and its derivative is the symbolic
one (`deriv_univariateEval_of_conditionFree`). Exponential polynomials are of this kind. The
particular solution that `#cas [dsolve y x]` (`CAS.Command.DSolveOrder`,
`CAS.Command.DSolveRoot`) finds for a forcing made of terms x^k e^(ax) cos(bx) and
x^k e^(ax) sin(bx) is one, and `CAS.Calculus.LinearODEOrder` takes its smoothness and its
derivatives from here.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- No division, logarithm, root, real power or inverse trigonometric function, and nonzero
denominators of rational literals. -/
def conditionFree : Verified.Expr (Fin 1) → Bool
  | .nat _ | .int _ | .pi | .e | .var _ => true
  | .rat _ d => d != 0
  | .add a b | .mul a b | .sub a b => conditionFree a && conditionFree b
  | .neg a | .pow a _ | .sin a | .cos a | .exp a => conditionFree a
  | _ => false

/-- An expression without side conditions (`conditionFree expr = true`) is valid (`ValidAt`) at
every point `ρ`. -/
theorem validAt_of_conditionFree (ρ : Fin 1 → ℝ) :
    ∀ (expr : Verified.Expr (Fin 1)), conditionFree expr = true → expr.ValidAt ρ
  | .nat _, _ | .int _, _ | .pi, _ | .e, _ | .var _, _ => trivial
  | .rat _ d, h => by simpa [conditionFree] using h
  | .add a b, h | .mul a b, h | .sub a b, h => by
      simp only [conditionFree, Bool.and_eq_true] at h
      exact ⟨validAt_of_conditionFree ρ a h.1, validAt_of_conditionFree ρ b h.2⟩
  | .neg a, h | .pow a _, h | .sin a, h | .cos a, h | .exp a, h =>
      validAt_of_conditionFree ρ a h
  | .div _ _, h | .atan _, h | .asin _, h | .acos _, h | .log _, h | .sqrt _, h
  | .rpow _ _, h => by simp [conditionFree] at h

/-- The symbolic derivative `expr.diff 0` of an expression without side conditions has no side
conditions either. -/
theorem conditionFree_diff :
    ∀ (expr : Verified.Expr (Fin 1)), conditionFree expr = true →
      conditionFree (expr.diff 0) = true
  | .nat _, _ | .int _, _ | .rat _ _, _ | .pi, _ | .e, _ => rfl
  | .var i, _ => by
      simp only [diff]
      split_ifs <;> rfl
  | .add a b, h | .sub a b, h | .mul a b, h => by
      simp only [conditionFree, Bool.and_eq_true] at h
      simp [conditionFree, conditionFree_diff a h.1, conditionFree_diff b h.2, h.1, h.2]
  | .neg a, h | .pow a _, h | .sin a, h | .cos a, h | .exp a, h => by
      simp only [conditionFree] at h
      simp [conditionFree, conditionFree_diff a h, h]
  | .div _ _, h | .atan _, h | .asin _, h | .acos _, h | .log _, h | .sqrt _, h
  | .rpow _ _, h => by simp [conditionFree] at h

/-- Every iterated symbolic derivative `expr.iteratedDiff 0 n` of an expression without side
conditions has no side conditions. -/
theorem conditionFree_iteratedDiff {expr : Verified.Expr (Fin 1)}
    (h : conditionFree expr = true) : ∀ n, conditionFree (expr.iteratedDiff 0 n) = true
  | 0 => h
  | n + 1 => conditionFree_diff _ (conditionFree_iteratedDiff h n)

/-- For every `n`, an expression without side conditions satisfies `ValidIteratesOn n s` on every
set `s ⊆ ℝ`: its iterated derivatives of the orders `k < n` are valid at every point of `s`. -/
theorem validIteratesOn_of_conditionFree {expr : Verified.Expr (Fin 1)}
    (h : conditionFree expr = true) (n : ℕ) (s : Set ℝ) : expr.ValidIteratesOn n s :=
  fun k _ _ _ ↦ validAt_of_conditionFree _ _ (conditionFree_iteratedDiff h k)

/-- An expression without side conditions is `Cⁿ` for every `n`. -/
theorem contDiff_of_conditionFree {expr : Verified.Expr (Fin 1)}
    (h : conditionFree expr = true) (n : ℕ) : ContDiff ℝ n expr.univariateEval :=
  contDiffOn_univ.mp
    (contDiffOn_univariateEval expr n uniqueDiffOn_univ
      (validIteratesOn_of_conditionFree h (n + 1) _))

/-- The derivative of an expression without side conditions is its symbolic derivative. -/
theorem deriv_univariateEval_of_conditionFree {expr : Verified.Expr (Fin 1)}
    (h : conditionFree expr = true) :
    deriv expr.univariateEval = (expr.diff 0).univariateEval :=
  funext fun x ↦ (hasDerivAt_univariateEval expr x (validAt_of_conditionFree _ _ h)).deriv

end CAS.Verified.Expr
