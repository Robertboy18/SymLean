/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import CAS.Numerics.Tactic
import Mathlib.Tactic.NormNum.Prime

/-!
# Failure messages of `cas` and `cega`

When `cas` or `cega` fails, its message should say what went wrong and what to try, with
settings and calls that parse as written. Each example below pins the part of one message that
says so. The calls the messages suggest are tried as well, where they succeed. The section on the
lemmas of `cas [l₁, l₂]` also proves goals with them, among them reflected equalities that the
reflected route does not prove.
-/

namespace CAS.Examples.Messages

/-! ## Recursion depth

Exhausting Lean's recursion depth is an ordinary failure of every form of `cas` and `cega`, not
Lean's runtime error, which `first` and `try` would not catch; the message gives the option's
value and a larger setting to try. -/

/--
error: cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12; some
routes run with a higher limit of their own). This is a resource limit, not a refutation of the
goal. A larger setting may help: write `set_option maxRecDepth 48 in` before the tactic
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2 + x) (2 * x + 1) x := by
  set_option maxRecDepth 12 in cas

/-- error: cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12 -/
#guard_msgs (error, substring := true) in
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
  set_option maxRecDepth 12 in cas

/-- error: cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12 -/
#guard_msgs (error, substring := true) in
example (x : ℝ) : x + 1 = 1 + x := by
  set_option maxRecDepth 12 in cas

/-- error: cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12 -/
#guard_msgs (error, substring := true) in
example (x : ℝ) : x + 1 = 1 + x := by
  set_option maxRecDepth 12 in cas?

/-- error: cega exceeded Lean's maximum recursion depth (the option maxRecDepth is 12 -/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  set_option maxRecDepth 12 in cega

/-- error: cega exceeded Lean's maximum recursion depth (the option maxRecDepth is 12 -/
#guard_msgs (error, substring := true) in
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 1000 := by
  set_option maxRecDepth 12 in cega

-- The failure is catchable, so `first` goes on to the next alternative.
set_option linter.unusedTactic false in
example (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2 + x) (2 * x + 1) x := by
  first
    | set_option maxRecDepth 16 in cas
    | cas

/-! ## An interval integral short of the stated bound

The report gives the interval that the panel search proposes for the integral, rounded outward,
and a call with twice the panels. -/

/--
error: cega: with 1 Simpson panel the search proposes [1.717917, 1.719805] for the integral, an
interval of width less than 1.9e-3 that does not prove the stated bound. Each doubling of the
panels divides the Simpson remainder by 16; try `cega (panels := 2)`.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 1)

-- With the limits reversed, the interval is that of the integral as written.
/-- the search proposes [-1.719805, -1.717917] for the integral -/
#guard_msgs (error, substring := true, whitespace := lax) in
example : |(∫ x in (1 : ℝ)..0, Real.exp x) + 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 1)

-- The suggested call proves it, and so does the doubling search of bare `cega`.
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 2)

example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega

-- Over an empty interval the integral is `0`, and the report shows what `norm_num` left.
/--
error: cega: the integral is over an empty interval, so it is 0, and `norm_num` did not prove
the goal that remains:
  0 ≤ x
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (x : ℝ) : (∫ t in (0 : ℝ)..0, t) ≤ x := by
  cega

/-! ## Finite certificates

A closed statement with a decision procedure is the goal of `cega`'s finite certificate, so its
kernel failure leads the report; a failed batch is named by its range of indices and the goal as
written. -/

/--
error: CEGA finite certificate could not certify a checked computation: the kernel did not
reduce the decision procedure of
  ∀ (i : Fin 2), ↑i = 0
to `true`. The statement may be false, or its decision procedure may not reduce in the kernel.
This is a closed statement with a decision procedure, which `cega` proves by evaluating it in
the kernel
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : ∀ i : Fin 2, i.val = 0 := by
  cega

/--
error: cega [batch := 1] could not certify batch 2 of 2, the indices i with 1 ≤ i < 2, of
  ∀ (i : Fin 2), ↑i = 0
The kernel did not reduce the check of this batch to `true`
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : ∀ i : Fin 2, i.val = 0 := by
  cega [batch := 1]

/-! ## Closed real bounds

The kernel cannot evaluate a comparison of real numbers, so the finite certificate names the
classical decision procedure; the box route suggests more digits, and that call proves the
bound. -/

/--
Its decision procedure mentions `Real.decidableLT`, which is classical and never reduces in the
kernel. Whether or not that is what stopped this check, the failure says nothing about the truth
of the statement.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example :
    |Real.sqrt 2 - 14142135623730950488 / 10000000000000000000| < 1 / 10000000000000000000 := by
  cega

/--
The goal has no variables, so subdivision does not apply; if the bound is true, more
digits may prove it, as in `cega (digits := 30)`
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example :
    |Real.sqrt 2 - 14142135623730950488 / 10000000000000000000| < 1 / 10000000000000000000 := by
  cega

example :
    |Real.sqrt 2 - 14142135623730950488 / 10000000000000000000| < 1 / 10000000000000000000 := by
  cega (digits := 30)

-- A bound on a box: the advice names a deeper subdivision and a higher precision.
/--
If the bound is true, a deeper subdivision or a higher precision may prove it, as in
`cega (depth := 4)` or `cega (prec := 24)`.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 5 := by
  cega

/-! ## Determinants -/

/--
error: cas evaluated the determinant with `norm_det`; the goal became
  4 = 5
which is false, so the stated value is not the determinant.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : Matrix.det !![(2 : ℤ), 1, 1; 1, 2, 1; 1, 1, 2] = 5 := by
  cas

-- An equation that is not `det A = v`: the report shows the goal that remained and claims
-- nothing about it, since it is not a comparison of two numerals.
/--
error: cas evaluated the determinant with `norm_det`; the goal became
  4 + 1 = 4
cas could not prove this arithmetic relation.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : Matrix.det !![(2 : ℤ), 1, 1; 1, 2, 1; 1, 1, 2] + 1 = 4 := by
  cas

-- A false disequality: the residual is false, and nothing is said about a stated value.
/--
error: cas evaluated the determinant with `norm_det`; the goal became
  4 ≠ 4
which is false.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : Matrix.det !![(2 : ℤ), 1, 1; 1, 2, 1; 1, 1, 2] ≠ 4 := by
  cas

/-! ## Fallbacks

The `grind` and `norm_num` fallbacks report their first line; `trace.cas.fallback` shows the
rest. -/

/--
Grind fallback:
  `grind` failed (`set_option trace.cas.fallback true` shows its diagnostics)
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example : Nat.Prime 2305843009213693951 := by
  cas

/-! ## Derivatives as atoms

When its derivative routes fail on an equality, `cas` runs its arithmetic routes with the
derivatives as atoms. Here the two sides are derivatives of different functions at different
points, a shape that only the arithmetic routes prove. -/

example (k t x : ℝ) :
    deriv (fun s ↦ Real.exp (-k ^ 2 * s) * Real.sin (k * x)) t =
      deriv (fun y ↦ deriv (fun z ↦ Real.exp (-k ^ 2 * t) * Real.sin (k * z)) y) x := by
  cas

-- A wrong derivative is reported once, by the derivative route.
/--
error: cas computed a checked derivative, but it does not match the stated result.
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (x : ℝ) : deriv (fun x ↦ x ^ 2) x = 3 * x := by
  cas

/-! ## Lemmas of `cas [l₁, l₂]`

The lemmas are elaborated before any route runs, as `simp only [l₁, l₂]` elaborates them, so an
unknown name fails at once. -/

/-- error: Unknown identifier `nonexistent_lemma_xyz` -/
#guard_msgs in
example (x : ℝ) : x + 0 = x := by
  cas [nonexistent_lemma_xyz]

-- An applied hypothesis is elaborated in the context of the goal, as `simp only` elaborates it.
example (f : ℝ → ℝ) (x : ℝ) (hf : ∀ t, f t = t ^ 2) : f (x + 1) = x ^ 2 + 2 * x + 1 := by
  cas [hf (x + 1)]

/-! A reflected equality, one side of which evaluates a checked expression, goes on to the
arithmetic script when the reflected route does not prove it, and the lemmas unfold its
evaluations there. The first three goals come from a variational integrand whose partial
derivatives were rewritten to evaluations of `Verified.Expr.diff`. In the next two, ordinary
equalities, `2 * x` is evaluated alone and inside `-(2 * x)`; the larger expression is exposed
first, so that both become constructor trees before the arithmetic script runs. In the next,
unfolding the evaluator after the exposure proves the goal by itself. In the last, an opaque
checked expression cannot be read back, and the report of the failure names the exposure. -/

section ReflectedGoals

open CAS.Euclid2

/-- The trial function `x² + y²` of the integrand. -/
def quadraticTrial : Verified.Expr (Fin 2) :=
  x ^ 2 + y ^ 2

/-- The test function `x` of the integrand. -/
def coordinateTest : Verified.Expr (Fin 2) :=
  x

/-- The constant source `4` of the integrand. -/
def constantSource : Verified.Expr (Fin 2) :=
  4

/-- The coefficient `1` of a term of the integrand. -/
def unitCoefficient : Verified.Expr (Fin 2) :=
  1

example (p : ℝ^2) :
    ((x : Verified.Expr (Fin 2)).diff 0).eval p * (y : Verified.Expr (Fin 2)).eval p =
      (y : Verified.Expr (Fin 2)).eval p := by
  cas [Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.SymVar.expr]

example (p : ℝ^2) :
    ((x : Verified.Expr (Fin 2)).diff 0).eval p * ((y : Verified.Expr (Fin 2)).diff 0).eval p +
        ((x : Verified.Expr (Fin 2)).diff 1).eval p * ((y : Verified.Expr (Fin 2)).diff 1).eval p +
        (1 : Verified.Expr (Fin 2)).eval p * (x : Verified.Expr (Fin 2)).eval p *
          (y : Verified.Expr (Fin 2)).eval p -
        (0 : Verified.Expr (Fin 2)).eval p * (y : Verified.Expr (Fin 2)).eval p =
      (x * y : Verified.Expr (Fin 2)).eval p := by
  cas [Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.SymVar.expr]

example (p : ℝ^2) :
    (quadraticTrial.diff 0).eval p * (coordinateTest.diff 0).eval p +
        (quadraticTrial.diff 1).eval p * (coordinateTest.diff 1).eval p =
      (2 * x : Verified.Expr (Fin 2)).eval p := by
  cas [quadraticTrial, coordinateTest, Verified.Expr.diff, Verified.Expr.eval,
    Verified.Expr.SymVar.expr]

example (p : ℝ^2) :
    (2 * x : Verified.Expr (Fin 2)).eval p - constantSource.eval p * coordinateTest.eval p -
        (-(2 * x) : Verified.Expr (Fin 2)).eval p = 0 := by
  cas [constantSource, coordinateTest, Verified.Expr.eval, Verified.Expr.SymVar.expr]

example (p : ℝ^2) :
    (2 * x : Verified.Expr (Fin 2)).eval p + (-(2 * x) : Verified.Expr (Fin 2)).eval p = 0 := by
  cas

example (p : ℝ^2) (u : ℝ) : unitCoefficient.eval p * u = u := by
  cas

/-- A checked expression that the kernel does not unfold. -/
opaque hiddenTrial : Verified.Expr (Fin 2) := 0

/--
Exposure of checked expressions:
  checked normalization did not evaluate to a serialized result
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example (p : ℝ^2) : hiddenTrial.eval p ≤ hiddenTrial.eval p - 1 := by
  cas

end ReflectedGoals

/-! ## Reserved words

`fast` and `batch` stay ordinary identifiers in a module that imports the batched forms of
`cega`. -/

/-- An identifier named like an option of `cega`. -/
public def fast : ℕ := 1

/-- Another identifier named like an option of `cega`. -/
public def batch : ℕ := 2

example : fast + batch = 3 := rfl

example : ∀ i : Fin 3, i.val < 3 := by
  cega [batch := 2]

end CAS.Examples.Messages
