/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
meta import CAS.Command.Syntax
meta import CAS.Tactic.KernelReadBack

/-!
# The `#cas` command and the `cas` tactic on ordinary goals

The `#cas` command parses a restricted mathematical grammar and reifies it into
the checked symbolic language. It is an InfoView inspection command: its report
shows theorem- or certificate-backed evidence separately from diagnostic
metadata. Auxiliary theorems validate that evidence; a theorem tactic gives a
result a stable name.

Calculator expressions denote real scalar maps `ℝ^n → ℝ`. The InfoView summary
shows that domain, the input and output types, and any nonzero or positivity
conditions required by the checked theorem. `derive` is one scalar partial
derivative. `grad` returns all scalar partials in the declared coordinate
order, with no fixed dimension limit.

The compiled examples state ordinary Mathlib goals and close them with
`cas`, bare `cas` and `cas using h`: derivatives of elementary functions
with their domain conditions, branch-sensitive logarithm, square-root and
absolute-value identities, equation hints, and the Pythagorean and perfect-square
passes. The `cas` examples, primitives and definite integrals, are in
`BasicIntegration.lean`. No goal constructs a `Verified.Expr`. Each refusal is
checked with `fail_if_success`.

The `#cas` commands of the calculator run in the build in `Manual.lean`,
`EncloseSubdivided.lean` and the example file of each mode, each inside
`#guard_msgs`, which checks its report.

Real scalars are the default. An annotation such as `(x : ℝ)` records the
domain explicitly. Reports for `log`, division, and other branch-sensitive
operations state their analytic conditions in the compact summary.
-/

@[expose] public section

namespace CAS.Examples.Basic

/-! ## Ordinary theorem syntax -/

/-- `cas` proves an ordinary Mathlib derivative statement. -/
example (x : ℝ) :
    deriv Real.sin x = Real.cos x := by
  cas

/-- Coefficients may be ordinary real parameters; no reflected AST is required. -/
example (a b x : ℝ) :
    deriv (fun t : ℝ ↦ a * t ^ 2 + b) x = 2 * a * x := by
  cas

/--
The differentiated coordinate is real, while coefficients may originate in
other scalar types and use their ordinary Lean coercions.
-/
example (n : ℕ) (a : NNReal) (x : ℝ) :
    deriv (fun t : ℝ ↦ n * t ^ 2 + (a : ℝ) * t) x =
      2 * n * x + a := by
  cas

/-- Mathlib's total real-logarithm derivative is available directly. -/
example (x : ℝ) : deriv Real.log x = 1 / x := by
  cas

/-- Composed logarithms require their argument to be nonzero. -/
example (x : ℝ) (hx : x < 0) :
    deriv (fun t : ℝ ↦ Real.log (-t)) x = 1 / x := by
  cas using hx

/-- Side-aware derivative presentation uses the logarithm domain to cancel `x / x`. -/
example (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas using hx

/-- Arcsine differentiation excludes the two endpoints where it is not differentiable. -/
example (x : ℝ) (hneg : x ≠ -1) (hpos : x ≠ 1) :
    deriv Real.arcsin x = 1 / Real.sqrt (1 - x ^ 2) := by
  cas

/-- Top-level tangent differentiation reuses Mathlib's total derivative theorem. -/
example (x : ℝ) :
    deriv Real.tan x = 1 / Real.cos x ^ 2 := by
  cas

/-- A stated value in another form is identified with the lemma's by the checked identity core:
`tan` is lowered to `sin / cos`, the difference is brought to one fraction, and the Pythagorean
pass clears its numerator. The identity records `cos x ≠ 0`, taken from the context. -/
example (x : ℝ) (hcos : Real.cos x ≠ 0) : deriv Real.tan x = 1 + Real.tan x ^ 2 := by
  cas

example (x : ℝ) (hcos : Real.cos x ≠ 0) : 1 + Real.tan x ^ 2 = deriv Real.tan x := by
  cas

/-- The same identification on the `HasDerivAt` shape and on a composed tangent, which take
the reflected route. -/
example (x : ℝ) (hcos : Real.cos x ≠ 0) : HasDerivAt Real.tan (1 + Real.tan x ^ 2) x := by
  cas

example (x : ℝ) (hcos : Real.cos (2 * x) ≠ 0) :
    deriv (fun t : ℝ ↦ Real.tan (2 * t)) x = 2 * (1 + Real.tan (2 * x) ^ 2) := by
  cas

/-- The hyperbolic sine reuses its checked exponential normal form. -/
example (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sinh (2 * t)) x = 2 * Real.cosh (2 * x) := by
  cas

/-- Mathlib's total derivative of real absolute value is available directly. -/
example (x : ℝ) :
    deriv (fun t : ℝ ↦ |t|) x = SignType.sign x := by
  cas

/-- One-sided evidence closes a composed absolute-value derivative. -/
example (x : ℝ) (hpositive : 0 < 2 * x + 1) :
    deriv (fun t : ℝ ↦ |2 * t + 1|) x = 2 := by
  cas using hpositive

/-- The default tactic uses a local positivity hypothesis for a branch-sensitive identity. -/
example (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x) = x := by
  cas

/-- Positivity may derive a logarithm branch condition from weaker local data. -/
example (x : ℝ) (hx : x ≠ 0) :
    Real.exp (Real.log (x ^ 2)) = x ^ 2 := by
  cas

/-- The full real identity retains an absolute value under mere nonvanishing. -/
example (x : ℝ) (hx : x ≠ 0) :
    Real.exp (Real.log x) = |x| := by
  cas

/-- Negative-branch evidence simplifies the resulting absolute value correctly. -/
example (x : ℝ) (hx : x < 0) :
    Real.exp (Real.log x) = -x := by
  cas

/-- An unproved branch is preserved while a later provable occurrence simplifies. -/
example (x y : ℝ) :
    Real.exp (Real.log x) + Real.exp (Real.log (1 + y ^ 2)) =
      Real.exp (Real.log x) + (1 + y ^ 2) := by
  cas

/-- Explicit side evidence can also be supplied to the ordinary arithmetic route. -/
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  cas using hx

/-- Sign hypotheses discharge every denominator in a cross-cancellation. -/
example (x y : ℝ) (hx : 0 < x) (hy : y < 0) :
    (x / y) * (y / x) = 1 := by
  cas

/-- Univariate polynomial factors cancel under the exact nonzero condition. -/
example (x : ℝ) (hx : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas

/-- Equivalent rational normal forms are accepted after checked differentiation. -/
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ Real.log (t ^ 2)) x = 2 / x := by
  cas

/-- Literal negative powers reuse natural powers, division, and their checked domains. -/
example (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ ↦ t ^ (-2 : ℤ)) x = -2 / x ^ 3 := by
  cas using hx

/-! ## Arithmetic route: constants, factors, roots, absolute values

Before its Mathlib script, the identity route prepares the goal with theorem-backed steps:
a hypothesis `a * b ≠ 0` is split into its factor conditions, absolute values of sign-known
arguments are evaluated, powers are distributed over products, and the identities
`√u ^ 2 = u` and `√u * √u = u` join the context once `0 ≤ u` is provable. Closed goals with
transcendental constants such as `Real.pi` go through the field route with `positivity`, and
the nonvanishing discharger of `field_simp` recovers a distance condition that `simp_all`
rewrote. -/

/-- `π` is a positive constant: the cancellation needs no hypothesis. -/
example : 4 * Real.pi * (1 / (4 * Real.pi)) = 1 := by
  cas

/-- A quotient logarithm splits completely, including its factor `4 * π`. -/
example (τ : ℝ) (hτ : 0 < τ) :
    -(τ * Real.log (4 * Real.pi) + Real.log τ * τ) = τ * Real.log (1 / (4 * Real.pi * τ)) := by
  cas

/-- A quotient logarithm inside a rational expression (the heat-ball flux computation). -/
example (c τ : ℝ) (hτ : 0 < τ) :
    -c / 2 * Real.log (4 * τ) = (2 * c * τ * Real.log (1 / (4 * τ))) / (4 * τ) := by
  cas

/-! ### Equation hints

An equation supplied with `cas using h` is a rewrite rule for the simplifier and, when the
goal does not contain its left-hand side, a hypothesis of which the goal is a polynomial
multiple: the goal and the hypothesis are cleared of denominators with `field_simp`, the
multiplier is found by exact division of the goal difference by the hypothesis difference in
the sparse multivariate polynomial ring over their atoms, and `linear_combination` certifies
it; `linarith` and `nlinarith` remain the fallback when the division is not exact. -/

/-- The hint is used as a rewrite rule when its left-hand side occurs in the goal. -/
example (p q : ℝ) (h : p / q = p - 1) : p / q + 1 = p := by
  cas using h

/-- Otherwise it is cleared of denominators and used as a linear-combination hypothesis; the
nonvanishing of `q` comes from the context. -/
example (p q : ℝ) (hq : q ≠ 0) (h : p / q = p - 1) : p = q * (p - 1) := by
  cas using h

/-- The conjugate-exponent identity `1 / q = 1 - 1 / p` from `p / q = p - 1`. -/
example (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (h : p / q = p - 1) : 1 / q = 1 - 1 / p := by
  cas using h

/-- Nonconstant multipliers: the goal difference is `q` or `p` times the cleared hypothesis
`p = q * (p - 1)`. -/
example (p q : ℝ) (h : p / q = p - 1) (hq : q ≠ 0) : p * q = q ^ 2 * (p - 1) := by
  cas using h

example (p q : ℝ) (h : p / q = p - 1) (hq : q ≠ 0) : p ^ 2 = q * p * (p - 1) := by
  cas using h

/-- A polynomial hypothesis with the multiplier `x`. -/
example (x y : ℝ) (h : x ^ 2 + x = y) : x ^ 3 = x * y - x ^ 2 := by
  cas using h

/-- A product hypothesis `a * b ≠ 0` supplies both factor conditions. -/
example (a b t : ℝ) (h : a * b ≠ 0) : 1 - a * b * t = a * b * (1 / (a * b) - t) := by
  cas

/-- Strict positivity of a radicand is weakened to the nonnegativity that `Real.sq_sqrt`
needs. -/
example (d : ℝ) (hd : 0 < d) : Real.sqrt d ^ 2 = d := by
  cas

/-- An absolute value distributes over a quotient and is evaluated on a positive denominator. -/
example (x y t : ℝ) (ht : 0 < t) : |(x - y) / t| = |x - y| / t := by
  cas

/-- A quotient by a natural power splits into inverse factors. The identity also holds
when the scale or distance is zero. -/
example (n : ℕ) {E : Type*} [MetricSpace E] (a b : E) (t G : ℝ) :
    G / (t * dist a b) ^ n = (t ^ n)⁻¹ * ((dist a b ^ n)⁻¹ * G) := by
  cas

/-- The constant `2π`. Bare `cas` unfolds real-valued definitions of the current module, as
`cas` does. -/
noncomputable def twoPi : ℝ :=
  2 * Real.pi

example : twoPi / 2 = Real.pi := by
  cas

/-- Without the product hypothesis the factor conditions are unavailable. -/
example (a b t : ℝ) : a * b * t = a * b * t := by
  fail_if_success have : 1 - a * b * t = a * b * (1 / (a * b) - t) := by cas
  rfl

/-- Without a sign hypothesis on the radicand the square-root identity is not used. -/
example (d : ℝ) : d = d := by
  fail_if_success have : Real.sqrt d ^ 2 = d := by cas
  rfl

/-- Without the sign of the denominator the absolute value is kept. -/
example (x y t : ℝ) : (x - y) / t = (x - y) / t := by
  fail_if_success have : |(x - y) / t| = |x - y| / t := by cas
  rfl

/-! ### Pythagorean identity and roots of perfect squares

Two unconditional passes of the side-conditioned normalizer close the identities below on the
checked identity route. `pythagorean` replaces every pair of cosine factors and every power
`cos u ^ n` with `n ≥ 2` by `1 - sin u ^ 2` (`Real.cos_sq'`) in the polynomial part of the
difference of the two sides, so the polynomial normalizer sees an identity in the single atom
`sin u`; denominators, radicands, logarithm arguments, and real powers keep their shape.
`sqrt-numeral` replaces `√n` by the numeral `k` once the kernel has checked `k * k = n`
(`Real.sqrt_mul_self`), for natural, integer, and rational radicands and quotients of two
literals. Neither pass records a condition. -/

/-- The textbook orientation of the Pythagorean identity. -/
example (x : ℝ) : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
  cas

/-- The other orientation: the difference of the two sides is rewritten as a whole, so the
direction of the statement does not matter. -/
example (x : ℝ) : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
  cas

/-- The difference of squares in its double-angle form. -/
example (x : ℝ) : Real.cos x ^ 2 - Real.sin x ^ 2 = 1 - 2 * Real.sin x ^ 2 := by
  cas

/-- A cosine pair separated by another factor of the product. -/
example (x : ℝ) : x * Real.cos x ^ 2 = x - x * Real.sin x ^ 2 := by
  cas

/-- A fourth power is two pairs. -/
example (x : ℝ) : Real.cos x ^ 4 = (1 - Real.sin x ^ 2) ^ 2 := by
  cas

/-- The rewrite descends into the argument of an exponential. -/
example (x : ℝ) : Real.exp (Real.cos x ^ 2) = Real.exp (1 - Real.sin x ^ 2) := by
  cas

/-- A denominator keeps its shape: the recorded condition is `cos x ≠ 0`, which the hypothesis
discharges, not `1 - sin x ^ 2 ≠ 0`. -/
example (x : ℝ) (hcos : Real.cos x ≠ 0) :
    Real.sin x ^ 2 / Real.cos x ^ 2 = 1 / Real.cos x ^ 2 - 1 := by
  cas

/-- Without the hypothesis the quotient identity is refused: where the cosine vanishes, the
left side is `0` and the right side is `-1`. -/
example (x : ℝ) : x = x := by
  fail_if_success
    have : Real.sin x ^ 2 / Real.cos x ^ 2 = 1 / Real.cos x ^ 2 - 1 := by cas
  rfl

/-- A derivative whose stated value needs the identity: the computed derivative is
`cos x ^ 2 - sin x ^ 2`. -/
example (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sin t * Real.cos t) x = 1 - 2 * Real.sin x ^ 2 := by
  cas

/-- Square roots of perfect squares evaluate, for natural and rational radicands. -/
example : Real.sqrt 9 = 3 := by
  cas

example : Real.sqrt (1 / 4) = 1 / 2 := by
  cas

/-- A radicand that is not a perfect square is left alone; its square still cancels through the
square-root square identities. -/
example : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  cas

end CAS.Examples.Basic
