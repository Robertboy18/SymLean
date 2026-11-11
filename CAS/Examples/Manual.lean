/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Examples and commands quoted in the documentation

Theorem examples and `#cas` commands quoted in the documentation (`CAS.lean`, the README and
the manual of the website) that no other example file runs, so that `lake build` checks what
the documentation shows. Each command runs inside `#guard_msgs`, which checks the summary of its
report: the header, the input, the output and the conditions.

The commands that need Hex are checked in `CASHex/Examples.lean`, and the native certificate
example in `tests/cega`.
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CAS.Examples.Manual

/-! ## Theorem examples -/

section TheoremExamples

open MeasureTheory Filter Topology CAS.Certificate

example (x y : ℝ) : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by
  cas

example :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 1000000| ≤ 1 / 1000000 := by
  cega

example (ε x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2 + ε ^ 2) (2 * x) x := by
  cas

example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega [enclose x in [0, 1]] (x / (1 + x))

#guard_msgs (drop info) in
set_option cas.verbose true in
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  cas?

example (x y : ℝ) : Real.sin x + Real.cos y ≤ 2 := by
  cas

example (z : ℂ) : (z + 1) ^ 2 = z ^ 2 + 2 * z + 1 := by
  cas

example (a s t : ℝ) (ha : 0 < a) : a ^ (s / 2) * a ^ ((t - s) / 2) = a ^ (t / 2) := by
  cas

example (a p q : ℝ) (ha : 0 < a) : (a ^ p) ^ q = a ^ (p * q) := by
  cas

example (a b p : ℝ) (ha : 0 < a) (hb : 0 < b) : (a * b) ^ p = a ^ p * b ^ p := by
  cas

example (b : ℝ) (k : ℕ) (hb : 0 < b) : (b ^ 2) ^ ((k : ℝ) / 2) = b ^ k := by
  cas

example (t β : ℝ) (ht : 0 < t) : t ^ (β - 1) = t ^ β / t := by
  cas

example (t β : ℝ) (ht : 0 < t) : t ^ (-β) = 1 / t ^ β := by
  cas

example (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  cas

example (x : ℝ) : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
  cas

example (a b : ℝ) : Real.exp a * Real.exp b = Real.exp (a + b) := by
  cas

example (u : ℝ) : Real.exp u ^ 2 * Real.exp (-2 * u) = 1 := by
  cas

example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x = (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas using hx

example (z : ℂ) : deriv (fun w : ℂ ↦ Complex.sin w + w ^ 3) z =
    Complex.cos z + 3 * z ^ 2 := by
  cas

example (ε x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2 + ε ^ 2) (2 * x) x := by
  cas

example (u₀ : ℝ) (hne : u₀ ≠ 1) :
    HasDerivWithinAt (fun u : ℝ ↦ u / (1 - u)) (1 / (1 - u₀) ^ 2)
      (Set.Icc 0 (1 / 2)) u₀ := by
  cas

example (x : ℝ^2) :
    DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0 * Real.exp (y 1)) x := by
  cas

example : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 0 ^ 2 + x 1 ^ 2) := by
  cas

example : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ 1 / t) (Set.Ioi 0) := by
  cas

example (p : ℝ^2) (hp : p 0 ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 1 / y 0) p := by
  cas

example (a b : ℝ) (hnonzero : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, 1 / t) = Real.log b - Real.log a := by
  cas using hnonzero

example (x : ℝ) (hinside : 0 < 1 - x ^ 2) :
    HasDerivAt
      (fun t : ℝ ↦ t * Real.arccos t - Real.sqrt (1 - t ^ 2))
      (Real.arccos x) x := by
  cas

example : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
  cas

example : (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-t)) = 1 := by
  cas

example : (∫ t in Set.Ici (1 : ℝ), t ^ (-(2 : ℝ))) = 1 := by
  cas

example : (∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2)) = Real.pi / 4 := by
  cas

example (a : ℝ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..1, 1 / (a ^ 2 + t ^ 2)) = Real.arctan (1 / a) / a := by
  cas

example : (∫ t in (0 : ℝ)..(1 / 2), 1 / Real.sqrt (1 - t ^ 2)) = Real.arcsin (1 / 2) := by
  cas

example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    HasDerivAt (fun x ↦ ∫ t in a..x, f t) (f b) b := by
  cas

example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log t ^ 2 / 2
  cas [integrate primitive := F using h]

#guard_msgs (drop info) in
theorem log_div_integral_of_goal (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) =
      Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas? using h

example :
    BoundOn (fun p : ℝ^2 ↦ p 0 * p 1)
      {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3} 4 := by
  cega [enclose x in [0, 1], y in [2, 3]] (x * y)

end TheoremExamples

/-! ## Commands -/

/--
info: #cas (LegendreP 5 x)
Domain: x ∈ ℝ
Input (polynomial in x): LegendreP 5 x
Output (polynomial with exact rational coefficients): 63/8*x^5 - 35/4*x^3 + 15/8*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (LegendreP 5 x)

/--
info: #cas (LegendreP 10 x)
Domain: x ∈ ℝ
Input (polynomial in x): LegendreP 10 x
Output (polynomial with exact rational coefficients): 46189/256*x^10 - 109395/256*x^8 +
45045/128*x^6 - 15015/128*x^4 + 3465/256*x^2 - 63/256

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (LegendreP 10 x)

set_option linter.style.longLine false in
/--
info: #cas [N 20]
Domain: Legendre polynomial at a rational point
Input (scalar ℝ): (LegendreP 5 (1 / 3))
Output (exact rational value and its first 20 significant digits, truncated): 1/3 ≈ 0.33333333333333333333

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 20] (LegendreP 5 (1 / 3))

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^3 - x)
Output (scalar ℝ): x^3 - x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (x^3 - x)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ 3 - x)
Output (scalar ℝ): x*(x - 1)*(x + 1)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x ^ 3 - x)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^4 - 5*x^2 + 4)
Output (scalar ℝ): (x - 1)*(x + 1)*(x - 2)*(x + 2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^4 - 5*x^2 + 4)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^2 + 1)
Output (scalar ℝ): x^2 + 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^2 + 1)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^3 - 200000001*x^2 + 200000000*x)
Output (scalar ℝ): x*(x - 1)*(x - 200000000)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^3 - 200000001*x^2 + 200000000*x)

/--
error: limit: no route proved the limit at ∞.
Asymptotic comparison:
  limit: log of an argument that is not equivalent to a positive power
Substitution x = 1 / t:
  limit: the expression is not built from x by field operations and functions of arguments with
a finite limit
-/
#guard_msgs (error, substring := true) in
#cas [limit x → ∞] (log (exp x + 1) - x)

/--
error: dsolve: the coefficient of the derivative of order 0 is not a rational constant
-/
#guard_msgs (error, substring := true) in
#cas [dsolve y x] (y'' + x*y = 0)

/--
error: dsolve: the checked integrator found no primitive of e ^ P times the right side
-/
#guard_msgs (error, substring := true) in
#cas [dsolve y x] (y' + x*y = 1)

/-- error: `Simplify` is no mode of `#cas`; the nearest mode is `simplify` -/
#guard_msgs in
#cas [Simplify] (x + x)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x ^ 4 - 1) / (x ^ 2 - 1))
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))

/--
info: #cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (scalar ℝ): cos(x*y)*y

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (sin (x * y))

/--
info: #cas [grad x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (vector ℝ^2; order x, y): (cos(x*y)*y, cos(x*y)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [grad x, y] (sin (x * y))

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / sqrt (1 - x ^ 2))
Output (scalar ℝ; antiderivative): asin(x)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0; 1 - x^2 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / sqrt (1 - x ^ 2))

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x ^ 2 + x)
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (x ^ 2 + x)

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ 3)
Output (scalar ℝ): 3*x^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ 3)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (atan x)
Output (scalar ℝ; antiderivative): x*atan(x) - 1/2*log(1 + x^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (atan x)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 2 = 1)
Output (equivalent real solution predicate): x = 1 ∨ x = -1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 2 = 1)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x ^ 5 - x - 1 = 0)
Output (the only real solution, by 20 decimals, truncated): 1.16730397826141868425

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x ^ 5 - x - 1 = 0)

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (2 * x)
Output (scalar ℝ): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (2 * x)

/--
info: #cas [derive x]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): (a * x + b)
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (a * x + b)

/--
info: #cas (prec := 16) [enclose]
Domain: closed real expression
Input (scalar ℝ): (sqrt 2)
Output (certified interval in ℝ): [92681/65536, 46341/32768]
Upper bound: 46341/32768
Absolute bound: 46341/32768
Center and radius: 185363/131072 ± 1/131072

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (prec := 16) [enclose] (sqrt 2)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 2 + 1 = 0)
Output (equivalent real solution predicate): False

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 2 + 1 = 0)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x = x)
Output (equivalent real solution predicate): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x = x)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (real relation): (-2 * x + 3 ≤ 7)
Output (equivalent real solution predicate): x ≥ -2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (-2 * x + 3 ≤ 7)

/--
info: #cas [derive]
Domain: x ∈ ℝ
Input (scalar ℝ): 2 * x
Output (scalar ℝ): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x : ℝ ↦ 2 * x)

/--
info: #cas [derive]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): a * x + b
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x ↦ a * x + b)

/--
info: #cas [derive]
Domain: x ∈ ℝ
Input (scalar ℝ): 7
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x ↦ 7)

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): 2
Output (scalar ℝ; antiderivative): 2*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (fun x : ℝ ↦ 2)

/--
info: #cas [fullSimplify depth]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin (2*x) - 2*sin x*cos x)
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify depth] (sin (2*x) - 2*sin x*cos x)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x + 0) * 1)
Output (scalar ℝ): x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [simplify] ((x + 0) * 1)

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (2 * x + 2))
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (sqrt (2 * x + 2))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (3/2 : ℝ))
Output (scalar ℝ): 3/2*sqrt(x)
Conditions: x > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ (3/2 : ℝ))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (-2))
Output (scalar ℝ): -(2/x^3)
Conditions: x ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ (-2))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (arcsin x)
Output (scalar ℝ): 1/sqrt(1 - x^2)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (arcsin x)

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x)
Output (scalar ℝ; antiderivative): -cos(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (sin x)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 4)
Output (scalar ℝ; antiderivative): 3/8*x - 5/8*sin(x)*cos(x) + 1/4*sin(x)*cos(x)^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin x ^ 4)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (arccos x)
Output (scalar ℝ; antiderivative): x*acos(x) - sqrt(1 - x^2)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0; 1 - x^2 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (arccos x)

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / sin (2 * x) ^ 2)
Output (scalar ℝ; antiderivative): -(1/2/(sin(2*x)/cos(2*x)))
Conditions: sin(2*x) ≠ 0; cos(2*x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: (0*sin(2*x)/cos(2*x) + 1/2*(cos(2*x)*(0*x + 2*1)*cos(2*x) - sin(2*x)*-sin(2*x)*(0*x + 2*1))/cos(2*x)^2)/(sin(2*x)/cos(2*x))^2
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: (0*sin(2*x)/cos(2*x) + 1/2*(cos(2*x)*(0*x + 2*1)*cos(2*x) - sin(2*x)*-sin(2*x)*(0*x + 2*1))/cos(2*x)^2)/(sin(2*x)/cos(2*x))^2 - 1/sin(2*x)^2
      Definition: IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): sin(2*x)/cos(2*x), cos(2*x), sin(2*x)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          (∀ x ∈ Set.uIcc a b, Real.sin (2 * x) / Real.cos (2 * x) ≠ 0 ∧ Real.cos (2 * x) ≠ 0 ∧ Real.sin (2 * x) ≠ 0) →
            ∫ (x : ℝ) in a..b, 1 / Real.sin (2 * x) ^ 2 =
              -(1 / 2) / (Real.sin (2 * b) / Real.cos (2 * b)) + 1 / 2 / (Real.sin (2 * a) / Real.cos (2 * a))
        Validation: proof term checked by the kernel against this proposition
        Theorem: IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (Verified.Expr.DiffDerivation.build 0
              ((Verified.Expr.rat (-1) 2).div
                (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos))).rawDerivative =
          Verified.Expr.diff 0
            ((Verified.Expr.rat (-1) 2).div
              (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos))
        Validation: proof term checked by the kernel against this proposition
        Theorem: Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          Verified.Expr.eval ρ
              (Verified.Expr.DiffDerivation.build 0
                  ((Verified.Expr.rat (-1) 2).div
                    (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div
                      ((Verified.Expr.nat 2).mul 𝕏[0]).cos))).simplifiedDerivative =
            Verified.Expr.eval ρ
              (Verified.Expr.DiffDerivation.build 0
                  ((Verified.Expr.rat (-1) 2).div
                    (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          Verified.Expr.Alg.SideHolds ρ
              (Command.displayDerivativeRoute
                  (Verified.Expr.DiffDerivation.build 0
                    ((Verified.Expr.rat (-1) 2).div
                      (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)))).nonzero →
            Verified.Expr.eval ρ
                (Command.displayDerivativeRoute
                    (Verified.Expr.DiffDerivation.build 0
                      ((Verified.Expr.rat (-1) 2).div
                        (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)))).rhs =
              Verified.Expr.eval ρ
                (Verified.Expr.DiffDerivation.build 0
                    ((Verified.Expr.rat (-1) 2).div
                      (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div
                        ((Verified.Expr.nat 2).mul 𝕏[0]).cos))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          Verified.Expr.ValidAt x.ofLp
              ((Verified.Expr.rat (-1) 2).div
                (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)) →
            Verified.Expr.Alg.SideHolds x.ofLp
                (Command.displayDerivativeRoute
                    (Verified.Expr.DiffDerivation.build 0
                      ((Verified.Expr.rat (-1) 2).div
                        (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      Verified.Expr.eval y.ofLp
                        ((Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)))
                    x)
                  (EuclideanSpace.single 0 1) =
                Verified.Expr.eval x.ofLp
                  (Command.displayDerivativeRoute
                      (Verified.Expr.DiffDerivation.build 0
                        ((Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos)))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (IntegrationCheck.route 0 ((Verified.Expr.nat 1).div (((Verified.Expr.nat 2).mul 𝕏[0]).sin.pow 2))
              {
                  candidate :=
                    (Verified.Expr.rat (-1) 2).div
                      (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                  routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed requirements
        Proposition: ∀ (x : ℝ^1),
          {
                    candidate :=
                      (Verified.Expr.rat (-1) 2).div
                        (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                    routeZero := ⋯ }.requirements.Holds
              x.ofLp →
            Verified.Expr.eval x.ofLp
                (Verified.Expr.diff 0
                  {
                      candidate :=
                        (Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                      routeZero := ⋯ }.candidate) =
              Verified.Expr.eval x.ofLp ((Verified.Expr.nat 1).div (((Verified.Expr.nat 2).mul 𝕏[0]).sin.pow 2))
        Validation: proof term checked by the kernel against this proposition
        Theorem: IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          {
                    candidate :=
                      (Verified.Expr.rat (-1) 2).div
                        (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                    routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  {
                      candidate :=
                        (Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                      routeZero := ⋯ }.candidate)
              (Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                ((Verified.Expr.nat 1).div (((Verified.Expr.nat 2).mul 𝕏[0]).sin.pow 2)))
              t
        Validation: proof term checked by the kernel against this proposition
        Theorem: IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              {
                      candidate :=
                        (Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                      routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b,
                Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                  ((Verified.Expr.nat 1).div (((Verified.Expr.nat 2).mul 𝕏[0]).sin.pow 2)) =
              Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  {
                      candidate :=
                        (Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                      routeZero := ⋯ }.candidate -
                Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  {
                      candidate :=
                        (Verified.Expr.rat (-1) 2).div
                          (((Verified.Expr.nat 2).mul 𝕏[0]).sin.div ((Verified.Expr.nat 2).mul 𝕏[0]).cos),
                      routeZero := ⋯ }.candidate
        Validation: proof term checked by the kernel against this proposition
        Theorem: IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] direct: ordered-sparse-polynomial: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: pythagorean: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [integrate x] (1 / sin (2 * x) ^ 2)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (x * log x))
Output (scalar ℝ; antiderivative): log(log(x))
Conditions: x ≠ 0; log(x) ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / (x * log x))

/--
info: #cas [enclose x in [-1 / 10, 1 / 10]]
Domain: x ∈ [-1/10, 1/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (cos x)
Output (certified interval in ℝ): [0.995004, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: ≈0.997502 ± 0.002498

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x / (1 + x))
Output (certified interval in ℝ): [0, 1/2]
Upper bound: 1/2
Absolute bound: 1/2
Center and radius: 1/4 ± 1/4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (x / (1 + x))

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x)
Output (certified interval in ℝ): [0, 0.841471]
Upper bound: 0.841471
Absolute bound: 0.841471
Center and radius: ≈0.420735 ± 0.420736

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (sin x)

/--
info: #cas [enclose x in [10, 1001 / 100]]
Domain: x ∈ [10, 1001/100] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x)
Output (certified interval in ℝ): [-0.552385, -0.544021]
Upper bound: -0.544021
Absolute bound: 0.552385
Center and radius: ≈-0.548203 ± 0.004182

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [10, 1001 / 100]] (sin x)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x ^ 2 + cos x ^ 2)
Output (certified interval in ℝ): [1, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: 1 ± 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (sin x ^ 2 + cos x ^ 2)

/--
info: #cas [enclose x in [9 / 10, 11 / 10]]
Domain: x ∈ [9/10, 11/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x * exp (-x))
Output (certified interval in ℝ): [0.356443, 0.379316]
Upper bound: 0.379316
Absolute bound: 0.379316
Center and radius: ≈0.367879 ± 0.011437

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))

/--
info: #cas (prec := 40) [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (exp x)
Output (certified interval in ℝ): [1, 2.718282]
Upper bound: 2.718282
Absolute bound: 2.718282
Center and radius: ≈1.859140 ± 0.859142

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (prec := 40) [enclose x in [0, 1]] (exp x)

/--
info: #cas [enclose x in [-5, 5]]
Domain: x ∈ [-5, 5] ⊆ ℝ
Input (scalar map ℝ → ℝ): (tanh x)
Output (certified interval in ℝ): [-0.999910, 0.999910]
Upper bound: 0.999910
Absolute bound: 0.999910
Center and radius: ≈-0.000001 ± 0.999911

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-5, 5]] (tanh x)

/--
info: #cas [enclose x in [-2, 1]]
Domain: x ∈ [-2, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (|x|)
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-2, 1]] (|x|)

/--
info: #cas [enclose x in [-1 / 2, 1 / 2]]
Domain: x ∈ [-1/2, 1/2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (arcsin x)
Output (certified interval in ℝ): [-0.523599, 0.523599]
Upper bound: 0.523599
Absolute bound: 0.523599
Center and radius: 0 ± 0.523599

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-1 / 2, 1 / 2]] (arcsin x)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x - 2)
Output (certified interval in ℝ): [-2, -1]
Upper bound: -1
Absolute bound: 2
Center and radius: -3/2 ± 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (x - 2)

/--
info: #cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ y)
Output (scalar ℝ): y*x^(y - 1)
Conditions: x > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ y)

/--
info: #cas [integrate x]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): ((a * x + b) / (1 + x ^ 2))
Output (scalar ℝ; antiderivative): a*1/2*log(x^2 + 1) + b*atan(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] ((a * x + b) / (1 + x ^ 2))

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x) ^ 3 * (cos x) ^ 2
Output (scalar ℝ; antiderivative): -(1/3*cos(x)^3) + 1/5*cos(x)^5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (fun x ↦ (sin x) ^ 3 * (cos x) ^ 2)

/--
info: #cas [derive]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): a * x + b
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x : ℝ ↦ a * x + b)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x * sin (x ^ 2))
Output (scalar ℝ; antiderivative): -(1/2*cos(x^2))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x * sin (x ^ 2))

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + 3 * y' + 2 * y = exp x)
Output (order 2, characteristic roots: -1, -2): y(x) = exp(x)*1/6 + c₁*exp(-x) + c₂*exp(-(2*x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' + 3 * y' + 2 * y = exp x)

end CAS.Examples.Manual
