/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

/-!
# The functions that `#cas` evaluates as calls

`#cas (gamma (5/2))`, `#cas (ChebyshevT 5 x)` and `#cas (powerMod 2 100 7)` evaluate a special or
number-theoretic function written as an ordinary call, when the call is the whole input. The
table here lists these functions with the number of their arguments and the forms of `#cas` that
evaluate them. The parser hints, the reference and the dispatch of `#cas e` read it, so a
function is described once. In all three forms a call is recognized by its calculator spelling,
the unqualified name of an entry applied to positional arguments. A Lean declaration of the same
name does not change the dispatch, and a variable of the section with that name is refused.

## Main definitions

* `CAS.Command.CallableFunction`: an entry of the table.
* `CAS.Command.FunctionTable.callableFunctions`: the table.
* `CAS.Command.FunctionTable.callHint?`: the forms that evaluate a function of the table, for
  the messages that meet its name elsewhere.

## Implementation notes

The calls share one syntax, `#cas e`, rather than a mode per function, so a function of the
table needs no syntax of its own and is written as a call. The docstring of each entry is the
reference entry of its function, in the template of the mode docstrings.
-/

@[expose] public section

namespace CAS.Command

/-- The forms of `#cas` that evaluate a call of the table. -/
inductive CallForm where
  /-- `#cas (f a …)`: the exact value, or the polynomial of a family of polynomials. -/
  | bare
  /-- `#cas [expand] (f n x)`: the polynomial of a family in monomials. -/
  | expand
  /-- `#cas [N d] (f a …)`: digits of the value. For `erf` and `BesselJ` a decimal enclosure of
  width at most `10^-d`; for a family of polynomials at a rational point the exact value with its
  first `d` significant digits, truncated toward zero, whose decimal bounds the theorem states. -/
  | numeric
  deriving BEq, Repr

/-- A function that `#cas` evaluates when a call of it is the whole input. -/
structure CallableFunction where
  /-- The name, as a call writes it. -/
  name : String
  /-- The call with its arguments named, such as `ChebyshevT n x`. -/
  usage : String
  /-- The number of arguments. -/
  arity : Nat
  /-- The forms of `#cas` that evaluate the call. -/
  forms : List CallForm
  /-- Whether the call needs `import CASHex.NumberTheory`. -/
  needsHex : Bool
  /-- What the call computes, in a few words. -/
  summary : String

namespace FunctionTable

/-- `#cas (ChebyshevT n x)` prints the Chebyshev polynomial of the first kind `T_n` in monomials
with integer coefficients and proves the expansion in every commutative ring.

## Theorem
For the printed polynomial `p`, the report proves
`∀ (R : Type*) [CommRing R], Polynomial.Chebyshev.T R n = p`, with `p` written in
`Polynomial.X`. The kernel evaluates the coefficient list of degree `n`, and
`CAS.Analysis.SpecialFunctions.chebyshevT_eq_intPoly`, proved from Mathlib's recurrence
`Polynomial.Chebyshev.T_add_two`, identifies it with Mathlib's polynomial. At a rational `q`,
`#cas (ChebyshevT n q)` proves the exact rational value of `T_n` at `q`, and
`#cas [N d] (ChebyshevT n q)` adds its first `d` significant digits,
truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 80`, a literal or a closed integer expression such as
`2 * 3`. The second argument is a variable, which the printed polynomial is written in, or a
rational number. `#cas [expand] (ChebyshevT n x)` prints the same polynomial.

## Options
None.

## Examples
```lean
#cas (ChebyshevT 5 x)
```
```output
Output (polynomial with integer coefficients): 16*x^5 - 20*x^3 + 5*x
```
```lean
#cas [expand] (ChebyshevT 1 t)
```
```output
Output (polynomial with integer coefficients): t
```
```lean
#cas (ChebyshevT 5 (1/2))
```
```output
Output (exact rational value): 1/2
```

## In a proof
```lean
theorem chebyshevT_five_at_half
    (h : ∀ (R : Type*) [CommRing R], Polynomial.Chebyshev.T R 5 =
      16 * Polynomial.X ^ 5 - 20 * Polynomial.X ^ 3 + 5 * Polynomial.X) :
    (Polynomial.Chebyshev.T ℝ 5).eval (1 / 2) = 1 / 2 := by
  rw [h ℝ]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here to `R = ℝ` at
`x = 1/2`.

## See also
Mathematica `ChebyshevT`, SymPy `chebyshevt`. The calls `ChebyshevU n x` and `LegendreP n x`.

## Possible issues
```lean
#cas (ChebyshevT 81 x)
```
```output
ChebyshevT accepts degrees up to 80
```
Mathlib's recurrence `Polynomial.Chebyshev.T_add_two` gives higher degrees from two lower ones.
-/
def chebyshevT : CallableFunction :=
  { name := "ChebyshevT", usage := "ChebyshevT n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "Chebyshev polynomial of the first kind" }

/-- `#cas (ChebyshevU n x)` prints the Chebyshev polynomial of the second kind `U_n` in monomials
with integer coefficients and proves the expansion in every commutative ring.

## Theorem
For the printed polynomial `p`, the report proves
`∀ (R : Type*) [CommRing R], Polynomial.Chebyshev.U R n = p`, with `p` written in
`Polynomial.X`. The kernel evaluates the coefficient list of degree `n`, and
`CAS.Analysis.SpecialFunctions.chebyshevU_eq_intPoly`, proved from Mathlib's recurrence
`Polynomial.Chebyshev.U_add_two`, identifies it with Mathlib's polynomial. At a rational `q`,
`#cas (ChebyshevU n q)` proves the exact rational value of `U_n` at `q`, and
`#cas [N d] (ChebyshevU n q)` adds its first `d` significant digits,
truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 80`, a literal or a closed integer expression. The second
argument is a variable, which the printed polynomial is written in, or a rational number.
`#cas [expand] (ChebyshevU n x)` prints the same polynomial.

## Options
None.

## Examples
```lean
#cas (ChebyshevU 4 x)
```
```output
Output (polynomial with integer coefficients): 16*x^4 - 12*x^2 + 1
```
```lean
#cas [expand] (ChebyshevU 2 x)
```
```output
Output (polynomial with integer coefficients): 4*x^2 - 1
```

## In a proof
```lean
theorem chebyshevU_four_at_one
    (h : ∀ (R : Type*) [CommRing R], Polynomial.Chebyshev.U R 4 =
      16 * Polynomial.X ^ 4 - 12 * Polynomial.X ^ 2 + 1) :
    (Polynomial.Chebyshev.U ℝ 4).eval 1 = 5 := by
  rw [h ℝ]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here to `R = ℝ` at
`x = 1`.

## See also
Mathematica `ChebyshevU`, SymPy `chebyshevu`. The calls `ChebyshevT n x` and `LegendreP n x`.

## Possible issues
```lean
#cas (ChebyshevU 81 x)
```
```output
ChebyshevU accepts degrees up to 80
```
Mathlib's recurrence `Polynomial.Chebyshev.U_add_two` gives higher degrees from two lower ones.
-/
def chebyshevU : CallableFunction :=
  { name := "ChebyshevU", usage := "ChebyshevU n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "Chebyshev polynomial of the second kind" }

/-- `#cas (HermiteH n x)` prints the physicists' Hermite polynomial `H_n` in monomials with
integer coefficients and proves the expansion at every real `x`.

## Theorem
Mathlib defines the probabilists' polynomial `Polynomial.hermite n`, and
`H_n (x) = √2 ^ n * Polynomial.hermite n (√2 * x)`. For the printed polynomial `p` the report
proves `∀ x : ℝ, √2 ^ n * Polynomial.aeval (√2 * x) (Polynomial.hermite n) = p`
(`CAS.Analysis.SpecialFunctions.sqrt_two_pow_mul_aeval_hermite`). At a rational `q`,
`#cas (HermiteH n q)` proves the exact rational value of `H_n` at `q`, and
`#cas [N d] (HermiteH n q)` adds its first `d` significant digits,
truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 60`, a literal or a closed integer expression. The second
argument is a variable, which the printed polynomial is written in, or a rational number.
`#cas [expand] (HermiteH n x)` prints the same polynomial.

## Options
None.

## Examples
```lean
#cas (HermiteH 4 x)
```
```output
Output (polynomial with integer coefficients): 16*x^4 - 48*x^2 + 12
```
```lean
#cas [expand] (HermiteH 5 x)
```
```output
Output (polynomial with integer coefficients): 32*x^5 - 160*x^3 + 120*x
```

## In a proof
```lean
theorem hermiteH_four_at_zero
    (h : ∀ x : ℝ, √2 ^ 4 * Polynomial.aeval (√2 * x) (Polynomial.hermite 4) =
      16 * x ^ 4 - 48 * x ^ 2 + 12) :
    √2 ^ 4 * Polynomial.aeval (√2 * 0) (Polynomial.hermite 4) = 12 := by
  rw [h 0]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here at `x = 0`.

## See also
Mathematica `HermiteH`, SymPy `hermite`. The call `HermiteHe n x`, Mathlib's own Hermite
polynomials.

## Possible issues
```lean
#cas (HermiteH 61 x)
```
```output
HermiteH accepts degrees up to 60
```
`#cas (HermiteHe n x)` accepts degrees up to 80, and `H_n (x) = √2 ^ n * He_n (√2 * x)` relates
the two.
-/
def hermiteH : CallableFunction :=
  { name := "HermiteH", usage := "HermiteH n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "physicists' Hermite polynomial" }

/-- `#cas (HermiteHe n x)` prints the probabilists' Hermite polynomial `He_n`, Mathlib's
`Polynomial.hermite n`, in monomials with integer coefficients and proves the expansion in `ℤ[X]`.

## Theorem
For the printed polynomial `p`, the report proves `Polynomial.hermite n = p` in `ℤ[X]`, with `p`
written in `Polynomial.X` (`CAS.Analysis.SpecialFunctions.hermite_eq_intPoly`, proved from
Mathlib's recurrence `Polynomial.hermite_succ`). At a rational `q`, `#cas (HermiteHe n q)`
proves the exact rational value of `He_n` at `q`, and `#cas [N d] (HermiteHe n q)` adds its
first `d` significant digits, truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 80`, a literal or a closed integer expression. The second
argument is a variable, which the printed polynomial is written in, or a rational number.
`#cas [expand] (HermiteHe n x)` prints the same polynomial.

## Options
None.

## Examples
```lean
#cas (HermiteHe 4 x)
```
```output
Output (polynomial with integer coefficients): x^4 - 6*x^2 + 3
```
```lean
#cas [expand] (HermiteHe 3 x)
```
```output
Output (polynomial with integer coefficients): x^3 - 3*x
```

## In a proof
```lean
theorem hermiteHe_four_at_one
    (h : Polynomial.hermite 4 = Polynomial.X ^ 4 - 6 * Polynomial.X ^ 2 + 3) :
    (Polynomial.hermite 4).eval 1 = -2 := by
  rw [h]
  norm_num
```
A proof can take the printed theorem as a hypothesis and evaluate it, as here at `x = 1`.

## See also
SymPy `hermite_prob`. The call `HermiteH n x`, the physicists' polynomials.

## Possible issues
```lean
#cas (HermiteHe 81 x)
```
```output
HermiteHe accepts degrees up to 80
```
Mathlib's recurrence `Polynomial.hermite_succ` gives higher degrees from lower ones.
-/
def hermiteHe : CallableFunction :=
  { name := "HermiteHe", usage := "HermiteHe n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "probabilists' Hermite polynomial" }

/-- `#cas (LegendreP n x)` prints the Legendre polynomial `P_n` in monomials with exact rational
coefficients and proves the expansion at every real `x`.

## Theorem
For the printed polynomial `p`, the report proves
`∀ x : ℝ, (CAS.Analysis.SpecialFunctions.legendre n).eval x = p` from the coefficient formula
`CAS.Analysis.SpecialFunctions.legendre_eval_eq_sum_coeff`. `legendre n` is Mathlib's shifted
Legendre polynomial `Polynomial.shiftedLegendre n` at `(1 - x) / 2`, so `P_n 1 = 1`. At a
rational `q`, `#cas (LegendreP n q)` proves the exact rational value of `P_n` at `q`, and
`#cas [N d] (LegendreP n q)` adds its first `d` significant digits,
truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 30`, a literal or a closed integer expression. The second
argument is a variable, which the printed polynomial is written in, or a rational number. The
kernel checks each coefficient, a closed rational computation.

## Options
None.

## Examples
```lean
#cas (LegendreP 3 x)
```
```output
Output (polynomial with exact rational coefficients): 5/2*x^3 - 3/2*x
```
```lean
#cas [expand] (LegendreP 5 x)
```
```output
Output (polynomial with exact rational coefficients): 63/8*x^5 - 35/4*x^3 + 15/8*x
```
```lean
#cas (LegendreP 2 (1/2))
```
```output
Output (exact rational value): -1/8
```

## In a proof
```lean
theorem legendre_three_at_half
    (h : ∀ x : ℝ,
      (CAS.Analysis.SpecialFunctions.legendre 3).eval x = 5 / 2 * x ^ 3 - 3 / 2 * x) :
    (CAS.Analysis.SpecialFunctions.legendre 3).eval (1 / 2) = -7 / 16 := by
  rw [h]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here at `x = 1/2`.

## See also
Mathematica `LegendreP`, SymPy `legendre`. The calls `ChebyshevT n x` and `HermiteHe n x`.

## Possible issues
```lean
#cas (LegendreP 31 x)
```
```output
LegendreP accepts degrees up to 30
```
The bound keeps the rational coefficients short; `legendre n` is defined at every degree.
-/
def legendreP : CallableFunction :=
  { name := "LegendreP", usage := "LegendreP n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "Legendre polynomial" }

/-- `#cas (BernoulliB n x)` prints the Bernoulli polynomial `B_n` in monomials with exact rational
coefficients and proves the expansion at every real `x`.

## Theorem
For the printed polynomial `p`, the report proves
`∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli n) = p` for Mathlib's
`Polynomial.bernoulli n`, from `Polynomial.coeff_bernoulli` and integer Bernoulli numerators that
the kernel evaluates (`CAS.Analysis.SpecialFunctions.bernoulli_eq_intPoly`). At a rational `q`,
`#cas (BernoulliB n q)` proves the exact rational value of `B_n` at `q`, and
`#cas [N d] (BernoulliB n q)` adds its first `d` significant digits,
truncated toward zero, with their decimal bounds in the theorem.

## Conditions and limits
`n` is a natural number with `n ≤ 60`, a literal or a closed integer expression. The second
argument is a variable, which the printed polynomial is written in, or a rational number. The
constant term of `B_n` is the Bernoulli number `bernoulli n`, with Mathlib's convention
`B_1 = -1/2`, which `#cas (BernoulliB n)` prints.

## Options
None.

## Examples
```lean
#cas (BernoulliB 4 x)
```
```output
Output (polynomial with exact rational coefficients): x^4 - 2*x^3 + x^2 - 1/30
```
```lean
#cas [expand] (BernoulliB 1 x)
```
```output
Output (polynomial with exact rational coefficients): x - 1/2
```

## In a proof
```lean
theorem bernoulliB_four_at_half
    (h : ∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli 4) =
      x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30) :
    Polynomial.aeval (1 / 2 : ℝ) (Polynomial.bernoulli 4) = 7 / 240 := by
  rw [h]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here at `x = 1/2`.

## See also
Mathematica `BernoulliB`, SymPy `bernoulli`. The call `BernoulliB n`, the Bernoulli numbers.

## Possible issues
```lean
#cas (BernoulliB 61 x)
```
```output
BernoulliB accepts degrees up to 60
```
`Polynomial.bernoulli_def` gives the coefficients at every degree in a proof.
-/
def bernoulliPolynomial : CallableFunction :=
  { name := "BernoulliB", usage := "BernoulliB n x", arity := 2,
    forms := [.bare, .expand, .numeric], needsHex := false,
    summary := "Bernoulli polynomial" }

/-- `#cas (BernoulliB n)` computes the Bernoulli number `Bₙ` of a natural number `n ≤ 60`, with
Mathlib's convention `B₁ = -1/2`, and proves it.

## Theorem
The report proves `bernoulli n = q` in `ℚ` for Mathlib's `bernoulli`; Mathlib's `bernoulli'`
has `B'₁ = 1/2` instead. The proof rewrites with
`CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators`, which holds at every `n` and writes `Bₙ`
as entry `n` of the integer recurrence `bernoulliNumerators n` over `(n + 1)!`, and the kernel
evaluates the recurrence and decides the equation (`decide +kernel`).

## Conditions and limits
`n` is a natural number with `n ≤ 60`, the largest index the command computes, a literal or a
closed integer expression. `B₀ = 1`, and `Bₙ = 0` for odd `n ≥ 3`.

## Options
None.

## Examples
```lean
#cas (BernoulliB 10)
```
```output
Output (Bernoulli number): 5/66
```
```lean
#cas (BernoulliB 1)
```
```output
Output (Bernoulli number): -1/2
```
```lean
#cas (BernoulliB 20)
```
```output
Output (Bernoulli number): -174611/330
```

## In a proof
```lean
theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators]
  decide +kernel
```
A proof repeats the two steps of the command, since the tactic `cas` does not evaluate
`bernoulli`.

## See also
Mathematica `BernoulliB`, SymPy `bernoulli`. The calls `BernoulliB n x`, whose constant term is
`Bₙ`, and `zeta s`, whose values at the even positive and the nonpositive integers are Bernoulli
numbers.

## Possible issues
```lean
#cas (BernoulliB 61)
```
```output
BernoulliB computes Bₙ for n ≤ 60
```
The command stops at `60`, its cutoff; `bernoulli_eq_numerators` holds at every `n`.
-/
def bernoulliNumber : CallableFunction :=
  { name := "BernoulliB", usage := "BernoulliB n", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "Bernoulli number" }

/-- `#cas (zeta s)` computes the exact value of the Riemann zeta function at an even positive
integer or a nonpositive integer `s` and proves it.

## Theorem
At an even `s = 2k > 0` the report proves `riemannZeta s = q * (Real.pi : ℂ) ^ s` with a rational
`q` (`riemannZeta_two_mul_nat`), such as `riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6`. At an integer
`s ≤ 0` it proves `riemannZeta s = q` (`riemannZeta_neg_nat_eq_bernoulli`). The equations hold in
`ℂ`, for Mathlib's `riemannZeta`, and `q` comes from a Bernoulli number that the kernel
evaluates.

## Conditions and limits
`s` is a closed rational expression whose value is an integer, such as `2` or `(-1)`. The odd
integers `s ≥ 3` and the pole `s = 1` are refused, and so are other rationals and integers
outside `-59 ≤ s ≤ 60`.

## Options
None.

## Examples
```lean
#cas (zeta 2)
```
```output
Output (exact value of ζ): pi^2/6
```
```lean
#cas (zeta 4)
```
```output
Output (exact value of ζ): pi^4/90
```
```lean
#cas (zeta (-1))
```
```output
Output (exact value of ζ): -1/12
```

## In a proof
```lean
theorem six_mul_zeta_two (h : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6) :
    6 * riemannZeta 2 = (Real.pi : ℂ) ^ 2 := by
  rw [h]
  ring
```
A proof can take the printed theorem as a hypothesis and use it, as here.

## See also
Mathematica `Zeta`, SymPy `zeta`. The call `BernoulliB n` and the mode `sum`, which sums
series.

## Possible issues
```lean
#cas (zeta 3)
```
```output
zeta: unsupported formula at the odd integer `3`; exact values are computed at even positive and
at nonpositive integers
```
The evaluator has formulas, by Bernoulli numbers, at the even integers `2 ≤ s ≤ 60` and the
integers `-59 ≤ s ≤ 0`, and none at the odd integers `s ≥ 3`. `#cas (zeta 1)` is refused too,
since `s = 1` is the pole.
-/
def zeta : CallableFunction :=
  { name := "zeta", usage := "zeta s", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "Riemann zeta function at an integer" }

/-- `#cas (gamma q)` computes the exact value of the Gamma function at an integer or a
half-integer `q` and proves it.

## Theorem
At a positive integer `q` the report proves `Real.Gamma q = v` with `v = (q - 1)!`, and at a
half-integer `Real.Gamma q = a * √Real.pi / b` with integers `a` and `b`. The proof is one
rewrite with a closed formula and a `norm_num` step: `Real.Gamma_nat_eq_factorial`,
`Γ (n + 1) = n!`, Mathlib's `Real.Gamma_nat_add_half`, `Γ (k + 1/2) = (2k - 1)‼ √π / 2^k`, and
`CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat`, `Γ (1/2 - k) = (-2)^k √π / (2k - 1)‼`. At an
integer `q ≤ 0`, a pole of `Γ`, the report proves `Real.Gamma q = 0`, Mathlib's value there
(`Real.Gamma_neg_nat_eq_zero`), and the Output line says so.

## Conditions and limits
`q` is a closed rational expression whose value is an integer or a half-integer with
`|q| ≤ 1001/2`. Other rationals, irrational numbers and symbols are refused.

## Options
None.

## Examples
```lean
#cas (gamma 5)
```
```output
Output (exact value of Γ): 24
```
```lean
#cas (gamma (5/2))
```
```output
Output (exact value of Γ): 3√π/4
```
```lean
#cas (gamma (-3/2))
```
```output
Output (exact value of Γ): 4√π/3
```
```lean
#cas (gamma (-3))
```
```output
Output (exact value of Γ): 0 (Mathlib's value at the pole -3; Mathematica: ComplexInfinity)
```

## In a proof
```lean
theorem gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * √Real.pi := by
  cas
```
The tactic `cas` proves `Real.Gamma q = v` with the same closed formulas.

## See also
Mathematica `Gamma`, SymPy `gamma`. The calls `factorial n`, since `Γ (n + 1) = n!`, and
`zeta s`.

## Possible issues
```lean
#cas (gamma (1/3))
```
```output
gamma: exact values are computed at integers and half-integers; `1/3` is neither
```
The evaluator has formulas only at the integers, `(q - 1)!` and Mathlib's `0` at the poles, and
at the half-integers, rational multiples of `√π`.
-/
def gamma : CallableFunction :=
  { name := "gamma", usage := "gamma x", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "Gamma function at an integer or a half-integer" }

/-- `#cas [N d] (erf q)` proves a decimal enclosure of width at most `10^-d` of the error function
`CAS.erf q` at a rational `q`.

## Theorem
The report proves `a ≤ CAS.erf q ∧ CAS.erf q ≤ b ∧ b - a ≤ 1 / 10 ^ d` for the printed interval
`[a, b]`. `CAS.erf x = 2 / √π ∫₀ˣ e^(-t²) dt`; the kernel checks a partial sum of its Taylor
series with a bound on the tail, and an interval for `√π` from Machin's formula.

## Conditions and limits
`q` is a rational with `|q| ≤ 10` and a denominator of at most `1000`, and `1 ≤ d ≤ 30`. `erf`
is `CAS.erf`, defined by the Gaussian integral above, since the Mathlib that SymLean builds on
has no error function. The call computes enclosures only, so `#cas (erf q)` is refused and points
to `#cas [N d] (erf q)`; the library proves the exact value `CAS.erf_zero : CAS.erf 0 = 0`.

## Options
None.

## Examples
```lean
#cas [N 30] (erf 1)
```
```output
Output (decimal enclosure of width at most 10^-30, with 30 terms of the series):
[0.8427007929497148693412206350826, 0.8427007929497148693412206350827]
```

## In a proof
```lean
theorem erf_one_pos (h : 21 / 25 ≤ CAS.erf 1 ∧ CAS.erf 1 ≤ 17 / 20) : 0 < CAS.erf 1 := by
  linarith [h.1]
```
A proof can take an enclosure as a hypothesis, as here a coarser one than the printed interval.

## See also
Mathematica `Erf`, SymPy `erf`. The mode `integrate`, which integrates Gaussians in terms of
`erf`, and the call `BesselJ n x`.

## Possible issues
```lean
#cas [N 10] (erf 11)
```
```output
erf accepts rational points with |q| ≤ 10 and a denominator of at most 1000
```
The series converges slowly far from `0`, so the bound keeps the kernel's partial sum short.
-/
def erf : CallableFunction :=
  { name := "erf", usage := "erf x", arity := 1,
    forms := [.numeric], needsHex := false,
    summary := "error function, by its digits" }

/-- `#cas [N d] (BesselJ n q)` proves a decimal enclosure of width at most `10^-d` of the Bessel
function `Complex.besselJ n q` at an integer order `n` and a rational `q`.

## Theorem
The report proves `∃ r : ℝ, Complex.besselJ n q = r ∧ a ≤ r ∧ r ≤ b ∧ b - a ≤ 1 / 10 ^ d` for
the printed interval `[a, b]` and Mathlib's `Complex.besselJ`. The kernel checks a partial sum of
the power series with a bound on its tail.

## Conditions and limits
`n` is an integer with `|n| ≤ 50`, `q` a rational with `|q| ≤ 50` and a denominator of at most
`1000`, and `1 ≤ d ≤ 30`. The call computes enclosures only, so `#cas (BesselJ n q)` is refused
and points to `#cas [N d] (BesselJ n q)`; Mathlib's `Complex.besselJ_zero` gives the exact value
at `0`.

## Options
None.

## Examples
```lean
#cas [N 10] (BesselJ 0 1)
```
```output
Output (decimal enclosure of width at most 10^-10, with 8 terms of the series):
[0.76519768655, 0.76519768656]
```

## In a proof
```lean
theorem besselJ_zero_one_pos
    (h : ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 3 / 4 ≤ r ∧ r ≤ 4 / 5) :
    ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 0 < r := by
  obtain ⟨r, hr, hlo, -⟩ := h
  exact ⟨r, hr, by linarith⟩
```
A proof can take an enclosure as a hypothesis, as here a coarser one than the printed interval.

## See also
Mathematica `BesselJ`, SymPy `besselj`. The call `erf x`.

## Possible issues
```lean
#cas [N 5] (BesselJ (1/2) 1)
```
```output
BesselJ accepts integer orders
```
Mathlib defines `Complex.besselJ` at every complex order; the series check is written for integer
orders.
-/
def besselJ : CallableFunction :=
  { name := "BesselJ", usage := "BesselJ n x", arity := 2,
    forms := [.numeric], needsHex := false,
    summary := "Bessel function of the first kind, by its digits" }

/-- `#cas (eulerPhi n)` computes Euler's totient `φ(n)`, the number of `0 ≤ i < n` coprime to
`n`, for a natural number `n` and proves it.

## Theorem
The report proves `Nat.totient n = t` for Mathlib's `Nat.totient`. Without Hex,
`CAS.NumberTheory.totient_eq_rangeSum` writes `φ(n)` as a sum of indicators of `gcd n d = 1`
over `[0, n)`, which the kernel evaluates. With `import CASHex.NumberTheory`, Hex factors `n`,
and `CAS.NumberTheory.totient_eq_of_primeFactorsList` computes `φ(n) = n / ∏ p * ∏ (p - 1)` from
the kernel-checked list of prime factors.

## Conditions and limits
`n` is a natural number, a literal or a closed integer expression. Without Hex `n ≤ 100000`; with
Hex the bound is the budget of its factor search. `φ(0) = 0` and `φ(1) = 1`.

## Options
None.

## Examples
```lean
#cas (eulerPhi 360)
```
```output
Output (eulerPhi): 96
```
```lean
#cas (eulerPhi 100)
```
```output
Output (eulerPhi): 40
```

## In a proof
```lean
theorem totient_thirty_six : Nat.totient 36 = 12 := by
  cas
```

## See also
Mathematica `EulerPhi`, SymPy `totient`. The calls `divisorSigma k n` and `moebiusMu n`, and the
mode `factorInteger`.

## Possible issues
```lean
#cas (eulerPhi 1000003)
```
```output
eulerPhi counts the residues coprime to n ≤ 100000 without Hex; for `1000003`,
`import CASHex.NumberTheory` computes φ from the factorization
```
Without Hex the count runs over all of `[0, n)`; Hex's factorization makes the product formula
apply.
-/
def eulerPhi : CallableFunction :=
  { name := "eulerPhi", usage := "eulerPhi n", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "Euler's totient" }

/-- `#cas (divisorSigma k n)` computes the sum `σₖ(n)` of the `k`-th powers of the divisors of a
positive natural number `n` and proves it.

## Theorem
The report proves `ArithmeticFunction.sigma k n = s` for Mathlib's `ArithmeticFunction.sigma`
by `CAS.NumberTheory.sigma_eq_of_cert`: the kernel checks the list of divisors of `n` with a
counting certificate, `⌊√n⌋` divisions and no factorization, and sums their `k`-th powers.

## Conditions and limits
`k` and `n` are natural numbers, literals or closed integer expressions, with
`1 ≤ n < 10^12` and `k < 2^32`, the exponents for which the kernel evaluates the powers `d ^ k`
of the certificate. The value has at most 10000 digits. `σ₀(n)` is the number of divisors of `n`
and `σ₁(n)` their sum.

## Options
None.

## Examples
```lean
#cas (divisorSigma 1 360)
```
```output
Output (divisorSigma 1): 1170
```
```lean
#cas (divisorSigma 2 12)
```
```output
Output (divisorSigma 2): 210
```
```lean
#cas (divisorSigma 0 360)
```
```output
Output (divisorSigma 0): 24
```

## In a proof
```lean
theorem sigma_two_twelve : ArithmeticFunction.sigma 2 12 = 210 := by
  cas
```

## See also
Mathematica `DivisorSigma`, SymPy `divisor_sigma`. The mode `divisors`, which prints the list
with the same certificate, and the calls `eulerPhi n` and `moebiusMu n`.

## Possible issues
```lean
#cas (divisorSigma 1 0)
```
```output
divisorSigma: expected a positive natural number
```
Every natural number divides `0`, and Mathlib sets `ArithmeticFunction.sigma k 0 = 0`.
-/
def divisorSigma : CallableFunction :=
  { name := "divisorSigma", usage := "divisorSigma k n", arity := 2,
    forms := [.bare], needsHex := false,
    summary := "sum of the k-th powers of the divisors" }

/-- `#cas (binomial n k)` computes the binomial coefficient `C(n, k)` of natural numbers `n` and
`k` and proves it.

## Theorem
The report proves `Nat.choose n k = c` for Mathlib's `Nat.choose`. For `k ≤ n` the proof rewrites
with `Nat.choose_eq_descFactorial_div_factorial`, after `Nat.choose_symm` when `n - k < k`, and
`norm_num` evaluates `n (n - 1) ⋯ (n - j + 1) / j!` for the smaller `j` of `k` and `n - k`. For
`k > n` it applies `Nat.choose_eq_zero_of_lt`, and `c = 0`.

## Conditions and limits
`n` and `k` are natural numbers, literals or closed integer expressions such as `2 ^ 10`, and for
`k > n` the coefficient is `0`. Negative and non-integer arguments are refused, since
`Nat.choose` is defined on natural numbers. The value has at most 10000 digits.

## Options
None.

## Examples
```lean
#cas (binomial 100 50)
```
```output
Output (binomial): 100891344545564193334812497256
```
```lean
#cas (binomial 10 3)
```
```output
Output (binomial): 120
```
```lean
#cas (binomial 3 10)
```
```output
Output (binomial): 0
```

## In a proof
```lean
theorem choose_ten_three : Nat.choose 10 3 = 120 := by
  cas
```

## See also
Mathematica `Binomial`, SymPy `binomial`. The call `factorial n`.

## Possible issues
```lean
#cas (binomial (-3) 2)
```
```output
binomial takes a natural number as its first argument; `-3` is negative
```
Mathlib's `Ring.choose` extends `C(n, k)` to negative `n`; the call evaluates `Nat.choose`.
-/
def binomial : CallableFunction :=
  { name := "binomial", usage := "binomial n k", arity := 2,
    forms := [.bare], needsHex := false,
    summary := "binomial coefficient" }

/-- `#cas (factorial n)` computes the factorial `n! = 1 · 2 ⋯ n` of a natural number `n` and
proves it.

## Theorem
The report proves `Nat.factorial n = f` for Mathlib's `Nat.factorial`. `norm_num` proves it with
Mathlib's extension for factorials (`Mathlib.Tactic.NormNum.NatFactorial`), which splits the
product in halves, and `decide +kernel` is the fallback.

## Conditions and limits
`n` is a natural number, a literal or a closed integer expression, and `0! = 1`. The value has
at most 10000 digits.

## Options
None.

## Examples
```lean
#cas (factorial 30)
```
```output
Output (factorial): 265252859812191058636308480000000
```
```lean
#cas (factorial 10)
```
```output
Output (factorial): 3628800
```
```lean
#cas (factorial 0)
```
```output
Output (factorial): 1
```

## In a proof
```lean
theorem factorial_ten : Nat.factorial 10 = 3628800 := by
  cas
```

## See also
Mathematica `Factorial`, SymPy `factorial`. The calls `binomial n k` and `gamma x`, since
`Γ (n + 1) = n!`.

## Possible issues
```lean
#cas (factorial (-1))
```
```output
factorial takes a natural number as its argument; `-1` is negative
```
`Γ` extends the factorial to the half-integers: `#cas (gamma (7/2))`.
-/
def factorial : CallableFunction :=
  { name := "factorial", usage := "factorial n", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "factorial" }

/-- `#cas (fibonacci n)` computes the Fibonacci number `Fₙ` of a natural number `n`, with `F₀ = 0`,
`F₁ = 1` and `Fₙ₊₂ = Fₙ₊₁ + Fₙ`, and proves it.

## Theorem
The report proves `Nat.fib n = F` for Mathlib's `Nat.fib`. `norm_num` proves it with Mathlib's
extension for `Nat.fib` (`Mathlib.Tactic.NormNum.NatFib`), which uses the doubling formulas of
`Nat.fastFib`, so the number of proof steps grows with the number of binary digits of `n`.

## Conditions and limits
`n` is a natural number, a literal or a closed integer expression. The value has at most 10000
digits.

## Options
None.

## Examples
```lean
#cas (fibonacci 100)
```
```output
Output (fibonacci): 354224848179261915075
```
```lean
#cas (fibonacci 20)
```
```output
Output (fibonacci): 6765
```

## In a proof
```lean
theorem fib_twenty : Nat.fib 20 = 6765 := by
  cas
```

## See also
Mathematica `Fibonacci`, SymPy `fibonacci`. The mode `rsolve`, which solves linear recurrences.

## Possible issues
```lean
#cas (fibonacci (-5))
```
```output
fibonacci takes a natural number as its argument; `-5` is negative
```
Mathlib's `Nat.fib` is defined on natural numbers.
-/
def fibonacci : CallableFunction :=
  { name := "fibonacci", usage := "fibonacci n", arity := 1,
    forms := [.bare], needsHex := false,
    summary := "Fibonacci number" }

/-- `#cas (powerMod a b m)` computes `a ^ b mod m` for natural numbers `a`, `b` and a positive
modulus `m` and proves it.

## Theorem
The report proves `a ^ b % m = r` in `ℕ`, with `r < m`. The proof is Mathlib's
`Mathlib.Meta.NormNum.evalNatPowMod`, repeated squaring, so its size grows with the number of
digits of `b`, and exponents with hundreds of digits are fine.

## Conditions and limits
`a`, `b` and `m` are natural numbers, literals or closed integer expressions, with `m ≥ 1`.

## Options
None.

## Examples
```lean
#cas (powerMod 3 1000 7)
```
```output
Output (modular power): 4
```
```lean
#cas (powerMod 2 123456789123456789123456789 1000000007)
```
```output
Output (modular power): 612059118
```
```lean
#cas (powerMod 2 100 7)
```
```output
Output (modular power): 2
```

## In a proof
```lean
theorem three_pow_mod_seven : 3 ^ 1000 % 7 = 4 := by
  cas
```

## See also
Mathematica `PowerMod`, Python `pow(a, b, m)`. The calls `modularInverse a m` and
`jacobiSymbol a n`.

## Possible issues
```lean
#cas (powerMod 2 10 0)
```
```output
powerMod: the modulus must be positive
```
Every natural number is `0` modulo `1`, and Mathlib's `a % 0 = a`; the call asks for `m ≥ 1`.
-/
def powerMod : CallableFunction :=
  { name := "powerMod", usage := "powerMod a b m", arity := 3,
    forms := [.bare], needsHex := false,
    summary := "modular power" }

/-- `#cas (modularInverse a m)` computes the inverse of an integer `a` modulo `m ≥ 2` in
`ZMod m`, or proves that there is none.

## Theorem
When `gcd(a, m) = 1` the report proves `(a : ZMod m) * r = 1 ∧ (a : ZMod m)⁻¹ = r` with
`0 ≤ r < m`, by kernel evaluation in `ZMod m` and `ZMod.inv_eq_of_mul_eq_one`. Otherwise it
proves `Nat.gcd |a| m = g ∧ ¬ IsUnit (a : ZMod m)` with `g > 1`, by
`ZMod.isUnit_iff_coprime`. The inverse comes from the extended Euclidean algorithm.

## Conditions and limits
`a` is an integer and `m` a natural number with `m ≥ 2`, literals or closed integer expressions.

## Options
None.

## Examples
```lean
#cas (modularInverse 3 11)
```
```output
Output (modular inverse): 4
```
```lean
#cas (modularInverse 17 3120)
```
```output
Output (modular inverse): 2753
```
```lean
#cas (modularInverse (-3) 7)
```
```output
Output (modular inverse): 2
```
```lean
#cas (modularInverse 6 9)
```
```output
Output (no inverse): none: gcd = 3
```

## In a proof
```lean
theorem inverse_three_mod_eleven : (3 : ZMod 11)⁻¹ = 4 := by
  cas
```
`cas` proves `(a : ZMod m)⁻¹ = b` for a unit `a` with the certificate of the call: the kernel
evaluates `a * b = 1` in `ZMod m`, and `ZMod.inv_eq_of_mul_eq_one` gives the inverse.

## See also
Mathematica `ModularInverse`, SymPy `mod_inverse`. The mode `extendedGCD`, which prints the
Bézout coefficients, and the call `powerMod a b m`.

## Possible issues
```lean
#cas (modularInverse 3 1)
```
```output
modularInverse: the modulus must be at least 2
```
`ZMod 1` is the zero ring, where every element is its own inverse.
-/
def modularInverse : CallableFunction :=
  { name := "modularInverse", usage := "modularInverse a m", arity := 2,
    forms := [.bare], needsHex := false,
    summary := "inverse modulo m" }

/-- `#cas (jacobiSymbol a n)` computes the Jacobi symbol `(a / n)` of an integer `a` and an odd
natural number `n` and proves it.

## Theorem
The report proves `jacobiSym a n = j` for Mathlib's `jacobiSym`, with `j` one of `-1`, `0` and
`1`, by `CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop`: the kernel runs a loop that takes out
factors `2` with the value of `(2 / n)` and otherwise swaps the arguments by quadratic
reciprocity. For a prime `n` the symbol is the Legendre symbol. For every odd `n`, `j = -1` shows
that `a` is not a square modulo `n` (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`).

## Conditions and limits
`a` is an integer and `n` an odd natural number, literals or closed integer expressions;
`(a / 1) = 1`, and `j = 0` exactly when `gcd(a, n) > 1`.

## Options
None.

## Examples
```lean
#cas (jacobiSymbol 1001 9907)
```
```output
Output (Jacobi symbol): -1
```
```lean
#cas (jacobiSymbol 2 15)
```
```output
Output (Jacobi symbol): 1
```
```lean
#cas (jacobiSymbol 6 9)
```
```output
Output (Jacobi symbol): 0
```

## In a proof
```lean
theorem not_square_mod_9907 : ¬IsSquare ((1001 : ℤ) : ZMod 9907) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one (by cas)
```
`cas` proves `jacobiSym a n = j` for odd `n` by the same run of the loop, and
`ZMod.nonsquare_of_jacobiSym_eq_neg_one` turns `jacobiSym 1001 9907 = -1` into a statement about
squares.

## See also
Mathematica `JacobiSymbol`, SymPy `jacobi_symbol`. The calls `powerMod a b m`, for Euler's
criterion `a ^ ((p - 1) / 2) ≡ (a / p) (mod p)` at an odd prime `p`, and `primeQ n`.

## Possible issues
```lean
#cas (jacobiSymbol 2 4)
```
```output
jacobiSymbol: expected an odd natural number
```
The Jacobi symbol `(a / n)` is defined for odd `n`, and the call takes only those.
-/
def jacobiSymbol : CallableFunction :=
  { name := "jacobiSymbol", usage := "jacobiSymbol a n", arity := 2,
    forms := [.bare], needsHex := false,
    summary := "Jacobi symbol" }

/-- `#cas (primeQ n)` decides with Hex whether a natural number `n` is prime and proves the
answer. The call needs Hex: it runs after `import CASHex.NumberTheory` in a build with
`-Khex=on`.

## Theorem
The report proves `Nat.Prime n` or `¬ Nat.Prime n`. A prime comes with a Pocklington certificate
from Hex's `primality`, which the kernel replays and `Hex.Nat.prime_iff` transports to
`Nat.Prime`. For a composite `n`, Hex's factor search finds a factor `d`, and `Nat.not_prime_mul`
proves `¬ Nat.Prime n` from `n = d * (n / d)`, which the report prints. `0` and `1` are not
prime by `norm_num`.

## Conditions and limits
`n` is a natural number, a literal or a closed integer expression. When Hex's test finds `n`
composite but its factor search finds no factor within its budget, the call refuses and claims
nothing. Without Hex the call refuses.

## Options
None.

## Examples
```lean
#cas (primeQ 2305843009213693951)
```
```output
Output (primality (Hex primality certificate)): True
```
```lean
#cas (primeQ 1000001)
```
```output
Output (primality (1000001 = 101*9901)): False
```

## In a proof
```lean
theorem mersenne_61_prime : Nat.Prime (2 ^ 61 - 1) := by
  cas
```
With `CASHex.Algebra` imported, bare `cas` proves `Nat.Prime n` with the same kind of
certificate, after evaluating `2 ^ 61 - 1`.

## See also
Mathematica `PrimeQ`, SymPy `isprime`. The mode `factorInteger` and the call `moebiusMu n`.

## Possible issues
```lean
#cas (primeQ 97)
```
```output
primeQ needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex;
build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
```
Without Hex the call refuses. Mathlib's `norm_num` extension `Mathlib.Tactic.NormNum.Prime`
proves `Nat.Prime n` for small `n` without Hex.
-/
def primeQ : CallableFunction :=
  { name := "primeQ", usage := "primeQ n", arity := 1,
    forms := [.bare], needsHex := true,
    summary := "primality, with a certificate from Hex" }

/-- `#cas (moebiusMu n)` computes the Möbius function `μ(n)` of a positive natural number `n` from
Hex's factorization and proves it. The call needs Hex: it runs after
`import CASHex.NumberTheory` in a build with `-Khex=on`.

## Theorem
The report proves `ArithmeticFunction.moebius n = μ` for Mathlib's Möbius function, with `μ` one
of `-1`, `0` and `1`. The proof starts from the factorization `Nat.primeFactorsList n = [p₁, …]`
of `#cas [factorInteger]`. When the `k` primes are distinct, `n` is squarefree
(`Nat.squarefree_iff_nodup_primeFactorsList`) and `μ = (-1) ^ k`
(`ArithmeticFunction.moebius_apply_of_squarefree`); a repeated prime gives `μ = 0`
(`ArithmeticFunction.moebius_eq_zero_of_not_squarefree`).

## Conditions and limits
`n` is a positive natural number, a literal or a closed integer expression, and `μ(1) = 1`.
When Hex's factor search runs out of budget, the call refuses and claims nothing. Without Hex
the call refuses.

## Options
None.

## Examples
```lean
#cas (moebiusMu 30)
```
```output
Output (Möbius function): -1
```
```lean
#cas (moebiusMu 360)
```
```output
Output (Möbius function): 0
```

## In a proof
```lean
theorem squarefree_thirty (h : ArithmeticFunction.moebius 30 = -1) : Squarefree 30 := by
  rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree, h]
  norm_num
```
A proof can take the printed theorem as a hypothesis: `μ(n) ≠ 0` says that `n` is squarefree
(`ArithmeticFunction.moebius_ne_zero_iff_squarefree`).

## See also
Mathematica `MoebiusMu`, SymPy `mobius`. The mode `factorInteger` and the calls `eulerPhi n` and
`divisorSigma k n`.

## Possible issues
```lean
#cas (moebiusMu 1001)
```
```output
moebiusMu needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex;
build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
```
Without Hex the call refuses.
-/
def moebiusMu : CallableFunction :=
  { name := "moebiusMu", usage := "moebiusMu n", arity := 1,
    forms := [.bare], needsHex := true,
    summary := "Möbius function, from Hex's factorization" }

/-- The call table, in the order of the reference. -/
def callableFunctions : List CallableFunction :=
  [chebyshevT, chebyshevU, hermiteH, hermiteHe, legendreP, bernoulliPolynomial, bernoulliNumber,
    zeta, gamma, erf, besselJ, eulerPhi, divisorSigma, binomial, factorial, fibonacci, powerMod,
    modularInverse, jacobiSymbol, primeQ, moebiusMu]

/-- The entry of the table with the name `name` and `arity` arguments. -/
def find? (name : String) (arity : Nat) : Option CallableFunction :=
  callableFunctions.find? fun f ↦ f.name == name && f.arity == arity

/-- The entries whose name is `name` up to case, or, with `pref`, starts with `name` up to case
when `name` has at least five letters. -/
def named (name : String) (pref : Bool := false) : List CallableFunction :=
  let key := name.toLower
  callableFunctions.filter fun f ↦
    f.name.toLower == key || (pref && key.length ≥ 5 && f.name.toLower.startsWith key)

/-- The commands that evaluate an entry, such as `` `#cas [N d] (erf x)` ``. -/
def commands (f : CallableFunction) : List String :=
  f.forms.map fun
    | .bare => s!"`#cas ({f.usage})`"
    | .expand => s!"`#cas [expand] ({f.usage})`"
    | .numeric => s!"`#cas [N d] ({f.usage})`"

/-- `a`, `a or b`, `a, b or c`. -/
def orList : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} or {b}"
  | a :: rest => s!"{a}, {orList rest}"

/-- The commands of an entry, with the import that a call through Hex needs. -/
def commandsText (f : CallableFunction) : String :=
  orList (commands f) ++ if f.needsHex then " with `import CASHex.NumberTheory`" else ""

/-- For a name of the table, up to case, the forms that evaluate its functions, as in
"`gamma x` is evaluated as the whole input of `#cas (gamma x)`". -/
def callHint? (name : String) : Option String :=
  match named name with
  | [] => none
  | fs => some <| "; ".intercalate <| fs.map fun f ↦
      s!"`{f.usage}` is evaluated as the whole input of {commandsText f}"

end FunctionTable

end CAS.Command
