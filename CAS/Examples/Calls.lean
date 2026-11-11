/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
meta import CAS.Command.Arguments
meta import CAS.Command.Gamma
meta import CAS.Command.NumberTheory.Functions

/-!
# Calls of special and number-theoretic functions: `#cas e`

`#cas` evaluates a function of the call table when the call is the whole input: a family of
polynomials in a variable or at a rational point, a Bernoulli number, a value of `ζ` or `Γ`, and
the number-theoretic functions at closed integer expressions. Each command runs in the build
inside `#guard_msgs`, which checks its report, and each report's theorem is kernel-checked when
the command runs. The arguments keep the ascriptions `ℕ` and `ℤ` with Lean's arithmetic. A call
is refused when evaluating an argument needs a number with more than 10000 digits, and so is a
value with more digits. The pins show the largest power of ten that an argument may reach and
the first one refused, also as a denominator and with a negative exponent, and values of
`ChebyshevT` and `LegendreP` above that bound. The modes `limit`, `nintegrate`, `findRoot`,
`dsolve` and `sum` read their rational numbers with the same guard, with a pin each, and
`(10 ^ 10000) / 0` is refused for its size before its division by zero. The `#guard` lines check
at the bound the products, sums and powers of the guard, rational sums and polynomial values
that are refused although their value is below the bound, the values of `binomial` and
`fibonacci`, the range of `gamma`, and the tests of decimal literals. The refusals show a call
inside a larger expression, the functions whose values have digits only, modes named after
functions, and a section variable that hides a function, in each of the three forms. The axioms
of the library theorems behind the certificates are checked at the end.
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CAS.Examples.Calls

/-! ## Polynomials, numbers and values -/

/--
info: #cas (ChebyshevT 5 x)
Domain: Polynomial.Chebyshev.T R 5, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 5 x
Output (polynomial with integer coefficients): 16*x^5 - 20*x^3 + 5*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (ChebyshevT 5 x)

set_option linter.style.longLine false in
/--
info: #cas [expand]
Domain: Polynomial.Chebyshev.T R 5, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 5 x
Output (polynomial with integer coefficients): 16*x^5 - 20*x^3 + 5*x

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of ChebyshevT 5
        Proposition: ∀ (R : Type) [inst : CommRing R],
          Polynomial.Chebyshev.T R 5 = 16 * Polynomial.X ^ 5 - 20 * Polynomial.X ^ 3 + 5 * Polynomial.X
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [expand] (ChebyshevT 5 x)

/--
info: #cas (BernoulliB 4 x)
Domain: Polynomial.bernoulli 4, x ∈ ℝ
Input (polynomial in x): BernoulliB 4 x
Output (polynomial with exact rational coefficients): x^4 - 2*x^3 + x^2 - 1/30

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (BernoulliB 4 x)

/--
info: #cas (BernoulliB 4)
Domain: ℚ (Mathlib's bernoulli, B₁ = -1/2)
Input (natural number): 4
Output (Bernoulli number): -1/30

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bernoulli number from the kernel-evaluated numerators
        Proposition: bernoulli 4 = -(1 / 30)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 4)

/--
info: #cas (zeta 4)
Domain: ℂ (Mathlib's riemannZeta)
Input (even positive integer): s = 4
Output (exact value of ζ): pi^4/90

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (zeta 4)

/--
info: #cas (gamma (5/2))
Domain: ℝ
Input (rational number): 5/2
Output (exact value of Γ): 3√π/4

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Gamma by a closed formula
        Proposition: Real.Gamma (5 / 2) = 3 * √Real.pi / 4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (gamma (5/2))

/--
info: #cas [N 2]
Domain: Legendre polynomial at a rational point
Input (scalar ℝ): (LegendreP 1 (1/3))
Output (exact rational value and its first 2 significant digits, truncated): 1/3 ≈ 0.33

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of the Legendre polynomial
        Proposition: Polynomial.eval (1 / 3) (Analysis.SpecialFunctions.legendre 1) = 1 / 3 ∧
          33 / 10 ^ 2 ≤ Polynomial.eval (1 / 3) (Analysis.SpecialFunctions.legendre 1) ∧
            Polynomial.eval (1 / 3) (Analysis.SpecialFunctions.legendre 1) < (33 + 1) / 10 ^ 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: Analysis.SpecialFunctions.legendre_eval_ratCast
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 2] (LegendreP 1 (1/3))

/-! ## Number theory -/

/--
info: #cas (eulerPhi 100)
Domain: ℕ
Input (natural numbers): 100
Output (eulerPhi): 40

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] eulerPhi
        Proposition: Nat.totient 100 = 40
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (eulerPhi 100)

/--
info: #cas (binomial 10 3)
Domain: ℕ
Input (natural numbers): (10, 3)
Output (binomial): 120

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] binomial
        Proposition: Nat.choose 10 3 = 120
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (binomial 10 3)

/--
info: #cas (powerMod 2 100 7)
Domain: ℕ
Input (natural numbers): 2^100 mod 7
Output (modular power): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (powerMod 2 100 7)

/--
info: #cas (jacobiSymbol 2 7)
Domain: ℤ × ℕ
Input (an integer and an odd natural number): (2 / 7)
Output (Jacobi symbol): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (jacobiSymbol 2 7)

/--
info: #cas [chineseRemainder]
Domain: ℕ
Input (natural numbers): x ≡ 2 mod 4, x ≡ 4 mod 6
Output (all solutions): 10 mod 12

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [chineseRemainder] ([2, 4], [4, 6])

/-! ## Arguments -/

/--
info: #cas (eulerPhi (2 ^ 10))
Domain: ℕ
Input (natural numbers): 1024
Output (eulerPhi): 512

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi (2 ^ 10))

/--
info: #cas (eulerPhi 0)
Domain: ℕ
Input (natural numbers): 0
Output (eulerPhi): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi 0)

/--
error: binomial takes integer arguments; `x` is a variable
-/
#guard_msgs in
#cas (binomial x 2)

/--
error: factorial takes a natural number as its argument; `-1` is negative
-/
#guard_msgs in
#cas (factorial (-1))

/--
info: #cas (factorial ((1 - 2 : ℕ) + 3))
Domain: ℕ
Input (natural numbers): 3
Output (factorial): 6

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] factorial
        Proposition: Nat.factorial 3 = 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (factorial ((1 - 2 : ℕ) + 3))

/--
info: #cas (factorial ((1 - 2 : ℤ) + 3))
Domain: ℕ
Input (natural numbers): 2
Output (factorial): 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] factorial
        Proposition: Nat.factorial 2 = 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (factorial ((1 - 2 : ℤ) + 3))

set_option linter.style.longLine false in
/--
error: factorial takes integer arguments; `(3 : ℝ)` has the type `ℝ`, and the ascriptions of an integer argument are `ℕ` and `ℤ`
-/
#guard_msgs in
#cas (factorial (3 : ℝ))

set_option linter.style.longLine false in
/--
error: eulerPhi takes integer arguments; `gamma x` is evaluated as the whole input of `#cas (gamma x)`
-/
#guard_msgs in
#cas (eulerPhi (gamma 3))

/-! ## Sizes of arguments and values -/

set_option linter.style.longLine false in
/--
info: #cas (gamma (399/2))
Domain: ℝ
Input (rational number): 399/2
Output (exact value of Γ): 126634928415063002907386656246666444756189908127894071659926333805593037190761437661599253712171855951423439053112483233406868541451318045491422893066878730339267816576787611905432539107137405297173653051577379270223256612665030115129031322016960495379733752681493082057706547109082546766125930746012803055422332823761685050933542751171579061287248881318569795579039659568289560971969986916929723630431681158370338380336761474609375√π/803469022129495137770981046170581301261101496891396417650688
-/
#guard_msgs (info, substring := true) in
#cas (gamma (399/2))

set_option linter.style.longLine false in
/--
info: #cas (gamma (1001/2))
Domain: ℝ
Input (rational number): 1001/2
Output (exact value of Γ): 100748329763750854004038917392303538250323418583550415705013777513334847930864905026212149922688916514224446856302103818809813965739969905602683824057028542369814437703275217182106137628427025253936696857063927677887236450311036887007989218384076420973974651860279864376153012567675767840733574225799002463604490891982796305162134708837541147007332276627034016790073315219533088052639255340728943149219519187498959529434982654113006616219355830114439411562650611374970334868978510289340267833632215930432706056111069583472778227977585526504938921664232801595705593340414168289146933191250605578218896799783237156997993612173843567447982392426109444012350386990916069363415575527636429080027392875413821124412782341957015410685185402984322002697631153866494712956244870206835064084512590679022924697003630949759950902438767963278695296882620493296103779237046934780464541286585179975172680371269700518965123152181467825566303777704391998857792627009043170482928030252033752456172692668989206857862233381387134495504231267039972111966329704875185659372569246229419619030694680808504265784672316785572965414328005856656944666840982779185954031239345256896720409853053597049715408663604581472840976596002762935980048845023622727663267632821809277089697420848324327380396425724029541015625√π/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376
-/
#guard_msgs (info, substring := true) in
#cas (gamma (1001/2))

/--
error: gamma: exact values are computed for |q| ≤ 1001/2; `1003/2` is outside that range
-/
#guard_msgs in
#cas (gamma (1003/2))

/--
error: gamma: exact values are computed for |q| ≤ 1001/2; `10 ^ 9999` is outside that range
-/
#guard_msgs in
#cas (gamma (10 ^ 9999))

/--
error: gamma: exact values are computed for |q| ≤ 1001/2; `6 * 10 ^ 9999` is outside that range
-/
#guard_msgs in
#cas (gamma (6 * 10 ^ 9999))

set_option linter.style.longLine false in
/--
error: gamma: evaluating `10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas (gamma (10 ^ 10000))

set_option linter.style.longLine false in
/--
error: gamma: evaluating `10 ^ 10000000000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas (gamma (10 ^ 10000000000))

-- An exponent that is not a numeral makes a real power, which is not a rational expression.
/--
error: gamma: expected a rational number
-/
#guard_msgs in
#cas (gamma (10 ^ (10 ^ 10)))

/--
error: gamma: exact values are computed at integers and half-integers; `1 / 10 ^ 9999` is neither
-/
#guard_msgs in
#cas (gamma (1 / 10 ^ 9999))

set_option linter.style.longLine false in
/--
error: gamma: evaluating `1 / 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas (gamma (1 / 10 ^ 10000))

-- A negative literal exponent is a reciprocal: `10 ^ (-9999)` is `1 / 10 ^ 9999`.
/--
error: gamma: exact values are computed at integers and half-integers; `10 ^ (-9999)` is neither
-/
#guard_msgs in
#cas (gamma (10 ^ (-9999)))

set_option linter.style.longLine false in
/--
error: gamma: evaluating `10 ^ (-10000)` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas (gamma (10 ^ (-10000)))

set_option linter.style.longLine false in
/--
error: gamma: evaluating `1 / 10 ^ 5000 / 10 ^ 5000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas (gamma (1 / 10 ^ 5000 / 10 ^ 5000))

/--
info: #cas (eulerPhi (10 ^ 9000 / 10 ^ 8998))
Domain: ℕ
Input (natural numbers): 100
Output (eulerPhi): 40

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi (10 ^ 9000 / 10 ^ 8998))

/--
info: #cas (eulerPhi (10 ^ 9999 / 10 ^ 9997))
Domain: ℕ
Input (natural numbers): 100
Output (eulerPhi): 40

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi (10 ^ 9999 / 10 ^ 9997))

/--
error: eulerPhi: `10 ^ 10000` has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (eulerPhi (10 ^ 10000 / 10 ^ 9998))

/--
error: eulerPhi: `10 ^ 5000 * 10 ^ 5000` has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (eulerPhi (10 ^ 5000 * 10 ^ 5000 / 10 ^ 9998))

/--
error: eulerPhi: `1e100000000000` has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (eulerPhi 1e100000000000)

/--
error: eulerPhi takes integer arguments; `1e-100000000000` is not an integer
-/
#guard_msgs in
#cas (eulerPhi 1e-100000000000)

/--
error: factorial: the value has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (factorial 5000)

/--
error: fibonacci: the value has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (fibonacci 47852)

/--
error: binomial: the value has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (binomial 100000 50000)

/--
error: divisorSigma: the value has more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (divisorSigma 4000 999999937)

set_option linter.style.longLine false in
/--
error: ChebyshevT: evaluating `ChebyshevT 2 (10 ^ 5000)` needs a number with more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (ChebyshevT 2 (10 ^ 5000))

set_option linter.style.longLine false in
/--
error: LegendreP: evaluating `LegendreP 2 (10 ^ 5000)` needs a number with more than 10000 digits, the most that a call computes
-/
#guard_msgs in
#cas (LegendreP 2 (10 ^ 5000))

set_option linter.style.longLine false in
/--
error: N: evaluating `10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [N 5] (BesselJ 0 (10 ^ 10000))

/-! ## Rational numbers of the modes -/

-- The modes read their points, bounds and initial values as `gamma` reads its argument
-- (`SpecialFunctions.parseRational`), so `10 ^ 10000 - 10 ^ 10000` is refused in each of them.
set_option linter.style.longLine false in
/--
error: limit: evaluating `10 ^ 10000 - 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [limit x → (10 ^ 10000 - 10 ^ 10000)] (x + 1)

set_option linter.style.longLine false in
/--
error: nintegrate: evaluating `10 ^ 10000 - 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [nintegrate x in [(10 ^ 10000 - 10 ^ 10000), 1]] (exp x)

set_option linter.style.longLine false in
/--
error: findRoot: evaluating `10 ^ 10000 - 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [findRoot x in [(10 ^ 10000 - 10 ^ 10000), 2]] (x^2 - 2)

set_option linter.style.longLine false in
/--
error: dsolve: evaluating `10 ^ 10000 - 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [dsolve y x, y 0 = (10 ^ 10000 - 10 ^ 10000), y' 0 = 1] (y'' + y = 0)

set_option linter.style.longLine false in
/--
error: sum: evaluating `10 ^ 10000 - 10 ^ 10000` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [sum k (10 ^ 10000 - 10 ^ 10000) 10] (k^2)

-- The evaluation starts at the leaves, so the numerator `10 ^ 10000` is refused before the
-- division by `0` is reached.
set_option linter.style.longLine false in
/--
error: limit: evaluating `(10 ^ 10000) / 0` needs a number with more than 10000 digits, the most that a rational argument may use
-/
#guard_msgs in
#cas [limit x → ((10 ^ 10000) / 0)] (x + 1)

section Guard

open CAS.Command.Arguments

-- A product, a sum or a power just below `10 ^ 10000` is formed and the first one at the bound
-- is refused; a rational product cancels before it multiplies.
#guard mulBelow? (10 ^ 5000) (10 ^ 5000) = none
#guard mulBelow? (10 ^ 5000 - 1) (10 ^ 5000) = some ((10 ^ 5000 - 1) * 10 ^ 5000)
#guard mulBelow? 3 ((10 ^ 10000 - 1) / 3) = some (10 ^ 10000 - 1)
#guard mulBelow? 3 ((10 ^ 10000 - 1) / 3 + 1) = none
#guard addBelow? (10 ^ 10000 - 2) 1 = some (10 ^ 10000 - 1)
#guard addBelow? (10 ^ 10000 - 1) 1 = none
#guard intAddBelow? (-(10 ^ 10000 - 2)) (-1) = some (-(10 ^ 10000 - 1))
#guard intAddBelow? (-(10 ^ 10000 - 1)) (-1) = none
#guard intAddBelow? (10 ^ 10000 - 1) (-1) = some (10 ^ 10000 - 2)
#guard intMulBelow? (-3) ((10 ^ 10000 - 1) / 3) = some (-(10 ^ 10000 - 1))
#guard powBelow? 10 9999 = some (10 ^ 9999)
#guard powBelow? 10 10000 = none
#guard powBelow? 2 33219 = some (2 ^ 33219)
#guard powBelow? 2 33220 = none
#guard ratMulBelow? ((10 ^ 6000 + 1) / 10 ^ 6000) (10 ^ 6000 / (10 ^ 6000 + 1)) = some 1
#guard ratMulBelow? (1 / 10 ^ 5000) (1 / 10 ^ 5000) = none

-- A rational sum is refused when a cross product, their sum or the least common denominator
-- reaches the bound, also when the sum in lowest terms is below it, as
-- `(10 ^ 10000 - 1) / 2 + 1 / 2 = 5 * 10 ^ 9999` is.
#guard ratAddBelow? (10 ^ 9999) (1 / 10) = none
#guard ratAddBelow? ((10 ^ 10000 - 1) / 2) (1 / 2) = none
#guard ratAddBelow? ((10 ^ 10000 - 3) / 2) (1 / 2) = some (5 * 10 ^ 9999 - 1)
#guard ratAddBelow? (1 / 10 ^ 5000) (1 / (10 ^ 5000 + 1)) = none
#guard ratAddBelow? (-(10 ^ 10000 - 2)) (-1) = some (-(10 ^ 10000 - 1))
#guard ratAddBelow? (-(10 ^ 10000 - 1)) (-1) = none

-- The bound holds for the numerator and the denominator of a negative number, and a power of a
-- negative fraction keeps its sign.
#guard (ratBelow? (-(10 ^ 10000 - 1))).isSome
#guard ratBelow? (-(10 ^ 10000)) = none
#guard (ratBelow? (-1 / (10 ^ 10000 - 1))).isSome
#guard ratBelow? (-1 / 10 ^ 10000) = none
#guard ratPowBelow? (-1 / 10) 9999 = some (-1 / 10 ^ 9999)
#guard ratPowBelow? (-1 / 10) 10000 = none

-- A polynomial value is refused when a partial sum reaches the bound: the first two terms of
-- `(10 ^ 10000 - 1) + q - q ^ 2` at `q = 1` sum to `10 ^ 10000`, although the value is below it.
#guard polyEvalBelow? [10 ^ 10000 - 1, 1, -1] 1 = none
#guard polyEvalBelow? [10 ^ 10000 - 1, -1, 1] 1 = some (10 ^ 10000 - 1)

-- `binomial` forms each `C(n, i + 1)` from `C(n, i)` by dividing before it multiplies, so
-- `C(10 ^ 5000 + 1, 2)` is formed as `(10 ^ 5000 + 1) (10 ^ 5000 / 2)`, below the bound, and not
-- from `(10 ^ 5000 + 1) 10 ^ 5000`, which is not. `C(33227, 16613)` and `F_47851` are below the
-- bound, and `C(33228, 16614)` and `F_47852` are not.
#guard Command.NumberTheory.chooseBelow? (10 ^ 5000 + 1) 2 =
    some ((10 ^ 5000 + 1) * (10 ^ 5000 / 2))
#guard (Command.NumberTheory.chooseBelow? 33227 16613).isSome
#guard Command.NumberTheory.chooseBelow? 33228 16614 = none
#guard (Command.NumberTheory.fibonacciBelow? 47851).isSome
#guard Command.NumberTheory.fibonacciBelow? 47852 = none

-- The range `|q| ≤ 1001/2` of `gamma` is decided by the integer part of `|q|` and its remainder,
-- also next to `1001/2`, where `2 |num q|` and `1001 den q` have `10001` digits.
#guard Command.Gamma.inRange (1001 / 2)
#guard Command.Gamma.inRange (-1001 / 2)
#guard !Command.Gamma.inRange (1003 / 2)
#guard !Command.Gamma.inRange (6 * 10 ^ 9999)
#guard Command.Gamma.inRange ((5005 * 10 ^ 9996 - 1) / 10 ^ 9997)
#guard !Command.Gamma.inRange ((5005 * 10 ^ 9996 + 1) / 10 ^ 9997)

-- A decimal literal `m × 10 ^ (±e)` is refused by its mantissa `m` and, with a positive power,
-- by the number of digits of `m` plus `e`, before its value is formed; `oversizedDecimal?`
-- finds such a literal inside an argument.
#guard decimalRefusal? (10 ^ 10000) true 10000 = some .mantissa
#guard decimalRefusal? (10 ^ 10000 - 1) true 10000 = none
#guard decimalRefusal? (10 ^ 9999) false 1 = some .value
#guard decimalRefusal? (10 ^ 9998) false 1 = none
#guard decimalRefusal? 1 false 10000 = some .value
#guard decimalRefusal? 1 false 9999 = none
#guard decimalRefusal? 0 false 100000 = none
#guard (oversizedDecimal? (Lean.Syntax.mkScientificLit ("1." ++ "".pushn '0' 10000)).raw).map
    Prod.snd = some .mantissa
#guard (oversizedDecimal? (Lean.Syntax.mkScientificLit "1e9999").raw).isNone
#guard (oversizedDecimal? (Lean.Syntax.node .none `term #[(Lean.Syntax.mkNumLit "2").raw,
    (Lean.Syntax.mkScientificLit "1e10000").raw])).map Prod.snd = some .value

end Guard

/-! ## Parsing next to the modes -/

/--
info: #cas (digits := 30) [findRoot x in [1, 2]]
Domain: x ∈ [1, 2]
Input (scalar ℝ): (x^2 - 2)
Output (certified simple root): x = 1.4142135623730950488
-/
#guard_msgs (info, substring := true) in
#cas (digits := 30) [findRoot x in [1, 2]] (x^2 - 2)

/-! ## Refusals -/

set_option linter.style.longLine false in
/--
error: unsupported symbolic function 'gamma'; expected abs, sin, cos, tan, sinh, cosh, tanh, atan/arctan, asin/arcsin, acos/arccos, exp, log, or sqrt. `gamma x` is evaluated as the whole input of `#cas (gamma x)`
-/
#guard_msgs in
#cas (2 * gamma (5/2))

/--
error: `#cas` computes no exact value of `BesselJ n x`; `#cas [N d] (BesselJ n x)` gives its digits
-/
#guard_msgs in
#cas (BesselJ 0 1)

/--
error: `gamma` is no mode of `#cas`; write `#cas (gamma x)`
-/
#guard_msgs in
#cas [gamma] (5/2)

set_option linter.style.longLine false in
/--
error: `LegendreP` is no mode of `#cas`; write `#cas (LegendreP n x)`, `#cas [expand] (LegendreP n x)` or `#cas [N d] (LegendreP n x)`
-/
#guard_msgs in
#cas [LegendreP 5]

/--
error: `primeQ` is no mode of `#cas`; write `#cas (primeQ n)` with `import CASHex.NumberTheory`
-/
#guard_msgs in
#cas [primeQ] 97

section

variable (gamma : ℝ → ℝ)

set_option linter.style.longLine false in
/--
error: `gamma` is a variable of the section, which hides the function `gamma` of `#cas`; rename the variable to evaluate the function
-/
#guard_msgs in
#cas (gamma (5/2))

end

section

variable (ChebyshevT : ℕ → ℝ → ℝ)

set_option linter.style.longLine false in
/--
error: `ChebyshevT` is a variable of the section, which hides the function `ChebyshevT` of `#cas`; rename the variable to evaluate the function
-/
#guard_msgs in
#cas [expand] (ChebyshevT 5 x)

end

section

variable (LegendreP : ℕ → ℝ → ℝ)

set_option linter.style.longLine false in
/--
error: `LegendreP` is a variable of the section, which hides the function `LegendreP` of `#cas`; rename the variable to evaluate the function
-/
#guard_msgs in
#cas [N 10] (LegendreP 2 (1/2))

end

section

variable (y : ℝ)

set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf (1/2))
Output (decimal enclosure of width at most 10^-10, with 10 terms of the series): [0.52049987781, 0.52049987782]
-/
#guard_msgs (info, substring := true) in
#cas [N 10] (erf (1/2))

end

/-! ## Axioms of the library theorems -/

/--
info: 'CAS.NumberTheory.divisors_eq_of_cert' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.divisors_eq_of_cert

/--
info: 'CAS.NumberTheory.sigma_eq_of_cert' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.sigma_eq_of_cert

/--
info: 'CAS.NumberTheory.toFinset_eq_insertChain' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.toFinset_eq_insertChain

/--
info: 'CAS.NumberTheory.toFinset_append_eq_insertAll' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.toFinset_append_eq_insertAll

/--
info: 'CAS.NumberTheory.totient_eq_rangeSum' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.totient_eq_rangeSum

/--
info: 'CAS.NumberTheory.totient_eq_of_primeFactorsList' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.totient_eq_of_primeFactorsList

/--
info: 'CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop

/--
info: 'CAS.NumberTheory.modEq_iff_of_lcm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.modEq_iff_of_lcm

/--
info: 'CAS.NumberTheory.not_exists_of_incompatible' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.NumberTheory.not_exists_of_incompatible

/--
info: 'CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat

end CAS.Examples.Calls
