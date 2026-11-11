/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified decimal digits

`#cas [N d] e` is the checked analogue of Mathematica's `N[e, d]`: it prints the first `d`
significant digits of a closed real expression and proves that they are the digits of the true
value, truncated toward zero. The evaluator `DigitsEval.eval` uses Machin's formula in fixed point
for `π`, FloatLib's series kernels for the elementary functions, and outward rounding to a binary
grid whose size follows `d`. Each command runs in the build inside `#guard_msgs`, which checks its
report.

The first outputs are `3.1415926535897932384626433832795028841971693993751`,
`0.841470984807896506652502321630`, `2.6881171418161354484 × 10^43`,
`-0.6931471805599453094172321`, `0.433883739117558120475768332848`,
`0.523598775598298873077107230546` and `1.25992104989487316476721060727`. The report of the
first one states the theorem

`31415926535897932384626433832795028841971693993751 / 10 ^ 49 ≤ Real.pi ∧`
`Real.pi < (31415926535897932384626433832795028841971693993751 + 1) / 10 ^ 49`,

checked by the kernel. The 300-digit sum and the 1000 digits of `π` take about 2 s and 0.2 s of
checking. The value `cos (π / 3) = 1 / 2` has a finite decimal expansion, so no enclosure
separates its digits from those of the neighbouring decimals; the command reports the certified
enclosure `[0.49999999999999999999, 0.50000000000000000001]` instead. The last command fails
because `x` is a free symbol.

The same theorems can be stated directly. The comparison of the enclosure with the two decimal
bounds is a closed Boolean check, proved by `cega` in the kernel.
-/

public section

namespace CAS.Examples.Digits

open CAS CAS.Continuum

/-- Fifty digits of `π`, from Machin's formula in fixed point at 206 bits. -/
theorem pi_fifty_digits :
    (31415926535897932384626433832795028841971693993751 / 10 ^ 49 : ℝ) ≤ Real.pi ∧
      Real.pi < (31415926535897932384626433832795028841971693993751 + 1) / 10 ^ 49 := by
  simpa using DigitsEval.of_lowerCheck_decimal (p := ⟨206, 74, 150⟩) (expr := .pi)
    (m := 31415926535897932384626433832795028841971693993751) (k := 49) (by cega) Fin.elim0

/-- Twenty-five digits of `-log 2`, a negative value. -/
theorem neg_log_two_digits :
    -((6931471805599453094172321 : ℝ) + 1) / 10 ^ 25 < -Real.log 2 ∧
      -Real.log 2 ≤ -(6931471805599453094172321 : ℝ) / 10 ^ 25 := by
  simpa using DigitsEval.of_upperCheck_decimal (p := ⟨246, 98, 150⟩)
    (expr := .neg (.log (.nat 2))) (m := 6931471805599453094172321) (k := 25) (by cega) Fin.elim0

/-- The leading digits of `exp 100 ≈ 2.6881171418161354484 × 10 ^ 43`. -/
theorem exp_hundred_digits :
    (26881171418161354484 : ℝ) * 10 ^ 24 ≤ Real.exp 100 ∧
      Real.exp 100 < ((26881171418161354484 : ℝ) + 1) * 10 ^ 24 := by
  simpa using DigitsEval.of_lowerCheck_scaled (p := ⟨106, 44, 84⟩) (expr := .exp (.nat 100))
    (m := 26881171418161354484) (k := 24) (by cega) Fin.elim0

end CAS.Examples.Digits

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [N 50]
Domain: closed real expression
Input (scalar ℝ): (pi)
Output (first 50 significant digits, truncated): 3.1415926535897932384626433832795028841971693993751

[CAS.Command.details] More details
  [CAS.Command.computation] Certified numerical evaluation
    Working precision: 206 bits, 74 series terms, 150 logarithm terms
    Guarantee: every printed digit is a digit of the real value, truncated toward zero
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Certified decimal digits
        Proposition: 31415926535897932384626433832795028841971693993751 / 10 ^ 49 ≤ Real.pi ∧
          Real.pi < (31415926535897932384626433832795028841971693993751 + 1) / 10 ^ 49
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.DigitsEval.eval_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 50] (pi)

/--
info: #cas [N 30]
Domain: closed real expression
Input (scalar ℝ): (sin 1)
Output (first 30 significant digits, truncated): 0.841470984807896506652502321630

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 30] (sin 1)

/--
info: #cas [N 20]
Domain: closed real expression
Input (scalar ℝ): (exp 100)
Output (first 20 significant digits, truncated): 2.6881171418161354484 × 10^43

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 20] (exp 100)

/--
info: #cas [N 25]
Domain: closed real expression
Input (scalar ℝ): (-log 2)
Output (first 25 significant digits, truncated): -0.6931471805599453094172321

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 25] (-log 2)

/--
info: #cas [N 30]
Domain: closed real expression
Input (scalar ℝ): (sin (π / 7))
Output (first 30 significant digits, truncated): 0.433883739117558120475768332848

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 30] (sin (π / 7))

/--
info: #cas [N 30]
Domain: closed real expression
Input (scalar ℝ): (arcsin (1 / 2))
Output (first 30 significant digits, truncated): 0.523598775598298873077107230546

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 30] (arcsin (1 / 2))

/--
info: #cas [N 30]
Domain: closed real expression
Input (scalar ℝ): (2 ^ (1 / 3 : ℝ))
Output (first 30 significant digits, truncated): 1.25992104989487316476721060727

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 30] (2 ^ (1 / 3 : ℝ))

set_option linter.style.longLine false in
/--
info: #cas [N 300]
Domain: closed real expression
Input (scalar ℝ): (atan (1 / 3) + log 3 + sqrt 5)
Output (first 300 significant digits, truncated): 3.65643082056454158120582352001246325910886421299193136743839463840477145626222441064443858554315573819648537459386138839488891492114022808709897127438874477811317570188586506173453749933481224970001993360693795193609358292427113064810405454135244817702178963767078617812879198286504956882974228782178

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 300] (atan (1 / 3) + log 3 + sqrt 5)

set_option linter.style.longLine false in
/--
info: #cas [N 1000]
Domain: closed real expression
Input (scalar ℝ): (pi)
Output (first 1000 significant digits, truncated): 3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148086513282306647093844609550582231725359408128481117450284102701938521105559644622948954930381964428810975665933446128475648233786783165271201909145648566923460348610454326648213393607260249141273724587006606315588174881520920962829254091715364367892590360011330530548820466521384146951941511609433057270365759591953092186117381932611793105118548074462379962749567351885752724891227938183011949129833673362440656643086021394946395224737190702179860943702770539217176293176752384674818467669405132000568127145263560827785771342757789609173637178721468440901224953430146549585371050792279689258923542019956112129021960864034418159813629774771309960518707211349999998372978049951059731732816096318595024459455346908302642522308253344685035261931188171010003137838752886587533208381420617177669147303598253490428755468731159562863882353787593751957781857780532171226806613001927876611195909216420198

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 1000] (pi)

/--
info: #cas [N 20]
Domain: closed real expression
Input (scalar ℝ): (cos (pi / 3))
Output (certified decimal enclosure): [0.49999999999999999999, 0.50000000000000000001]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [N 20] (cos (pi / 3))

-- Under `open Real`, `π` is Mathlib's notation for `Real.pi`.
open Real in
/--
info: #cas [N 15]
Domain: closed real expression
Input (scalar ℝ): (π / 4)
Output (first 15 significant digits, truncated): 0.785398163397448
-/
#guard_msgs (info, substring := true) in
#cas [N 15] (π / 4)

/--
error: N needs a closed expression; free symbols: x
-/
#guard_msgs in
#cas [N 15] (x + 1)

