/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Numerics

The compiled examples of the docstrings of the Numerics family: certified decimal digits,
enclosures on boxes, certified integrals and roots, and the tactics `cega` and `cega?`. Each
section pins the report lines that a docstring shows and proves its theorem, and checks the axioms
of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.Numerics

set_option linter.hashCommand false

/-! ## N -/

/--
Output (first 20 significant digits, truncated): 1.4142135623730950488
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 20] (sqrt 2)

/--
Output (first 10 significant digits, truncated): 5.859874482
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 10] (exp 1 + pi)

/--
Output (certified decimal enclosure): [0.49999999999999999999, 0.50000000000000000001]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 20] (cos (pi / 3))

theorem digits_sqrt_two : Real.sqrt 2 ≤ 1.415 := by
  cega

/--
info: 'CAS.Examples.Reference.Numerics.digits_sqrt_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms digits_sqrt_two

/--
N needs a closed expression; free symbols: x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 15] (x + 1)

/--
N accepts between 1 and 2000 digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 0] (pi)

/-! ## enclose -/

/--
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [0, 1]] (x ^ 2 + x)

/--
Output (certified interval in ℝ): [0, 1.841471]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [0, 1], y in [0, 1]] (x * y + sin y)

/--
Output (certified interval in ℝ): [-2, 2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/--
Output (certified interval in ℝ): [-1/2, 1/2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))

/--
Output (certified interval in ℝ): [0.000000, 0.000001]
Upper bound: 0.000001
Absolute bound: 0.000001
Center and radius: ≈0.000000 ± 0.000001
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose] (1 / 1000000000000000000000000)

theorem enclose_bound (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : x ^ 2 + x ≤ 2 := by
  cas

/--
info: 'CAS.Examples.Reference.Numerics.enclose_bound' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms enclose_bound

/--
no checked interval route succeeded on this box. Possible domain obstruction: check whether
denominator intervals exclude zero.
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [-1, 1]] (1 / x)

/--
interval endpoints must be exact rational literals, such as -1, 3/2, -1/10, or 0.1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [0, pi]] (sin x)

/--
interval endpoints are reversed: 1 > 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [enclose x in [1, 0]] (x)

/-! ## nintegrate -/

/--
Output (certified value of the integral): 0.746824 ± 10^-6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nintegrate x in [0, 1]] (exp (-x^2))

/--
Output (certified value of the integral): 0.45969770 ± 10^-8
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 8) [nintegrate x in [0, 1]] (sin x)

/--
Output (certified value of the integral): 0.666667 ± 10^-6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nintegrate x in [0, 1]] (sqrt x)

theorem nintegrate_gauss :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 10 ^ 6| ≤ 1 / 10 ^ 6 := by
  cega

/--
info: 'CAS.Examples.Reference.Numerics.nintegrate_gauss' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nintegrate_gauss

/--
nintegrate: the domain checker found no fourth-derivative validity certificate for the integrand
on [0, 1] and no substitution removes the singularity
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nintegrate x in [0, 1]] (1 / x)

/--
nintegrate accepts between 1 and 12 digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 16) [nintegrate x in [0, 1]] (x)

/--
nintegrate needs rational limits a < b
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nintegrate x in [1, 0]] (x)

/-! ## findRoot -/

/--
Output (certified simple root): x = 0.7390851332 ± 10^-10
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [findRoot x in [0, 1]] (cos x = x)

/--
Output (certified simple root): x = 1.09861228866810969140 ± 10^-20
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 20) [findRoot x in [0, 2]] (exp x - 3)

/--
Output (certified simple root): x = 3.1415926536 ± 10^-10
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [findRoot x in [2, 4]] (sin x)

theorem findRoot_cos : ∃ x : ℝ, Real.cos x = x ∧ 0.739 < x ∧ x < 0.74 := by
  cas

/--
info: 'CAS.Examples.Reference.Numerics.findRoot_cos' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms findRoot_cos

/--
findRoot: no sign change of the expression at 65 equally spaced points of [-1, 1]; a root of even
multiplicity, or two roots closer than the sample spacing, has no certificate here
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [findRoot x in [-1, 1]] (x^2)

/--
findRoot: the derivative cannot be evaluated on [9999999999/10000000000, 10000000001/10000000000],
where the sign changes; the expression may have a singularity there rather than a root
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [findRoot x in [0, 2]] (1 / (x - 1))

/-! ## cega -/

example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega

example : Real.exp 1 ≤ 2.72 := by
  cega

example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega

theorem cega_sin_lt_one (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x < 1 := by
  have h : Real.sin x ≤ 17 / 20 := by cega
  linarith

/--
info: 'CAS.Examples.Reference.Numerics.cega_sin_lt_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cega_sin_lt_one

/--
cega box route: comparison with the stated bound: the certified value does not give the stated
bound.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega

/--
cega box route: no rational bounds on `x` in the hypotheses; the route needs hypotheses `a ≤ x` and
`x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r` with rational literal endpoints
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega

/-! ## cega? -/

/--
Try this: [apply] cega [enclose x in [0, 1]] (Real.sin x)
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?

/--
Try this: [apply] cega [enclose] (√2)
-/
#guard_msgs (whitespace := lax, substring := true) in
example : Real.sqrt 2 ≤ 1.415 := by
  cega?

theorem cega_sin_bound (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega [enclose x in [0, 1]] (Real.sin x)

/--
info: 'CAS.Examples.Reference.Numerics.cega_sin_bound' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cega_sin_bound

/--
cega box route: no rational bounds on `x` in the hypotheses
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega?

end CAS.Examples.Reference.Numerics
