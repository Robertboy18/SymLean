/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Sums, products and recurrences

The compiled examples of the docstrings of the Sums family: finite sums in closed form or by
value, series, finite products, and linear recurrences. Each section pins the report lines that a
docstring shows and proves its theorem, and checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.Sums

set_option linter.hashCommand false

/-! ## sum -/

/--
Output (closed form): n*(n + 1)*(2*n + 1)/6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 n] (k^2)

/--
Output (closed form (Gosper)): n/(n + 1)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 n] (1 / (k * (k + 1)))

/--
Output (sum of the series (ζ value)): pi^2/6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 ∞] (1/k^2)

theorem sum_squares :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  cas

/--
info: 'CAS.Examples.Reference.Sums.sum_squares' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_squares

/--
sum: Gosper's algorithm finds no closed form in hypergeometric terms for this summand
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 n] (1 / k)

/--
Output (exact value): 7381/2520
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 10] (1 / k)

/--
sum: the summand is not a sum of terms c k ^ j r ^ k with rational c and r
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [sum k 1 n] (sin k)

/-! ## product -/

/--
Output (closed form): (n + 1)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [product k 1 n] ((k + 1) / k)

/--
Output (closed form): 2^n*n!
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [product k 1 n] (2*k)

theorem product_telescoping : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, ((k : ℝ) + 1) / k = n + 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Sums.product_telescoping' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms product_telescoping

/--
product: the upper bound must be a variable
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [product k 1 5] (k)

/--
product: the factor is not, as written, a constant times powers of linear factors k + s with
integer s, and without Hex `product` does not factor it: write it as such a product, or use
CASHex (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely
over ℚ
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [product k 2 n] (1 - 1 / k ^ 2)

/--
product: the expression is not a rational function: it has a function other than the field
operations and natural powers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [product k 1 n] (sin k)

/-! ## rsolve -/

/--
Output (the sequence with these initial values): a n = -1 + 2*2^n
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rsolve a n, a 0 = 1] (a (n + 1) = 2 * a n + 1)

/--
Output (general solution): a n = c₁*2^n + c₂*3^n
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rsolve a n] (a (n + 2) = 5 * a (n + 1) - 6 * a n)

theorem rsolve_closed_form (a : ℕ → ℝ) (h : ∀ n, a (n + 1) = 2 * a n + 1) (h₀ : a 0 = 1) :
    ∀ n, a n = -1 + 2 * 2 ^ n := by
  intro n
  induction n with
  | zero =>
    rw [h₀]
    norm_num
  | succ n ih =>
    rw [h, ih]
    ring

/--
info: 'CAS.Examples.Reference.Sums.rsolve_closed_form' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rsolve_closed_form

/--
rsolve: the terms in n must be sums of c n^j r^n
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rsolve a n] (a (n + 1) = a n + sin n)

/--
rsolve: the equation is about the sequence b, but the mode names a; write #cas [rsolve b n]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rsolve a n] (b (n + 1) = 2 * b n)

/--
rsolve: give the 2 initial values a k, …, a (k + 1) at consecutive indices
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rsolve a n, a 0 = 1] (a (n + 2) = 5 * a (n + 1) - 6 * a n)

end CAS.Examples.Reference.Sums
