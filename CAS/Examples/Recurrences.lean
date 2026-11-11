/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Finite products and linear recurrences: `#cas [product]`, `#cas [rsolve]`

Each command runs in the build inside `#guard_msgs`, which checks its report; each report's theorem
is kernel-checked when the command runs. The Fibonacci recurrence gets Binet's formula with `√5`
as an equivalence: a sequence satisfies the recurrence and the initial values exactly when it is
the closed form. Without initial values the theorem is the general solution, a family with one
real parameter per characteristic root. Both come from `LinearRecurrence.rec_general` and
`LinearRecurrence.rec_ivp`, whatever the roots: rational, quadratic surds, complex pairs in real
form, or roots known only by certified enclosures, as for the Padovan recurrence
`a (n + 3) = a (n + 1) + a n`, whose characteristic polynomial `r ^ 3 - r - 1` is irreducible.

The recurrence theorems assume the recurrence for every `n`, as stated: a sequence that satisfies
it only from some index on is not covered.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- Product
/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): ((k + 1) / k)
Output (closed form): (n + 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Closed form for every upper bound
        Proposition: ∀ (n : ℕ), ∏ k ∈ Finset.Icc 1 n, (↑k + 1) / ↑k = ↑n + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [product k 1 n] ((k + 1) / k)

/--
info: #cas [product k 2 n]
Domain: k ∈ [2, n]
Input (factor): ((k - 1)*(k + 1)/k^2)
Output (closed form): (n + 1)/(2*n) for n ≥ 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Closed form for every upper bound n ≥ 1
        Proposition: ∀ (n : ℕ), 1 ≤ n → ∏ k ∈ Finset.Icc 2 n, (↑k - 1) * (↑k + 1) / ↑k ^ 2 = (↑n +
1) / (2 * ↑n)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [product k 2 n] ((k - 1)*(k + 1)/k^2)

/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): (k)
Output (closed form): n!

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] (k)

/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): (2*k)
Output (closed form): 2^n*n!

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] (2*k)

/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): (k * (k + 1))
Output (closed form): n!*(n + 1)!

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] (k * (k + 1))

/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): ((k + 2) / k)
Output (closed form): (n + 1)*(n + 2)/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] ((k + 2) / k)

/--
info: #cas [product k 0 n]
Domain: k ∈ [0, n]
Input (factor): (3)
Output (closed form): 3*3^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 0 n] (3)

set_option linter.style.longLine false in
/--
error: product: the factor is not, as written, a constant times powers of linear factors k + s with integer s, and without Hex `product` does not factor it: write it as such a product, or use CASHex (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely over ℚ
-/
#guard_msgs (error, drop info) in
#cas [product k 1 n] (k^2 + 1)

set_option linter.style.longLine false in
/--
error: product: the factor is not, as written, a constant times powers of linear factors k + s with integer s, and without Hex `product` does not factor it: write it as such a product, or use CASHex (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely over ℚ
-/
#guard_msgs (error, drop info) in
#cas [product k 2 n] (1 - 1/k^2)

-- A linear factor with a rational shift, `2*k - 1 = 2*(k - 1/2)`: Hex would not help.
set_option linter.style.longLine false in
/--
error: product: the factor is not a constant times powers of linear factors k + s with integer s; its product needs Gamma functions or Pochhammer symbols
-/
#guard_msgs (error, drop info) in
#cas [product k 1 n] (2*k - 1)

/--
error: product: the factor k vanishes in the range of the product
-/
#guard_msgs (error, drop info) in
#cas [product k 0 n] (1 / k)

-- RSolve
set_option linter.style.longLine false in
/--
info: #cas [rsolve a n, a 0 = 0, a 1 = 1]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 2) = a (n + 1) + a n, a 0 = 0, a 1 = 1
Output (the sequence with these initial values): a n = (((1 + sqrt(5))/2)^n - ((1 -
sqrt(5))/2)^n)/sqrt(5)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] A sequence has the recurrence and the initial values exactly when it is the closed form
        Proposition: ∀ (a : ℕ → ℝ),
          (∀ (n : ℕ), a (n + 2) = a (n + 1) + a n) ∧ a 0 = 0 ∧ a 1 = 1 ↔
            ∀ (n : ℕ), a n = (((1 + √5) / 2) ^ n - ((1 - √5) / 2) ^ n) / √5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [rsolve a n, a 0 = 0, a 1 = 1] (a (n + 2) = a (n + 1) + a n)

/--
info: #cas [rsolve a n]
Domain: a : ℕ → ℝ
Input (recurrence): a (n + 2) = a (n + 1) + a n
Output (general solution): a n = c₁*((1 + sqrt(5))/2)^n + c₂*((1 - sqrt(5))/2)^n

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Closed form of every solution
        Proposition: ∀ (a : ℕ → ℝ),
          (∀ (n : ℕ), a (n + 2) = a (n + 1) + a n) ↔
            ∃ c₁ c₂, ∀ (n : ℕ), a n = c₁ * ((1 + √5) / 2) ^ n + c₂ * ((1 - √5) / 2) ^ n
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [rsolve a n] (a (n + 2) = a (n + 1) + a n)

-- The initial values may sit at any two consecutive indices.
set_option linter.style.longLine false in
/--
info: #cas [rsolve a n, a 1 = 1, a 2 = 1]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 2) = a (n + 1) + a n, a 1 = 1, a 2 = 1
Output (the sequence with these initial values): a n = (((1 + sqrt(5))/2)^n - ((1 -
sqrt(5))/2)^n)/sqrt(5)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 1 = 1, a 2 = 1] (a (n + 2) = a (n + 1) + a n)

/--
info: #cas [rsolve a n, a 0 = 1]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 1) = 2 * a n + 1, a 0 = 1
Output (the sequence with these initial values): a n = -1 + 2*2^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 1] (a (n + 1) = 2 * a n + 1)

/--
info: #cas [rsolve a n]
Domain: a : ℕ → ℝ
Input (recurrence): a (n + 2) = 5 * a (n + 1) - 6 * a n
Output (general solution): a n = c₁*2^n + c₂*3^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n] (a (n + 2) = 5 * a (n + 1) - 6 * a n)

/--
info: #cas [rsolve a n, a 0 = 2, a 1 = 3]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 2) = 3 * a (n + 1) - 2 * a n, a 0 = 2, a 1 = 3
Output (the sequence with these initial values): a n = 1 + 2^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 2, a 1 = 3] (a (n + 2) = 3 * a (n + 1) - 2 * a n)

-- A double root: `1` and `n`.
/--
info: #cas [rsolve a n]
Domain: a : ℕ → ℝ
Input (recurrence): a (n + 2) = 2 * a (n + 1) - a n
Output (general solution): a n = c₁ + c₂*n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n] (a (n + 2) = 2 * a (n + 1) - a n)

/--
info: #cas [rsolve a n, a 0 = 0, a 1 = 0]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 2) - 2 * a (n + 1) + a n = 1, a 0 = 0, a 1 = 0
Output (the sequence with these initial values): a n = 1/2*n^2 - 1/2*n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 0, a 1 = 0] (a (n + 2) - 2 * a (n + 1) + a n = 1)

/--
info: #cas [rsolve a n, a 0 = 1]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 1) = a n + n, a 0 = 1
Output (the sequence with these initial values): a n = -(1/2*n) + 1/2*n^2 + 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 1] (a (n + 1) = a n + n)

-- The complex characteristic roots `±i`, in real form.
/--
info: #cas [rsolve a n, a 0 = 1, a 1 = 0]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 2) = - a n, a 0 = 1, a 1 = 0
Output (the sequence with these initial values): a n = re(i^n)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 1, a 1 = 0] (a (n + 2) = - a n)

-- The Padovan numbers: `r ^ 3 - r - 1` has one real root and a pair of complex roots, known by
-- certified enclosures, which the theorem states first and names `r₁` and `z₁`.
set_option linter.style.longLine false in
/--
info: #cas [rsolve a n, a 0 = 1, a 1 = 1, a 2 = 1]
Domain: a : ℕ → ℝ
Input (recurrence with initial values): a (n + 3) = a (n + 1) + a n, a 0 = 1, a 1 = 1, a 2 = 1
Output (the sequence with these initial values): a n = (7/23*r₁^2 + 1/23*r₁ + 3/23)*r₁^n +
2*re((7/23*z₁^2 + 1/23*z₁ + 3/23)*z₁^n)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n, a 0 = 1, a 1 = 1, a 2 = 1] (a (n + 3) = a (n + 1) + a n)

/--
info: #cas [rsolve a n]
Domain: a : ℕ → ℝ
Input (recurrence): a (n + 3) = a (n + 1) + a n
Output (general solution): a n = c₁*r₁^n + c₂*re(z₁^n) + c₃*im(z₁^n)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n] (a (n + 3) = a (n + 1) + a n)

-- `r ^ 4 - 5 r ^ 2 + 6 = (r ^ 2 - 2) (r ^ 2 - 3)`: without a factor provider the quartic is not
-- split and its four real roots are enclosed; with CASHex they are `±√2` and `±√3`.
/--
info: #cas [rsolve a n]
Domain: a : ℕ → ℝ
Input (recurrence): a (n + 4) = 5 * a (n + 2) - 6 * a n
Output (general solution): a n = c₁*r₁^n + c₂*r₂^n + c₃*r₃^n + c₄*r₄^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rsolve a n] (a (n + 4) = 5 * a (n + 2) - 6 * a n)

set_option linter.style.longLine false in
/--
error: rsolve: recurrences with coefficients that depend on n are not treated (the coefficient of a n is n)
-/
#guard_msgs (error, drop info) in
#cas [rsolve a n] (a (n + 1) = n * a n)

/--
error: rsolve: the coefficient of a n is zero; this is a recurrence of lower order for a (n + 1)
-/
#guard_msgs (error, drop info) in
#cas [rsolve a n] (a (n + 2) = a (n + 1))

/--
error: rsolve: the recurrence must be linear in a
-/
#guard_msgs (error, drop info) in
#cas [rsolve a n] (a (n + 1) = a n * a n)

/--
error: rsolve: give the 2 initial values a k, …, a (k + 1) at consecutive indices
-/
#guard_msgs (error, drop info) in
#cas [rsolve a n, a 0 = 1] (a (n + 2) = a (n + 1) + a n)

-- Bases of powers are parenthesized
/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): (-2)
Output (closed form): (-2)^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] (-2)

/--
info: #cas [product k 1 n]
Domain: k ∈ [1, n]
Input (factor): (2/3)
Output (closed form): (2/3)^n

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [product k 1 n] (2/3)
