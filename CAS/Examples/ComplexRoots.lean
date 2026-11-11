/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# All complex roots of a polynomial

`#cas [roots z in ℂ] (p = q)` lists every complex solution of a polynomial equation with rational
coefficients, each once, by certified enclosures: `AlgRoot.real S lo hi` for a real root in
`(lo, hi)` and `AlgRoot.complex S u v ρ` for a complex root within `ρ` of `u + v i`, with `S` the
monic radical of `p - q`. The theorem binds the roots by `let`, states the enclosures and proves
`p z - q z = 0 ↔ z ∈ [r₁, …, z₁, conj z₁, …]` for every complex `z`, with `p - q` expanded. When
every root is a Gaussian rational, the roots are exact and the theorem is the equivalence
`p z - q z = 0 ↔ z = w₁ ∨ ⋯ ∨ z = wₖ`. Each command runs in the build inside `#guard_msgs`, which
checks its report.

The roots of `z ^ 4 + 1` are `z₁, conj z₁` near `-0.70710678 ± 0.70710678 i` and `z₂, conj z₂` near
`0.70710678 ± 0.70710678 i`; `z ^ 3 = 2` has the real root `1.25992105…` and a pair near
`-0.62996052 ± 1.09112364 i`; `z ^ 5 - z - 1` one real root and two pairs; `2 z ^ 2 - 2 z + 1` the
exact pair `1/2 ± 1/2 i`; `z ^ 6 = 1` the roots `±1` and two pairs; `(z - 1) ^ 3 (z ^ 2 + 1)` the
exact roots `1` and `± i`, each once; and `z ^ 2 + 1` the roots `± i`, with the theorem
`∀ z : ℂ, z ^ 2 + 1 = 0 ↔ z = Complex.I ∨ z = -Complex.I`. When some root is not a Gaussian
rational, the rational roots are enclosed like the others.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (z ^ 4 + 1 = 0)
Output (all 4 distinct complex roots, by certified enclosures): z₁, conj z₁ = α ± iβ, α ∈
[-0.70710680, -0.70710676], β ∈ [0.70710676, 0.70710680], z₂, conj z₂ = α ± iβ, α ∈ [0.70710676,
0.70710680], β ∈ [0.70710676, 0.70710680]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The complex roots, by certified enclosures, and no other
root
        Proposition: let z₁ := CAS.AlgRoot.complex [1, 0, 0, 0, 1] (-0.70710678) 0.70710678
2e-8;
        let z₂ := CAS.AlgRoot.complex [1, 0, 0, 0, 1] 0.70710678 0.70710678 2e-8;
        (z₁.re ∈ Set.Icc (-0.70710680) (-0.70710676) ∧ z₁.im ∈ Set.Icc 0.70710676 0.70710680) ∧
          (z₂.re ∈ Set.Icc 0.70710676 0.70710680 ∧ z₂.im ∈ Set.Icc 0.70710676 0.70710680) ∧
            ∀ (z : ℂ), z ^ 4 + 1 = 0 ↔ z ∈ [z₁, (starRingEnd ℂ) z₁, z₂, (starRingEnd ℂ) z₂]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [roots z in ℂ] (z ^ 4 + 1 = 0)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (z ^ 3 = 2)
Output (all 3 distinct complex roots, by certified enclosures): r₁ ∈ (1.25992104, 1.25992106), z₁,
conj z₁ = α ± iβ, α ∈ [-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots z in ℂ] (z ^ 3 = 2)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (z ^ 5 - z - 1 = 0)
Output (all 5 distinct complex roots, by certified enclosures): r₁ ∈ (1.16730397, 1.16730399), z₁,
conj z₁ = α ± iβ, α ∈ [-0.76488445, -0.76488441], β ∈ [0.35247153, 0.35247157], z₂, conj z₂ = α ±
iβ, α ∈ [0.18123242, 0.18123246], β ∈ [1.08395408, 1.08395412]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots z in ℂ] (z ^ 5 - z - 1 = 0)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (2 * z ^ 2 - 2 * z + 1 = 0)
Output (all 2 distinct complex roots): 1/2 + 1/2*i, 1/2 - 1/2*i

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots z in ℂ] (2 * z ^ 2 - 2 * z + 1 = 0)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (z ^ 6 = 1)
Output (all 6 distinct complex roots, by certified enclosures): r₁ ∈ (-1.00000001, -0.99999999), r₂
∈ (0.99999999, 1.00000001), z₁, conj z₁ = α ± iβ, α ∈ [-0.50000002, -0.49999998], β ∈ [0.86602538,
0.86602542], z₂, conj z₂ = α ± iβ, α ∈ [0.49999998, 0.50000002], β ∈ [0.86602538, 0.86602542]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots z in ℂ] (z ^ 6 = 1)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): ((z - 1) ^ 3 * (z ^ 2 + 1) = 0)
Output (all 3 distinct complex roots): 1, i, -i

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots z in ℂ] ((z - 1) ^ 3 * (z ^ 2 + 1) = 0)

/--
info: #cas [roots z in ℂ]
Domain: z ∈ ℂ
Input (polynomial equation with rational coefficients): (z ^ 2 + 1 = 0)
Output (all 2 distinct complex roots): i, -i

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The complex roots and no other root
        Proposition: ∀ (z : ℂ), z ^ 2 + 1 = 0 ↔ z = Complex.I ∨ z = -Complex.I
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [roots z in ℂ] (z ^ 2 + 1 = 0)

