/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Positive definiteness and Rayleigh bounds of rational matrices

`#cas [positiveDefinite] A` decides whether a matrix with rational entries is positive definite
and proves the answer; `#cas [eigenvalueBounds] A` gives certified Rayleigh bounds of a symmetric
matrix. Each command runs in the build inside `#guard_msgs`, which checks its report.

Both commands eliminate exactly over `ℚ`, so tiny entries and nearly singular matrices need no
care. The answers are `True` with `!![2, 1; 1, 2].PosDef`, from `A = L D Lᵀ` with the pivots `2`
and `3/2`; `False` with `¬!![1, 2; 2, 1].PosDef`, from the vector `x = (-2, 1)` and
`xᵀ A x = -3`; `False` because `!![1, 2; 3, 4]` is not symmetric; `True` for a tridiagonal
matrix; `False` for the singular `!![1, 1; 1, 1]`, where `x = (-1, 1)` gives `xᵀ A x = 0`, and
`True` once its last entry is `1000000000001/1000000000000`; `True` for
`!![1/10^15, 0; 0, 1/10^15]`; and `True` for the `10 × 10` Hilbert matrix `1 / (i + j + 1)`,
whose last pivot is `1/44914183600`.

The Rayleigh bounds `c ≤ λ_min, λ_max ≤ μ` are the extreme eigenvalues rounded outward to six
places, or to `d` places with `(digits := d)`. The proposition states
`c ∑ xᵢ² ≤ ∑ᵢ ∑ⱼ A i j xᵢ xⱼ ≤ μ ∑ xᵢ²` for every real vector and gives two vectors for which the
bounds `c + 10 ^ (-d)` and `μ - 10 ^ (-d)` fail. The bounds are `1` and `3` for `!![2, 1; 1, 2]`;
`1.267949` and `4.732051` for the tridiagonal matrix, whose extreme eigenvalues are `3 - √3` and
`3 + √3`; `1` and `1000000` for `!![1000000, 0; 0, 1]`; and, with fourteen places,
`0.00000000000010` and `1.75191967026518` for the Hilbert matrix, whose smallest eigenvalue is
about `1.09 × 10 ^ (-13)`.

`posDef_two_one` is the first answer as a theorem, with the factorization the command finds.
-/

public section

namespace CAS.Examples.Matrix

open CAS.Analysis.Matrix

/-- `!![2, 1; 1, 2]` is positive definite: `A = L D Lᵀ` with `L = !![1, 0; 1/2, 1]` and the
pivots `D = (2, 3/2)`, which the kernel checks entry by entry. -/
theorem posDef_two_one :
    (Matrix.of fun i j ↦ ((![![2, 1], ![1, 2]] : Fin 2 → Fin 2 → ℚ) i j : ℝ)).PosDef :=
  posDef_of_ldlCheck (l := ![![0, 0], ![1/2, 0]]) (D := ![2, 3/2]) (by decide +kernel)

end CAS.Examples.Matrix

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![2, 1; 1, 2]
Output (Boolean): True

[CAS.Command.details] More details
  [CAS.Command.computation] Certificate
    A = L D Lᵀ over ℚ with pivots D = [2, 3/2], all positive
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The matrix is positive definite
        Proposition: !![2, 1; 1, 2].PosDef
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [positiveDefinite] !![2, 1; 1, 2]

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![1, 2; 2, 1]
Output (Boolean): False (xᵀAx ≤ 0 for x = [-2, 1])

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![1, 2; 2, 1]

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![1, 2; 3, 4]
Output (Boolean): False (not symmetric)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![1, 2; 3, 4]

/--
info: #cas [positiveDefinite]
Domain: 3 × 3 real matrix
Input (matrix): !![4, 1, 0; 1, 3, 1; 0, 1, 2]
Output (Boolean): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![4, 1, 0; 1, 3, 1; 0, 1, 2]

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![1, 1; 1, 1]
Output (Boolean): False (xᵀAx ≤ 0 for x = [-1, 1])

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![1, 1; 1, 1]

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![1, 1; 1, 1000000000001/1000000000000]
Output (Boolean): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![1, 1; 1, 1000000000001/1000000000000]

/--
info: #cas [positiveDefinite]
Domain: 2 × 2 real matrix
Input (matrix): !![1/10^15, 0; 0, 1/10^15]
Output (Boolean): True

[CAS.Command.details] More details
  [CAS.Command.computation] Certificate
    A = L D Lᵀ over ℚ with pivots D = [1/1000000000000000, 1/1000000000000000], all positive
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The matrix is positive definite
        Proposition: !![1 / 1000000000000000, 0; 0, 1 / 1000000000000000].PosDef
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [positiveDefinite] !![1/10^15, 0; 0, 1/10^15]

/--
info: #cas [positiveDefinite]
Domain: 10 × 10 real matrix
Input (matrix): !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]
Output (Boolean): True

[CAS.Command.details] More details
  [CAS.Command.computation] Certificate
    A = L D Lᵀ over ℚ with pivots D = [1, 1/12, 1/180, 1/2800, 1/44100, 1/698544, 1/11099088,
1/176679360, 1/2815827300, 1/44914183600], all positive
-/
#guard_msgs (info, substring := true) in
#cas [positiveDefinite] !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]

/--
info: #cas [eigenvalueBounds]
Domain: 2 × 2 symmetric real matrix
Input (matrix): !![2, 1; 1, 2]
Output (Rayleigh bounds): 1.000000 ≤ λ_min, λ_max ≤ 3.000000

[CAS.Command.details] More details
  [CAS.Command.computation] Certificate
    A - cI = L D Lᵀ and μI - A = L' D' L'ᵀ over ℚ, with nonnegative pivots
    x, y over ℚ with xᵀAx < (c + 10^-6) |x|² and yᵀAy > (μ - 10^-6) |y|²
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Rayleigh bounds, sharp to 10^-6
        Proposition: (∀ (x : Fin 2 → ℝ),
            1.000000 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![2, 1; 1, 2] i j * x i * x j ∧
              ∑ i, ∑ j, !![2, 1; 1, 2] i j * x i * x j ≤ 3.000000 * ∑ i, x i ^ 2) ∧
          (∃ x, ∑ i, ∑ j, !![2, 1; 1, 2] i j * x i * x j < 1.000001 * ∑ i, x i ^ 2) ∧
            ∃ x, 2.999999 * ∑ i, x i ^ 2 < ∑ i, ∑ j, !![2, 1; 1, 2] i j * x i * x j
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [eigenvalueBounds] !![2, 1; 1, 2]

/--
info: #cas [eigenvalueBounds]
Domain: 3 × 3 symmetric real matrix
Input (matrix): !![4, 1, 0; 1, 3, 1; 0, 1, 2]
Output (Rayleigh bounds): 1.267949 ≤ λ_min, λ_max ≤ 4.732051

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]

/--
info: #cas [eigenvalueBounds]
Domain: 2 × 2 symmetric real matrix
Input (matrix): !![1000000, 0; 0, 1]
Output (Rayleigh bounds): 1.000000 ≤ λ_min, λ_max ≤ 1000000.000000

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalueBounds] !![1000000, 0; 0, 1]

/--
info: #cas (digits := 14) [eigenvalueBounds]
Domain: 10 × 10 symmetric real matrix
Input (matrix): !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]
Output (Rayleigh bounds): 0.00000000000010 ≤ λ_min, λ_max ≤ 1.75191967026518

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 14) [eigenvalueBounds] !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]
