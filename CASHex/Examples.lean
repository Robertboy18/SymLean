/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CASHex.Algebra
public import CASHex.Factor
public import CASHex.LinearAlgebra
public import CASHex.NumberTheory

/-!
# Examples of the optional Hex routes

Bare `cas` on irreducibility over `ℤ` and `ZMod p`, on determinants of matrix literals and on
primality, through Hex; the complete factorization over `ℚ` of `#cas [factor]`, `#cas [apart]` and
`#cas [product]`; the calls `primeQ n`, `moebiusMu n` and `eulerPhi n` and the commands
`#cas [factorInteger]` and `[det]`, which call Hex and check its certificates; `#cas [dsolve]`,
`[rsolve]` and `[inverseLaplace]`, whose root splitter takes the factors of Hex's factorization;
and `#cas [eigenvalues]` and `[eigenvectors]`, which ask Hex whether factors of the
characteristic polynomial are irreducible over `ℚ` (the enclosed factors for eigenvalues, the
factors left after the rational roots for eigenvectors): the theorems state it for each factor
whose irreducibility Hex certifies, and the reports list the others. Each proof depends only on
the standard axioms.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>.
  The certificates checked here are Hex's; the routes that call it are in `CASHex.Algebra`,
  `CASHex.Factor`, `CASHex.LinearAlgebra` and `CASHex.NumberTheory`.
-/

@[expose] public section

namespace CASHex.Examples

open Polynomial

set_option linter.hashCommand false

/-- A certificate over `ℤ`: `X ^ 4 + 1` is Eisenstein after the shift `X ↦ X + 1`. -/
theorem irreducible_X_pow_four_add_one : Irreducible (X ^ 4 + 1 : ℤ[X]) := by
  cas

/-- A Rabin certificate over `ZMod 5`. -/
theorem irreducible_X_sq_add_two : Irreducible (X ^ 2 + 2 : (ZMod 5)[X]) := by
  cas

/-- The AES modulus over `ZMod 2`. -/
theorem irreducible_aes : Irreducible (X ^ 8 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  cas

-- A Swinnerton-Dyer polynomial is outside Hex's certificate languages. `cas` then tries
-- `irreducibility!`, whose kernel replay of Hex's factorizer needs `import all` of Hex's executable
-- modules in a `module` such as this one, so here it is refused.
example : True := by
  fail_if_success
    have : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by cas
  trivial

-- `cas?` reaches the Hex route, reports it and suggests bare `cas`.
/--
info: Try this:
  [apply] cas

Lean checked the suggested replacement against the original goal. Selected route: CAS route: hex, Hex irreducibility certificate, checked by the kernel.
-/
#guard_msgs in
example : Irreducible (X ^ 2 + 2 : (ZMod 5)[X]) := by
  cas?

/-- A determinant by Hex's fraction-free elimination. -/
theorem det_four : Matrix.det !![(3 : ℤ), 1, -4, 4; 3, 3, 2, -5; -2, 4, -3, 5; -2, 0, -3, 0] =
    650 := by
  cas

/-- info: 'CASHex.Examples.irreducible_aes' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducible_aes

/-- info: 'CASHex.Examples.det_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms det_four

-- A reducible polynomial is refused.
example : True := by
  fail_if_success
    have : Irreducible (X ^ 4 - 1 : ℤ[X]) := by cas
  trivial

/-- A determinant equation written the other way round, over `ℚ`. -/
theorem det_rational : (5 / 4 : ℚ) = Matrix.det !![(1 / 2 : ℚ), 1; -1 / 4, 2] := by
  cas

-- With `cas.hexHeartbeats` at `0` the Hex route is off, and the other routes of `cas` do not
-- prove irreducibility.
example : True := by
  fail_if_success
    have : Irreducible (X ^ 4 + 1 : ℤ[X]) := by
      set_option cas.hexHeartbeats 0 in cas
  trivial

-- With a budget of one thousand heartbeats the first branch fails (Hex runs out, and no other
-- route of `cas` proves this goal), and the failure is ordinary, so `first` goes on.
set_option linter.unusedTactic false in
example : Irreducible (X ^ 4 + 1 : ℤ[X]) := by
  first
    | set_option cas.hexHeartbeats 1 in cas
    | cas

-- After a Hex failure, `first` goes on as well.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example : True := by
  first
    | (have : Irreducible (X ^ 4 - 1 : ℤ[X]) := by cas); trivial
    | trivial

/-- Output (scalar ℝ, factors irreducible over ℚ): (x^2 - 2*x + 2)*(x^2 + 2*x + 2) -/
#guard_msgs (info, substring := true) in
#cas [factor] (x ^ 4 + 4)

/-- Output (scalar ℝ, factors irreducible over ℚ): (x^2 - x + 1)*(x + 1)*(x^2 + x + 1)*(x - 1) -/
#guard_msgs (info, substring := true) in
#cas [factor] (x ^ 6 - 1)

-- A repeated factor and a scalar that is not a unit of `ℤ`: `(x - 1)` appears with exponent 2.
/-- Output (scalar ℝ, factors irreducible over ℚ): 1/2*((x - 1)^2*x) -/
#guard_msgs (info, substring := true) in
#cas [factor] (x ^ 3 / 2 - x ^ 2 + x / 2)

-- `apart` and `product` with Hex's complete factorization over `ℚ` (without Hex they use only
-- the factors written in the input; see `CAS/Examples/Algebra.lean` and
-- `CAS/Examples/Recurrences.lean`).
/-- Output (partial fractions): -1/(2*(x + 1)) + 1/(2*(x - 1)) -/
#guard_msgs (info, substring := true) in
#cas [apart] (1/(x^2-1))

/-- Output (partial fractions): 1/(x + 1) + 1/(x - 1) - 1/x -/
#guard_msgs (info, substring := true) in
#cas [apart x] ((x^2 + 1) / (x^3 - x))

/-- Output (partial fractions): -(x - 2)/(3*(x^2 - x + 1)) + 1/(3*(x + 1)) -/
#guard_msgs (info, substring := true) in
#cas [apart] (1/(x^3 + 1))

/-- Output (partial fractions): -(x - 2)/(8*(x^2 - 2*x + 2)) + (x + 2)/(8*(x^2 + 2*x + 2)) -/
#guard_msgs (info, substring := true) in
#cas [apart] (1/(x^4 + 4))

/-- Output (partial fractions): 7/(2*x + 1) - 2/(x + 1) -/
#guard_msgs (info, substring := true) in
#cas [apart] ((3*x + 5)/(2*x^2 + 3*x + 1))

-- Rational integration with Hex's factorization of a denominator of degree three or more (refused
-- without Hex; see `CAS/Examples/BasicIntegration.lean`).
set_option linter.style.longLine false in
/-- Output (scalar ℝ; antiderivative): -1/6*log(x^2 + x + 1) - atan((2*x + 1)/sqrt(3))/sqrt(3) + 1/3*log(x - 1) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1/(x^3 - 1))

-- Eigenvalues through the backend of `#cas [eigenvalues]`. They are rational here, so the report
-- is the factorization of the characteristic polynomial, as without Hex.
/-- Output (eigenvalues with multiplicity): [1, 100000007, 100000009] -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![100000007, 0, 0; 0, 100000009, 0; 0, 0, 1]

-- The characteristic polynomial `X ^ 3 - 2` has one real and two complex roots, named by their
-- enclosures; Hex's certificate adds that it is irreducible over `ℚ`.
/-- Irreducible (X ^ 3 - 2) ∧ -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]

-- Eigenvectors through the backend of `#cas [eigenvectors]`: for each factor `q` of the
-- characteristic polynomial left after its rational roots, a basis for every root `α` of `q`, with
-- entries that are polynomials in `α`, and the statement that `q` splits over `ℝ` when a
-- certificate shows that its roots are all real. The theorem adds that `q` is irreducible over
-- `ℚ` for each `q` whose irreducibility Hex certifies, and the report lists the others. The
-- planner metadata names the backend.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(2×2)
Input (matrix): !![1, 1; 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((map (algebraMap ℚ ℝ) (X ^ 2 - X - 1)).Splits ∧
            ∀ (α : ℝ),
              (aeval α) (X ^ 2 - X - 1) = 0 →
                (∀ (i : Fin 1), (!![1, 1; 1, 0] - α • 1).mulVec (![![α, 1]] i) = 0) ∧
                  LinearIndependent ℝ ![![α, 1]] ∧
                    ∀ (x : Fin 2 → ℝ), (!![1, 1; 1, 0] - α • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![α, 1]] i) ∧
          Irreducible (X ^ 2 - X - 1) ∧ !![1, 1; 1, 0].charpoly = X ^ 2 - X - 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] CASHex backend of eigenvectors: selected
-/
#guard_msgs (whitespace := lax) in
#cas [eigenvectors] !![1, 1; 1, 0]

-- The characteristic polynomial `X ^ 2 - X / 2 - 1` does not have integer coefficients; Hex
-- certifies its primitive integer scaling `2 X ^ 2 - X - 2`.
/-- Irreducible (2 * X ^ 2 - X - 2) ∧ -/
#guard_msgs (info, substring := true) in
#cas [eigenvectors] !![1/2, 1; 1, 0]

-- The Swinnerton-Dyer polynomial `X ^ 4 - 10 X ^ 2 + 1` is irreducible over `ℚ` but outside Hex's
-- certificate languages: the theorems have no `Irreducible` conjunct for it, and both reports
-- list it. Its roots are real, so the eigenvectors theorem says that it splits over `ℝ`.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(4×4)
Input (matrix): !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α^3 - 10*α, α^2 - 10, α, 1]]] for each α ∈ ℝ with α^4 - 10*α^2 + 1 = 0
Factors without a Hex irreducibility certificate: X^4 - 10*X^2 + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((map (algebraMap ℚ ℝ) (X ^ 4 - 10 * X ^ 2 + 1)).Splits ∧
            ∀ (α : ℝ),
              (aeval α) (X ^ 4 - 10 * X ^ 2 + 1) = 0 →
                (∀ (i : Fin 1),
                    (!![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0] - α • 1).mulVec
                        (![![α ^ 3 - 10 * α, α ^ 2 - 10, α, 1]] i) =
                      0) ∧
                  LinearIndependent ℝ ![![α ^ 3 - 10 * α, α ^ 2 - 10, α, 1]] ∧
                    ∀ (x : Fin 4 → ℝ),
                      (!![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0] - α • 1).mulVec x = 0 →
                        ∃ c, x = ∑ i, c i • ![![α ^ 3 - 10 * α, α ^ 2 - 10, α, 1]] i) ∧
          !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0].charpoly = X ^ 4 - 10 * X ^ 2 + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] CASHex backend of eigenvectors: selected
-/
#guard_msgs (whitespace := lax) in
#cas [eigenvectors] !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]

set_option linter.style.longLine false in
/--
info: #cas [eigenvalues]
Domain: ℚ^(4×4)
Input (matrix): !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]
Output (eigenvalues with multiplicity): [r₁, r₂, r₃, r₄]; r₁ ∈ (-3.14626438, -3.14626436), r₂ ∈ (-0.31783726, -0.31783724), r₃ ∈ (0.31783724, 0.31783726), r₄ ∈ (3.14626436, 3.14626438)
Factors without a Hex irreducibility certificate: X^4 - 10*X^2 + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The spectrum with algebraic multiplicities
        Proposition: let r₁ := CAS.AlgRoot.real [1, 0, -10, 0, 1] (-3.14626438) (-3.14626436);
        let r₂ := CAS.AlgRoot.real [1, 0, -10, 0, 1] (-0.31783726) (-0.31783724);
        let r₃ := CAS.AlgRoot.real [1, 0, -10, 0, 1] 0.31783724 0.31783726;
        let r₄ := CAS.AlgRoot.real [1, 0, -10, 0, 1] 3.14626436 3.14626438;
        (r₁ ∈ Set.Ioo (-3.14626438) (-3.14626436) ∧ r₁ ^ 4 - 10 * r₁ ^ 2 + 1 = 0) ∧
          (r₂ ∈ Set.Ioo (-0.31783726) (-0.31783724) ∧ r₂ ^ 4 - 10 * r₂ ^ 2 + 1 = 0) ∧
            (r₃ ∈ Set.Ioo 0.31783724 0.31783726 ∧ r₃ ^ 4 - 10 * r₃ ^ 2 + 1 = 0) ∧
              (r₄ ∈ Set.Ioo 3.14626436 3.14626438 ∧ r₄ ^ 4 - 10 * r₄ ^ 2 + 1 = 0) ∧
                spectrum ℝ !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0] = {r₁, r₂, r₃, r₄} ∧
                  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0].charpoly.roots = {r₁, r₂, r₃, r₄}
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] CASHex backend of eigenvalues: selected
-/
#guard_msgs (whitespace := lax) in
#cas [eigenvalues] !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]

set_option linter.style.longLine false in
/-- Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℂ with α^2 + 1 = 0 -/
#guard_msgs (info, substring := true) in
#cas [eigenvectors] !![0, -1; 1, 0]

-- The irreducible cubic `X ^ 3 - 2`: one statement for its real root and its two complex roots.
/-- Irreducible (X ^ 3 - 2) ∧ !![0, 0, 2; 1, 0, 0; 0, 1, 0].charpoly = X ^ 3 - 2 -/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![0, 0, 2; 1, 0, 0; 0, 1, 0]

-- A rational eigenvalue and the two roots of the irreducible quadratic `X ^ 2 - X - 1`.
set_option linter.style.longLine false in
/-- Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![1, 0, 0]], α ↦ [![0, α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0 -/
#guard_msgs (info, substring := true) in
#cas [eigenvectors] !![2, 0, 0; 0, 1, 1; 0, 1, 0]

/-- Output (closed form): (n + 1)/(2*n) for n ≥ 1 -/
#guard_msgs (info, substring := true) in
#cas [product k 2 n] (1 - 1/k^2)

set_option linter.style.longLine false in
/--
error: product: the factor is not a constant times powers of linear factors k + s with integer s; its product needs Gamma functions or Pochhammer symbols
-/
#guard_msgs (error, drop info) in
#cas [product k 1 n] (k^2 + 1)

-- `r ^ 4 - 5 r ^ 2 + 6 = (r ^ 2 - 3) (r ^ 2 - 2)` from Hex's factorization: the exact roots `±√3`
-- and `±√2`, in the order of Hex's factors, where the core route encloses four real roots.
set_option linter.style.longLine false in
/-- Output (general solution): a n = c₁*sqrt(3)^n + c₂*(-sqrt(3))^n + c₃*sqrt(2)^n + c₄*(-sqrt(2))^n -/
#guard_msgs (info, substring := true) in
#cas [rsolve a n] (a (n + 4) = 5 * a (n + 2) - 6 * a n)

/-- Primality through Hex's `primality`: a Pocklington certificate replayed in the kernel. -/
theorem mersenne_61_prime : Nat.Prime (2 ^ 61 - 1) := by
  cas

/-! ## Commands that call Hex -/

-- primeQ, factorInteger, moebiusMu, eulerPhi through Hex
/--
info: #cas (primeQ 2305843009213693951)
Domain: ℕ
Input (natural numbers): 2305843009213693951
Output (primality (Hex primality certificate)): True

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] primality (Hex primality certificate)
        Proposition: Nat.Prime 2305843009213693951
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (primeQ 2305843009213693951)

/--
info: #cas (primeQ 170141183460469231731687303715884105727)
Domain: ℕ
Input (natural numbers): 170141183460469231731687303715884105727
Output (primality (Hex primality certificate)): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (primeQ 170141183460469231731687303715884105727)

/--
info: #cas (primeQ 1000001)
Domain: ℕ
Input (natural numbers): 1000001
Output (primality (1000001 = 101*9901)): False

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (primeQ 1000001)

/--
info: #cas [factorInteger]
Domain: ℕ
Input (natural numbers): 600851475143
Output (prime factorization): 71*839*1471*6857  [(71, 1), (839, 1), (1471, 1), (6857, 1)]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] prime factorization
        Proposition: Nat.primeFactorsList 600851475143 = [71, 839, 1471, 6857]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [factorInteger] 600851475143

/--
info: #cas [factorInteger]
Domain: ℕ
Input (natural numbers): 1000000016000000063
Output (prime factorization): 1000000007*1000000009  [(1000000007, 1), (1000000009, 1)]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factorInteger] 1000000016000000063

/--
info: #cas [factorInteger]
Domain: ℕ
Input (natural numbers): 2305843009213693953
Output (prime factorization): 3*768614336404564651  [(3, 1), (768614336404564651, 1)]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factorInteger] 2305843009213693953

/--
info: #cas (moebiusMu 30)
Domain: ℕ
Input (natural numbers): 30
Output (Möbius function): -1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (moebiusMu 30)

/--
info: #cas (moebiusMu 360)
Domain: ℕ
Input (natural numbers): 360
Output (Möbius function): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (moebiusMu 360)

/--
info: #cas (eulerPhi 1000003)
Domain: ℕ
Input (natural numbers): 1000003
Output (eulerPhi): 1000002

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] eulerPhi
        Proposition: Nat.totient 1000003 = 1000002
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (eulerPhi 1000003)

/--
info: #cas (eulerPhi 600851475143)
Domain: ℕ
Input (natural numbers): 600851475143
Output (eulerPhi): 591194251200

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi 600851475143)

/--
error: factorInteger: expected a natural number at least 2
-/
#guard_msgs (error, drop info) in
#cas [factorInteger] 1

-- det through Hex's Bareiss certificate
/--
info: #cas [det]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 4, 5, 6; 7, 8, 10]
Output (determinant (Hex's Bareiss certificate)): -3

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Determinant
        Proposition: !![1, 2, 3; 4, 5, 6; 7, 8, 10].det = -3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]

/--
info: #cas [det]
Domain: ℚ^(2×2)
Input (matrix): !![1/2, 1; 3, 4]
Output (determinant (Hex's Bareiss certificate)): -1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [det] !![1/2, 1; 3, 4]

/-! `#cas [dsolve y x]` with Hex's factor provider. The root splitter asks it for the square-free
part `r ^ 4 + 5 r ^ 2 + 6` of degree four, and the factors `r ^ 2 + 2` and `r ^ 2 + 3` it returns
give the exact roots `±√2 i` and `±√3 i`, which the core names by enclosures (see
`CAS/Examples/DSolveRoot.lean`). The characteristic polynomial of the second equation splits into
the rational root `1` and a quadratic without the provider, so its answer is the one of
`CAS/Examples/DSolveOrder.lean`. -/

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' + 5*y'' + 6*y = 0)
Output (order 4, characteristic roots: ±√
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' + 5*y'' + 6*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - (1234566/1234567) * y'' +
(1234566/1234567) * y' - y = 0)
Output (order 3, characteristic roots: 1, -1/2469134 ± 1/2469134√6096622709955 i)
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - (1234566/1234567) * y'' + (1234566/1234567) * y' - y = 0)

/-! `#cas [inverseLaplace s t]` with Hex's factorization over `ℚ`: Hex splits `s ^ 4 + 4` into
`(s ^ 2 - 2 s + 2) (s ^ 2 + 2 s + 2)`, so the answer is exact, where without Hex the factor keeps
enclosures of its roots (see `CAS/Examples/InverseLaplace.lean`). -/

/--
Domain: s > 1
Input (proper rational function of s): (1 / (s ^ 4 + 4))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 4 + 4))

end CASHex.Examples
