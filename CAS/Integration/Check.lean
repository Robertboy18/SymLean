/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.SideConditionCompaction
public import CAS.Integration.TrigNormalization

/-!
# Residual check for symbolic antiderivatives

The soundness theorems rest on this residual route alone: the planner filters candidates with its
own tests (`IntegrationPlanner.searchCheckCandidate?`), and `integrate?` accepts a candidate only
through `certifyCandidate?`.
`route` forms the residual `candidate' - integrand` (`residual`), runs the checked
side-conditioned simplification route, and `certifyCandidate?` accepts exactly when the route
reaches literal zero, returning an `AntiderivativeCert`.

The route's raw obligations remain inspectable through `rawResidualNonzero`.
The public `residualNonzero` list is a checked canonical compaction of
it. An antiderivative certificate combines these algebraic obligations
with the validity requirements of both the primitive and integrand
(`AntiderivativeCert.requirements`).

## Main definitions

* `route`: the checked simplification route of the residual of a candidate.
* `AntiderivativeCert`: a candidate together with the proof that its route reaches literal zero.
* `certifyCandidate?`: the certificate of a candidate, when its route reaches literal zero.
* `AntiderivativeCert.candidateRequirements`: the requirement lists of a certificate, computed
  from the coordinate, the integrand and the candidate alone.

## Main results

* `AntiderivativeCert.eval_diff_eq`: the derivative of the certified primitive in coordinate `i`
  equals the integrand at every point where the certificate's requirements hold.
* `AntiderivativeCert.candidate_validAt` and `AntiderivativeCert.integrand_validAt`: there both
  expressions are defined.
* `sideHolds_of_dropListedPowers`: dropping listed powers of listed obligations loses nothing.

## Implementation notes

The route has two stages. `sparsePolynomialRoute` applies the ordered sparse normalizer, sound by
`Verified.Expr.Alg.eval_mvNormalizeExpr`, which closes polynomial residuals. A power of a product
of variables stays one exponent vector, but a power of a sum such as `(x + 1)^k` is multiplied
out. When the normalized residual is not zero, `TrigNormalization.route` continues from it. Every
stage is a `Verified.Expr.SideClaimRoute`, whose `sound` field proves that its output and its
input have equal values wherever its recorded nonzero obligations hold. The certificate stores
the candidate and `routeZero`, an equation between syntax trees decided by evaluation (the
integration tactic decides it with `decide +kernel`), and `eval_diff_eq_of_route_rhs_eq_zero`
derives the derivative identity from it. Search procedures may be arbitrarily heuristic because
the semantic theorem depends only on the checked route.

We compact the obligations with `Verified.Expr.compactNonzero` and then `dropListedPowers`, which
removes the expanded square of a denominator that the quotient rule records next to the
denominator; `Verified.Expr.sideHolds_of_compactNonzero` and `sideHolds_of_dropListedPowers`
transport the compact list back to the raw one. `AntiderivativeCert.candidateRequirements`
computes the same lists without a certificate, and
`AntiderivativeCert.requirements_eq_candidateRequirements` holds by `rfl`, so a tactic can read
the lists back and certify the route and the requirements in one kernel evaluation.
-/

@[expose] public section

namespace CAS.IntegrationCheck

/-- Symbolic derivative residual for an antiderivative candidate. -/
def residual {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  candidate.diff i - integrand

/-- Checked sparse-polynomial normalization used as the first residual pass. -/
def sparsePolynomialRoute {n : Nat}
    (expr : Verified.Expr (Fin n)) :
    Verified.Expr.SideClaimRoute (Fin n) where
  lhs := expr
  rhs := Verified.Expr.Alg.mvNormalizeExpr expr
  nonzero := []
  steps :=
    [{ name := "ordered-sparse-polynomial", kind := .checked }]
  sound := by
    intro x _hside
    simpa using
      Verified.Expr.Alg.eval_mvNormalizeExpr (WithLp.toLp 2 x) expr

/-- The sparse polynomial route records its input unchanged, including on fallback. -/
@[simp] theorem sparsePolynomialRoute_lhs {n : Nat}
    (expr : Verified.Expr (Fin n)) :
    (sparsePolynomialRoute expr).lhs = expr :=
  rfl

/--
The checked simplification route used to validate an antiderivative.

Rational-coefficient polynomials first use the ordered sparse
normalizer. This keeps powers compact and avoids expanding a high-degree
monomial into a long factor list. Unsupported expressions are returned
unchanged and continue through the trigonometric and theorem-side routes.
-/
def route {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) :
    Verified.Expr.SideClaimRoute (Fin n) :=
  let sparse := sparsePolynomialRoute (residual i integrand candidate)
  if sparse.rhs = 0 then
    sparse
  else
    sparse.trans
      (TrigNormalization.route sparse.rhs)
      (TrigNormalization.route_lhs sparse.rhs)

/-- The antiderivative residual route starts from the residual `∂ᵢ candidate - integrand`,
whether or not the trigonometric second stage was appended. -/
@[simp] theorem route_lhs {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) :
    (route i integrand candidate).lhs = residual i integrand candidate := by
  by_cases hzero :
      (sparsePolynomialRoute (residual i integrand candidate)).rhs = 0
  · simp [route, hzero]
  · simp [route, hzero, Verified.Expr.SideClaimRoute.trans]

/-- Raw nonzero obligations emitted by the checked antiderivative residual route. -/
def rawResidualNonzero {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) : List (Verified.Expr (Fin n)) :=
  (route i integrand candidate).nonzero

/--
Canonical nonzero obligations for the checked antiderivative residual route.

Checked normalization, product/power factorization, and deduplication
compact the raw list. The result gives sufficient obligations and may retain
conditions introduced by normalization; it need not be equivalent to the raw
list. The soundness theorem transports it back to the exact route requirements.
-/
def residualNonzero {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) : List (Verified.Expr (Fin n)) :=
  Verified.Expr.compactNonzero
    (rawResidualNonzero i integrand candidate)

/-- Semantic derivative identity supplied by a successful checked route. -/
theorem eval_diff_eq_of_route_rhs_eq_zero
    {n : Nat} {i : Fin n} {integrand candidate : Verified.Expr (Fin n)}
    (hzero : (route i integrand candidate).rhs = 0)
    (x : ℝ^n)
    (hside : Verified.Expr.Alg.SideHolds x
      (residualNonzero i integrand candidate)) :
    (candidate.diff i).eval x = integrand.eval x := by
  have hroute := (route i integrand candidate).sound x
    (Verified.Expr.sideHolds_of_compactNonzero hside)
  rw [route_lhs, hzero] at hroute
  change _ = (candidate.diff i).eval x - integrand.eval x at hroute
  simpa [sub_eq_zero] using hroute.symm

/-- A kernel-checked symbolic antiderivative certificate. -/
structure AntiderivativeCert {n : Nat} (i : Fin n)
    (integrand : Verified.Expr (Fin n)) where
  /-- Certified primitive. -/
  candidate : Verified.Expr (Fin n)
  /-- The theorem-side residual route closes syntactically to zero. -/
  routeZero : (route i integrand candidate).rhs = 0

/-- Total degree of a normalized polynomial expression, where every other node counts as an
atom of degree one. It only proposes the exponent tried by `powerOf`. -/
def degree {ι : Type*} : Verified.Expr ι → Nat
  | .add a b => max (degree a) (degree b)
  | .sub a b => max (degree a) (degree b)
  | .mul a b => degree a + degree b
  | .neg a => degree a
  | .pow a k => k * degree a
  | .nat _ => 0
  | .int _ => 0
  | .rat _ _ => 0
  | _ => 1

/-- The exponent `k = deg r / deg s` tried for `r = s ^ k`. -/
def exponent {ι : Type*} [DecidableEq ι] (s r : Verified.Expr ι) : Nat :=
  degree (Verified.Expr.Alg.normalize r) / degree (Verified.Expr.Alg.normalize s)

/-- `r - s ^ k` normalizes to `0` for the exponent `k = deg r / deg s`, and `k ≥ 2`. -/
def powerOf {ι : Type*} [DecidableEq ι] (s r : Verified.Expr ι) : Bool :=
  2 ≤ exponent s r &&
    decide (Verified.Expr.Alg.normalize (r - .pow s (exponent s r)) = 0)

/-- An obligation of the list that is not a power of another obligation of the list. -/
def isBase {ι : Type*} [DecidableEq ι] (side : List (Verified.Expr ι))
    (s : Verified.Expr ι) : Bool :=
  !side.any fun t ↦ powerOf t s

/-- Drop every nonzero obligation that is a power of another listed obligation which is not
itself such a power. The quotient rule records the expanded square of a denominator next to the
denominator, and this removes the square. A list without such a pair is returned unchanged. -/
def dropListedPowers {ι : Type*} [DecidableEq ι] (side : List (Verified.Expr ι)) :
    List (Verified.Expr ι) :=
  side.filter fun r ↦ !side.any fun s ↦ isBase side s && powerOf s r

/-- An obligation accepted by `powerOf s r` is the power of `s` it was tested against. -/
theorem eval_eq_pow_of_powerOf {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {s r : Verified.Expr ι} (h : powerOf s r = true) :
    r.eval ρ = s.eval ρ ^ exponent s r := by
  simp only [powerOf, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa [Verified.Expr.eval] using
    Verified.Expr.Alg.eval_eq_of_normalize_sub_eq_zero ρ r (.pow s (exponent s r)) h.2

/-- The obligations kept by `dropListedPowers` imply every original obligation. -/
theorem sideHolds_of_dropListedPowers {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {side : List (Verified.Expr ι)}
    (h : Verified.Expr.Alg.SideHolds ρ (dropListedPowers side)) :
    Verified.Expr.Alg.SideHolds ρ side := by
  intro r hr
  by_cases hdrop : (side.any fun s ↦ isBase side s && powerOf s r) = true
  · obtain ⟨s, hs, hsr⟩ := List.any_eq_true.mp hdrop
    simp only [Bool.and_eq_true] at hsr
    have hkept : s ∈ dropListedPowers side := by
      refine List.mem_filter.mpr ⟨hs, ?_⟩
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true,
        not_and]
      intro t _ _
      have hbase := hsr.1
      simp only [isBase, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hbase
      simpa using hbase t ‹_›
    rw [eval_eq_pow_of_powerOf (ρ := ρ) hsr.2]
    exact pow_ne_zero _ (h s hkept)
  · exact h r (List.mem_filter.mpr ⟨hr, by simpa using hdrop⟩)

namespace AntiderivativeCert

variable {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}

/-- Raw nonzero obligations emitted by this certificate's checked residual route. -/
def rawResidualNonzero (cert : AntiderivativeCert i integrand) :
    List (Verified.Expr (Fin n)) :=
  CAS.IntegrationCheck.rawResidualNonzero i integrand cert.candidate

/-- Canonical nonzero obligations for this certificate's checked residual route. -/
def residualNonzero (cert : AntiderivativeCert i integrand) :
    List (Verified.Expr (Fin n)) :=
  CAS.IntegrationCheck.residualNonzero i integrand cert.candidate

/-- Domain requirements of a checked antiderivative before compaction: the validity
requirements of the primitive and of the integrand, with the certificate's canonical residual
denominators appended to the nonzero list. -/
def rawRequirements (cert : AntiderivativeCert i integrand) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  let candidateRequirements := cert.candidate.validityRequirements
  let integrandRequirements := integrand.validityRequirements
  { nonzero :=
      candidateRequirements.nonzero ++
        integrandRequirements.nonzero ++ cert.residualNonzero
    positive :=
      candidateRequirements.positive ++ integrandRequirements.positive }

/--
Canonical domain requirements of a checked antiderivative.

The nonzero requirements cover the primitive, the integrand, and every
denominator used by the checked residual route. Checked factorization and
deduplication replace that raw list by sufficient canonical obligations, and an
obligation that is a power of another listed obligation is dropped. The
positive requirements record the strict square-root domains in both
expressions and are deduplicated syntactically. Real-logarithm arguments and
inverse-sine/cosine endpoint exclusions occur among the nonzero requirements.
-/
def requirements (cert : AntiderivativeCert i integrand) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  let raw := cert.rawRequirements
  { nonzero := dropListedPowers (Verified.Expr.compactNonzero raw.nonzero)
    positive := raw.positive.dedup }

/-- Compute the canonical domain requirements from the coordinate, integrand, and
candidate, without needing a residual proof. This lets tactics evaluate the lists
before constructing a certificate and certify both in one kernel evaluation. -/
def candidateRequirements {n : Nat} (i : Fin n) (integrand candidate : Verified.Expr (Fin n)) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  let candidateRequirements := candidate.validityRequirements
  let integrandRequirements := integrand.validityRequirements
  { nonzero :=
      dropListedPowers (Verified.Expr.compactNonzero
        (candidateRequirements.nonzero ++ integrandRequirements.nonzero ++
          CAS.IntegrationCheck.residualNonzero i integrand candidate))
    positive := (candidateRequirements.positive ++ integrandRequirements.positive).dedup }

/-- Requirement computation is independent of the certificate's residual proof. -/
theorem requirements_eq_candidateRequirements (cert : AntiderivativeCert i integrand) :
    cert.requirements = candidateRequirements i integrand cert.candidate :=
  rfl

private theorem rawRequirements_holds (cert : AntiderivativeCert i integrand)
    (x : ℝ^n) (h : cert.requirements.Holds x) :
    cert.rawRequirements.Holds x :=
  ⟨Verified.Expr.sideHolds_of_compactNonzero (sideHolds_of_dropListedPowers h.1),
    fun d hd ↦ h.2 d (List.mem_dedup.mpr hd)⟩

/-- Held certificate requirements imply validity of the primitive. -/
theorem candidate_validAt (cert : AntiderivativeCert i integrand)
    (x : ℝ^n) (h : cert.requirements.Holds x) :
    cert.candidate.ValidAt x := by
  apply Verified.Expr.ValidityRequirements.validAt_of_holds x cert.candidate
  obtain ⟨hnonzero, hpositive⟩ := cert.rawRequirements_holds x h
  exact ⟨fun d hd ↦ hnonzero d (by simp [rawRequirements, hd]),
    fun d hd ↦ hpositive d (by simp [rawRequirements, hd])⟩

/-- Held certificate requirements imply validity of the integrand. -/
theorem integrand_validAt (cert : AntiderivativeCert i integrand)
    (x : ℝ^n) (h : cert.requirements.Holds x) :
    integrand.ValidAt x := by
  apply Verified.Expr.ValidityRequirements.validAt_of_holds x integrand
  obtain ⟨hnonzero, hpositive⟩ := cert.rawRequirements_holds x h
  exact ⟨fun d hd ↦ hnonzero d (by simp [rawRequirements, hd]),
    fun d hd ↦ hpositive d (by simp [rawRequirements, hd])⟩

/-- Held certificate requirements discharge the checked residual route. -/
theorem residualNonzero_holds (cert : AntiderivativeCert i integrand)
    (x : ℝ^n) (h : cert.requirements.Holds x) :
    Verified.Expr.Alg.SideHolds x cert.residualNonzero := fun d hd ↦
  (cert.rawRequirements_holds x h).1 d (by simp [rawRequirements, hd])

/-- Semantic derivative identity supplied by a checked antiderivative certificate. -/
theorem eval_diff_eq (cert : AntiderivativeCert i integrand)
    (x : ℝ^n)
    (h : cert.requirements.Holds x) :
    (cert.candidate.diff i).eval x = integrand.eval x :=
  eval_diff_eq_of_route_rhs_eq_zero cert.routeZero x (cert.residualNonzero_holds x h)

end AntiderivativeCert

/-- Accept a candidate exactly when the checked residual route reaches zero. -/
@[irreducible]
def certifyCandidate? {n : Nat} (i : Fin n)
    (integrand candidate : Verified.Expr (Fin n)) :
    Option (AntiderivativeCert i integrand) :=
  if hzero : (route i integrand candidate).rhs = (0 : Verified.Expr (Fin n)) then
    some { candidate := candidate, routeZero := hzero }
  else
    none

end CAS.IntegrationCheck
