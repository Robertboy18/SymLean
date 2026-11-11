/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Bound
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Approximation certificates

`ApproxOn f g s ε` says that `g` approximates `f` uniformly within `ε` on `s`.
An `ApproxCert` stores such a theorem as data, so CEGA planners and symbolic
passes can compose approximation and refinement claims while the final
statement is still an ordinary Lean theorem.

A chain of certificates may mix an interval backend, a Taylor model and an exact
symbolic rewrite. Each constructor either stores a given `ApproxOn` theorem or
derives one from other certificates.

## Main definitions

* `ApproxCert`: a function pair, an error budget, and the `ApproxOn` proof.
* `ApproxCert.trans`, `add`, `sub`, `neg`, `weightedSum`: composition with added budgets.
* `ApproxCert.mapLipschitz`, `mulReal`: propagation through a Lipschitz map and through
  products with known magnitude bounds.
* `ApproxCert.ofRealEnclosureAround`: conversion from enclosure certificates.

## Implementation notes

The `sound` field is the whole content of an `ApproxCert`. A certificate exists only once the
kernel has checked a proof of `ApproxOn lhs rhs s eps`; the two functions and the budget are
data that a planner, an interval evaluator or a Taylor backend may choose freely. They are
fields, not indices of the type, so each composite step computes its own budget (`trans` and
`add` add budgets, `weightedSum` takes `Σ |wᵢ| εᵢ`, `mapLipschitz` multiplies by the Lipschitz
constant, `union` takes the maximum), and `weaken` compares the result with a target afterwards.
Every rule is the triangle inequality or a product expansion. For `mulReal` we expand
`a b - a' b' = a (b - b') + b' (a - a')`, so only `|a.lhs|` and `|b.rhs|` need magnitude bounds.
`ofRealEnclosureAround` is the step where an interval evaluator returns a range: an enclosure
inside `[center - eps, center + eps]` becomes an approximation by the constant `center`.
-/

@[expose] public section

open scoped BigOperators

namespace CAS.Certificate

/--
A checked uniform approximation certificate on a domain.

The fields `lhs`, `rhs`, and `eps` make the certificate composable as data, and
`sound` proves the `ApproxOn` proposition. The budget is necessarily nonnegative on every
nonempty domain; equivalently, a negative budget certifies only an empty domain.
-/
structure ApproxCert (α E : Type*) [NormedAddCommGroup E] (s : Set α) where
  /-- Left-hand function. -/
  lhs : α → E
  /-- Right-hand/reference function. -/
  rhs : α → E
  /-- Uniform error budget.  It is nonnegative whenever `s` is nonempty. -/
  eps : ℝ
  /-- `lhs` is uniformly `eps`-close to `rhs` on `s`. -/
  sound : ApproxOn lhs rhs s eps

namespace ApproxCert

variable {α E : Type*} [NormedAddCommGroup E] {s : Set α}

/-- A checked real-valued approximation certificate gives the corresponding
pointwise interval enclosure. -/
theorem mem_Icc (c : ApproxCert α ℝ s) {x : α} (hx : x ∈ s) :
    c.lhs x ∈ Set.Icc (c.rhs x - c.eps) (c.rhs x + c.eps) := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp (c.sound x hx)
  constructor <;> linarith

/-! ## Error-budget invariant -/

/-- Every approximation budget on a nonempty domain is nonnegative. -/
theorem eps_nonneg (c : ApproxCert α E s) (hs : s.Nonempty) : 0 ≤ c.eps :=
  hs.elim fun x hx ↦ (norm_nonneg _).trans (c.sound x hx)

/-- A negative approximation budget can certify only the empty domain. -/
theorem eq_empty_of_eps_neg (c : ApproxCert α E s) (heps : c.eps < 0) : s = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx ↦ not_lt_of_ge (c.eps_nonneg ⟨x, hx⟩) heps

/-- An approximation budget is nonnegative unless its certified domain is empty. -/
theorem eps_nonneg_or_eq_empty (c : ApproxCert α E s) : 0 ≤ c.eps ∨ s = ∅ :=
  (le_or_gt 0 c.eps).imp_right c.eq_empty_of_eps_neg

/-! ## Constructors and structural rules -/

/-- The certificate of an existing approximation theorem. -/
def ofApproxOn (f g : α → E) (eps : ℝ) (h : ApproxOn f g s eps) :
    ApproxCert α E s where
  lhs := f
  rhs := g
  eps := eps
  sound := h

/-- Reflexivity certificate. -/
def refl (f : α → E) (s : Set α) : ApproxCert α E s where
  lhs := f
  rhs := f
  eps := 0
  sound := approxOn_refl f s

/-- Symmetry of approximation certificates. -/
def symm (c : ApproxCert α E s) : ApproxCert α E s where
  lhs := c.rhs
  rhs := c.lhs
  eps := c.eps
  sound := approxOn_symm c.sound

/-- Weaken a certificate to a larger error budget. -/
def weaken (c : ApproxCert α E s) {eps' : ℝ} (heps : c.eps ≤ eps') :
    ApproxCert α E s where
  lhs := c.lhs
  rhs := c.rhs
  eps := eps'
  sound := approxOn_mono_error c.sound heps

/-- Restrict an approximation certificate to a smaller patch. -/
def restrict (c : ApproxCert α E s) (t : Set α) (hsub : t ⊆ s) :
    ApproxCert α E t where
  lhs := c.lhs
  rhs := c.rhs
  eps := c.eps
  sound := approxOn_mono_domain c.sound hsub

/-- Restricting a certificate to a smaller patch keeps its left-hand function. -/
@[simp]
theorem restrict_lhs (c : ApproxCert α E s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).lhs = c.lhs :=
  rfl

/-- Restricting a certificate to a smaller patch keeps its reference function. -/
@[simp]
theorem restrict_rhs (c : ApproxCert α E s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).rhs = c.rhs :=
  rfl

/-- Restricting a certificate to a smaller patch keeps its error budget. -/
@[simp]
theorem restrict_eps (c : ApproxCert α E s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).eps = c.eps :=
  rfl

/-- Expose domain restriction directly as an ordinary approximation theorem. -/
theorem sound_restrict (c : ApproxCert α E s) (t : Set α) (hsub : t ⊆ s) :
    ApproxOn c.lhs c.rhs t c.eps :=
  (c.restrict t hsub).sound

/-- Compose two approximation certificates whose middle functions agree. -/
def trans (a b : ApproxCert α E s) (hmid : a.rhs = b.lhs) :
    ApproxCert α E s where
  lhs := a.lhs
  rhs := b.rhs
  eps := a.eps + b.eps
  sound := by
    have hb : ApproxOn a.rhs b.rhs s b.eps := by
      simpa [hmid] using b.sound
    exact approxOn_trans a.sound hb

/--
Rewrite the right side of an approximation certificate by an exact equality on the same domain.

Exact symbolic certificates thus become zero-error steps in a
longer chain, and routes need not use syntactically identical endpoint
functions.
-/
def replaceRhs (c : ApproxCert α E s) (rhs' : α → E) (h : Set.EqOn c.rhs rhs' s) :
    ApproxCert α E s where
  lhs := c.lhs
  rhs := rhs'
  eps := c.eps
  sound := by
    simpa using approxOn_trans c.sound (approxOn_of_eqOn h)

/--
Add two approximation certificates pointwise.

If `f ≈ g` with error `ε` and `h ≈ k` with error `δ`, then `f+h ≈ g+k` with
error `ε+δ`.  This is the certificate-level triangle inequality used by residual and numerical
error estimators.
-/
def add (a b : ApproxCert α E s) : ApproxCert α E s where
  lhs := fun x ↦ a.lhs x + b.lhs x
  rhs := fun x ↦ a.rhs x + b.rhs x
  eps := a.eps + b.eps
  sound := by
    intro x hx
    have hsplit :
        (a.lhs x + b.lhs x) - (a.rhs x + b.rhs x) =
          (a.lhs x - a.rhs x) + (b.lhs x - b.rhs x) := by
      abel
    calc
      ‖(a.lhs x + b.lhs x) - (a.rhs x + b.rhs x)‖
          = ‖(a.lhs x - a.rhs x) + (b.lhs x - b.rhs x)‖ := by rw [hsplit]
      _ ≤ ‖a.lhs x - a.rhs x‖ + ‖b.lhs x - b.rhs x‖ := norm_add_le _ _
      _ ≤ a.eps + b.eps := add_le_add (a.sound x hx) (b.sound x hx)

/-- Negate both sides of an approximation certificate. -/
def neg (c : ApproxCert α E s) : ApproxCert α E s where
  lhs := fun x ↦ -c.lhs x
  rhs := fun x ↦ -c.rhs x
  eps := c.eps
  sound := by
    intro x hx
    have hneg : (-c.lhs x) - (-c.rhs x) = -(c.lhs x - c.rhs x) := by
      abel
    calc
      ‖(-c.lhs x) - (-c.rhs x)‖ = ‖-(c.lhs x - c.rhs x)‖ := by rw [hneg]
      _ = ‖c.lhs x - c.rhs x‖ := norm_neg _
      _ ≤ c.eps := c.sound x hx

/--
Subtract two approximation certificates pointwise.

This is implemented as addition with `neg`, so the error budget is again the sum of the two local
budgets.
-/
def sub (a b : ApproxCert α E s) : ApproxCert α E s where
  lhs := fun x ↦ a.lhs x - b.lhs x
  rhs := fun x ↦ a.rhs x - b.rhs x
  eps := a.eps + b.eps
  sound := by
    have h := (a.add b.neg).sound
    simpa [ApproxCert.add, ApproxCert.neg, sub_eq_add_neg] using h

/-! ## Nonlinear propagation -/

/--
Push an approximation certificate through a Lipschitz map.

If `φ` has Lipschitz constant `L` and `f ≈ g` with error `ε`, then
`φ ∘ f ≈ φ ∘ g` with error `L * ε`. Nonlinear post-processing of any
approximation, whether it came from an exact symbolic route or an interval
enclosure, goes through this rule.
-/
def mapLipschitz {F : Type*} [NormedAddCommGroup F]
    (c : ApproxCert α E s) (φ : E → F) (L : ℝ) (hL : 0 ≤ L)
    (hφ : ∀ x y, ‖φ x - φ y‖ ≤ L * ‖x - y‖) :
    ApproxCert α F s where
  lhs := fun x ↦ φ (c.lhs x)
  rhs := fun x ↦ φ (c.rhs x)
  eps := L * c.eps
  sound := by
    intro x hx
    exact le_trans (hφ (c.lhs x) (c.rhs x))
      (mul_le_mul_of_nonneg_left (c.sound x hx) hL)

/-! ## Finite assembly -/

/--
Weighted finite sum of approximation certificates.

Certified quadrature and weighted residual assembly both reduce to this. For real weights `wᵢ`,
a component error `εᵢ` contributes `|wᵢ| εᵢ` to the final error budget. The target is any normed
real vector space, which covers scalar residuals, vector residuals, and projected weak-form
integrals.
-/
noncomputable def weightedSum {ι : Type*} [Fintype ι]
    [NormedSpace ℝ E] (w : ι → ℝ) (c : ι → ApproxCert α E s) :
    ApproxCert α E s where
  lhs := fun x ↦ ∑ i, w i • (c i).lhs x
  rhs := fun x ↦ ∑ i, w i • (c i).rhs x
  eps := ∑ i, |w i| * (c i).eps
  sound := by
    intro x hx
    have hsplit :
        (∑ i, w i • (c i).lhs x) - (∑ i, w i • (c i).rhs x) =
          ∑ i, w i • ((c i).lhs x - (c i).rhs x) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [smul_sub]
    calc
      ‖(∑ i, w i • (c i).lhs x) - (∑ i, w i • (c i).rhs x)‖
          = ‖∑ i, w i • ((c i).lhs x - (c i).rhs x)‖ := by rw [hsplit]
      _ ≤ ∑ i, ‖w i • ((c i).lhs x - (c i).rhs x)‖ := by
        simpa using norm_sum_le Finset.univ
          (fun i ↦ w i • ((c i).lhs x - (c i).rhs x))
      _ ≤ ∑ i, |w i| * (c i).eps := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        calc
          ‖w i • ((c i).lhs x - (c i).rhs x)‖
              = |w i| * ‖(c i).lhs x - (c i).rhs x‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |w i| * (c i).eps :=
            mul_le_mul_of_nonneg_left ((c i).sound x hx) (abs_nonneg _)

/-! ## Product propagation -/

/--
Multiply two real-valued approximation certificates under explicit local magnitude bounds.

If `a.lhs ≈ a.rhs` with error `ε`, `b.lhs ≈ b.rhs` with error `δ`, and on the same
patch we know `|a.lhs| ≤ A` and `|b.rhs| ≤ B`, then

`a.lhs * b.lhs ≈ a.rhs * b.rhs`

with error `A * δ + B * ε`.

The bounds are asymmetric because the proof expands

`a.lhs*b.lhs - a.rhs*b.rhs =
  a.lhs*(b.lhs-b.rhs) + b.rhs*(a.lhs-a.rhs)`,

so only the left factor of the first certificate and the reference factor of the second need
magnitude bounds. Other variants follow by symmetry or by replacing certificate endpoints with
exact zero-error steps.
-/
def mulReal {α : Type*} {s : Set α} (a b : ApproxCert α ℝ s)
    (A B : ℝ)
    (hA : BoundOn (fun x ↦ |a.lhs x|) s A)
    (hB : BoundOn (fun x ↦ |b.rhs x|) s B) :
    ApproxCert α ℝ s where
  lhs := fun x ↦ a.lhs x * b.lhs x
  rhs := fun x ↦ a.rhs x * b.rhs x
  eps := A * b.eps + B * a.eps
  sound := by
    intro x hx
    have hexpand :
        a.lhs x * b.lhs x - a.rhs x * b.rhs x =
          a.lhs x * (b.lhs x - b.rhs x) + b.rhs x * (a.lhs x - a.rhs x) := by
      ring
    have hterm₁ :
        |a.lhs x * (b.lhs x - b.rhs x)| ≤ A * b.eps := by
      calc
        |a.lhs x * (b.lhs x - b.rhs x)|
            = |a.lhs x| * |b.lhs x - b.rhs x| := abs_mul _ _
        _ ≤ A * b.eps :=
            mul_le_mul (hA x hx) (b.sound x hx) (abs_nonneg _) (le_trans (abs_nonneg _) (hA x hx))
    have hterm₂ :
        |b.rhs x * (a.lhs x - a.rhs x)| ≤ B * a.eps := by
      calc
        |b.rhs x * (a.lhs x - a.rhs x)|
            = |b.rhs x| * |a.lhs x - a.rhs x| := abs_mul _ _
        _ ≤ B * a.eps :=
            mul_le_mul (hB x hx) (a.sound x hx) (abs_nonneg _) (le_trans (abs_nonneg _) (hB x hx))
    calc
      ‖a.lhs x * b.lhs x - a.rhs x * b.rhs x‖
          = |a.lhs x * b.lhs x - a.rhs x * b.rhs x| := Real.norm_eq_abs _
      _ = |a.lhs x * (b.lhs x - b.rhs x) + b.rhs x * (a.lhs x - a.rhs x)| := by
        rw [hexpand]
      _ ≤ |a.lhs x * (b.lhs x - b.rhs x)| + |b.rhs x * (a.lhs x - a.rhs x)| :=
        abs_add_le _ _
      _ ≤ A * b.eps + B * a.eps := add_le_add hterm₁ hterm₂

/--
Multiply two real-valued approximation certificates using magnitude-bound certificates.

The same as `mulReal`, with the magnitude bounds for `|a.lhs|` and `|b.rhs|` supplied as
`BoundCert`s, which is what interval routes return.
-/
def mulRealOfBoundCerts {α : Type*} {s : Set α} (a b : ApproxCert α ℝ s)
    (boundLhs : BoundCert α s) (boundRhs : BoundCert α s)
    (hLhs : boundLhs.fn = fun x ↦ |a.lhs x|)
    (hRhs : boundRhs.fn = fun x ↦ |b.rhs x|) :
    ApproxCert α ℝ s :=
  a.mulReal b boundLhs.upper boundRhs.upper
    (by
      intro x hx
      simpa [hLhs] using boundLhs.sound x hx)
    (by
      intro x hx
      simpa [hRhs] using boundRhs.sound x hx)

/-! ## Patch gluing and residual bridges -/

/-- Glue approximation certificates on two patches.

The functions must agree extensionally as Lean functions; the combined error is
the maximum of the two local error budgets. -/
def union {t : Set α} (a : ApproxCert α E s) (b : ApproxCert α E t)
    (hlhs : a.lhs = b.lhs) (hrhs : a.rhs = b.rhs) :
    ApproxCert α E (s ∪ t) where
  lhs := a.lhs
  rhs := a.rhs
  eps := max a.eps b.eps
  sound := by
    intro x hx
    rcases hx with hx | hx
    · exact le_trans (a.sound x hx) (le_max_left a.eps b.eps)
    · have hb : ‖a.lhs x - a.rhs x‖ ≤ b.eps := by
        simpa [hlhs.symm, hrhs.symm] using b.sound x hx
      exact le_trans hb (le_max_right a.eps b.eps)

/-- A zero-error approximation certificate gives equality on the domain. -/
theorem eqOn_of_eps_eq_zero (c : ApproxCert α E s) (heps : c.eps = 0) :
    Set.EqOn c.lhs c.rhs s :=
  eqOn_of_approxOn_zero (by simpa [heps] using c.sound)

/-- A residual bound as approximation by zero. -/
def ofResidualBound (residual : α → E) (eps : ℝ)
    (h : ResidualBound residual s eps) : ApproxCert α E s where
  lhs := residual
  rhs := fun _ ↦ 0
  eps := eps
  sound := h

/--
Turn a real enclosure into an approximation by a chosen representative value.

If `f` is enclosed in `[lo, hi]` and that interval lies inside
`[center - eps, center + eps]`, then `f` is uniformly `eps`-close to the constant
representative `center`.  This is the usual numerical step
where an interval evaluator returns a range and CEGA records the corresponding
approximation radius.
-/
def ofRealEnclosureAround (c : EnclosureCert α s) (center eps : ℝ)
    (hlo : center - eps ≤ c.lo) (hhi : c.hi ≤ center + eps) :
    ApproxCert α ℝ s where
  lhs := c.fn
  rhs := fun _ ↦ center
  eps := eps
  sound := by
    intro x hx
    have henc := c.sound x hx
    have hlower : -eps ≤ c.fn x - center := by
      linarith
    have hupper : c.fn x - center ≤ eps := by
      linarith
    simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hlower, hupper⟩)

end ApproxCert

end CAS.Certificate
