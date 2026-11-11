/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Normed.Group.Real

/-!
# Semantic relations for certified continuum computation

The relations that CEGA certificates prove: uniform approximation, upper
bounds, two-sided enclosures, and residual bounds on a domain. They are
ordinary Lean propositions. Certificates store proofs of them, routes compose
certificates and project back to them, and the tactics close goals by reducing
to them. Planners may search over charts and edges, but an accepted result is
always a theorem about one of these relations.

## Main definitions

* `ApproxOn f g s ε`: `‖f x - g x‖ ≤ ε` for every `x ∈ s`, the uniform approximation
  relation that every CEGA route eventually certifies.
* `BoundOn`, `EnclosedOn`: one-sided and two-sided pointwise real bounds on a domain.
* `ResidualBound`: `ApproxOn residual 0 s ε`, the form in which PDE residual checks arrive.

## Main results

* `approxOn_refl`, `approxOn_symm`, `approxOn_trans`, `approxOn_mono_error`,
  `approxOn_mono_domain`, `approxOn_union`: the laws that let certificates be composed,
  reversed, weakened, restricted, and glued along a cover; `boundOn_union`, `enclosedOn_union`
  and `residualBound_union` glue the other relations.
* `approxOn_of_difference_residualBound`, `difference_residualBound_of_approxOn`: an
  approximation of `f` by `g` is a residual bound on `f - g`, and conversely.
* `enclosedOn_add`, `enclosedOn_sub`, `enclosedOn_scale_nonneg`, `enclosedOn_scale_nonpos`,
  `enclosedOn_mul_nonneg`: the interval-arithmetic composition rules stated directly for
  enclosures of functions.
* `eqOn_of_approxOn_zero`, `eqOn_zero_of_residualBound_zero`: a zero error budget is the
  same thing as pointwise equality on the domain.

## Implementation notes

Every statement here is an elementary consequence of the triangle inequality and the
order axioms of `ℝ`.

The certificates `EnclosureCert`, `BoundCert`, `ApproxCert`, and `ResidualCert` are structures
that store the function being certified, its bounds or error budget on a domain, and, in the
`sound` field, a proof of one of these relations, so evaluators, planners, routes, and tactics
can pass the theorem around as data; the atlases glue them over a `PatchCover`. We keep one-off
hypotheses as explicit theorem arguments. Route steps, backend labels, and search traces are
metadata and never stand in for a `sound` field. We add a certificate type only for a new
semantic relation or a reusable composition law, not for a shorter statement of one theorem.

The modules of `CAS.Certificate` import only Mathlib, modules of `CAS.Domain`, and each other,
never calculator commands, tactic frontends, or interval planners: numerical algorithms
construct certificates, and CEGA routes and tactics project their theorems. Theorems apply
them through `CAS.CEGA`, and the numerical constructors are in the modules under
`CAS/Continuum`. The predicates `PositiveOn` and `NonzeroOn` are in `CAS.Domain.SideConditions`,
and the expression-indexed nonvanishing certificates `ExprNonzeroCert` in
`CAS.Exact.ExpressionSideConditions`.
-/

@[expose] public section

namespace CAS.Certificate

/-!
## Semantic vocabulary

Every certificate of the symbolic layer proves one of these propositions.
-/

/--
Uniform approximation of two functions on a domain, measured in a normed target.

This is the main CEGA refinement relation.  Exact symbolic equality is the case
`ε = 0`; interval, Taylor and quadrature routes normally produce positive `ε`.
On the empty domain the proposition is vacuous, so it does not by itself force `ε`
to be nonnegative.  The certificate structures prove that `ε` is nonnegative unless
the domain is empty.
-/
def ApproxOn {α E : Type*} [NormedAddCommGroup E]
    (f g : α → E) (s : Set α) (ε : ℝ) : Prop :=
  ∀ x, x ∈ s → ‖f x - g x‖ ≤ ε

/--
A pointwise upper bound on a real-valued function over a domain.

It supplies the magnitude bounds needed by Lipschitz propagation and by product and
quotient estimates.
-/
def BoundOn {α : Type*} (f : α → ℝ) (s : Set α) (c : ℝ) : Prop :=
  ∀ x, x ∈ s → f x ≤ c

/--
A pointwise two-sided real enclosure over a domain.

Interval backends and validated numerical routines usually produce this first;
it can then be projected to a bound, residual estimate, or midpoint
approximation certificate.
-/
def EnclosedOn {α : Type*} (f : α → ℝ) (s : Set α) (lo hi : ℝ) : Prop :=
  ∀ x, x ∈ s → lo ≤ f x ∧ f x ≤ hi

/--
A residual bound is approximation of a residual by zero on a domain.

After an ansatz is differentiated and its residual simplified, the exact
symbolic routes prove `ε = 0` and validated numerical CEGA proves a positive
tolerance.
-/
def ResidualBound {α E : Type*} [NormedAddCommGroup E]
    (residual : α → E) (s : Set α) (ε : ℝ) : Prop :=
  ApproxOn residual (fun _ ↦ 0) s ε

/-- A zero residual budget forces exact equality with the zero function.

Once a certificate has reduced its error budget to zero, exact equality follows without any
backend-specific theorem. -/
theorem eqOn_zero_of_residualBound_zero {α E : Type*} [NormedAddCommGroup E]
    {residual : α → E} {s : Set α} (h : ResidualBound residual s 0) :
    Set.EqOn residual (fun _ ↦ 0) s := fun x hx ↦
  norm_le_zero_iff.mp (by simpa [ResidualBound, ApproxOn] using h x hx)

/-! ## Residual/approximation bridges -/

/-- A bound on the explicit difference residual `f - g` is exactly a uniform approximation
claim for `f` by `g`.

Symbolic routes and interval evaluators usually certify a residual expression, while theorems
are stated as `ApproxOn f g s ε`. This lemma connects the two for exact symbolic results, Taylor
truncation, quadrature, and PDE residual checks alike. -/
theorem approxOn_of_difference_residualBound {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} {ε : ℝ}
    (h : ResidualBound (fun x ↦ f x - g x) s ε) :
    ApproxOn f g s ε := fun x hx ↦ by
  simpa [ResidualBound, ApproxOn] using h x hx

/-- The converse of `approxOn_of_difference_residualBound`.

This is useful when a theorem is naturally stated as `ApproxOn f g s ε`, but a downstream planner
wants to keep manipulating the residual function `fun x ↦ f x - g x`. -/
theorem difference_residualBound_of_approxOn {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} {ε : ℝ}
    (h : ApproxOn f g s ε) :
    ResidualBound (fun x ↦ f x - g x) s ε := fun x hx ↦ by
  simpa [ResidualBound, ApproxOn] using h x hx

/-!
## Enclosure and bound laws

Interval and range-analysis backends normally prove `EnclosedOn` first.  These
projection and composition lemmas turn that two-sided information into weaker
facts such as upper bounds, residual bounds, and monotone interval products.
The certificate modules turn these lemmas into certificate constructors.
-/

/-- Widen an enclosure: lowering the lower endpoint or raising the upper one keeps it valid. -/
theorem enclosedOn_mono {α : Type*} {f : α → ℝ} {s : Set α} {lo hi lo' hi' : ℝ}
    (h : EnclosedOn f s lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    EnclosedOn f s lo' hi' := fun x hx ↦ ⟨hlo.trans (h x hx).1, (h x hx).2.trans hhi⟩

/-- Restrict an upper-bound claim to a smaller patch. -/
theorem boundOn_mono_domain {α : Type*} {f : α → ℝ} {s t : Set α} {c : ℝ}
    (h : BoundOn f s c) (hsub : t ⊆ s) : BoundOn f t c := fun x hx ↦ h x (hsub hx)

/-- Weaken an upper-bound claim to a larger bound. -/
theorem boundOn_mono {α : Type*} {f : α → ℝ} {s : Set α} {c d : ℝ}
    (h : BoundOn f s c) (hcd : c ≤ d) : BoundOn f s d := fun x hx ↦ (h x hx).trans hcd

/-- Transport an upper-bound claim across pointwise function equality and domain restriction. -/
theorem boundOn_congr {α : Type*} {f g : α → ℝ} {s t : Set α} {c : ℝ}
    (h : BoundOn f s c) (hsub : t ⊆ s) (hfg : Set.EqOn g f t) :
    BoundOn g t c := fun x hx ↦ hfg hx ▸ h x (hsub hx)

/-- Restrict a two-sided enclosure to a smaller patch. -/
theorem enclosedOn_mono_domain {α : Type*} {f : α → ℝ} {s t : Set α} {lo hi : ℝ}
    (h : EnclosedOn f s lo hi) (hsub : t ⊆ s) : EnclosedOn f t lo hi := fun x hx ↦ h x (hsub hx)

/-- Transport a two-sided enclosure across pointwise function equality and domain restriction. -/
theorem enclosedOn_congr {α : Type*} {f g : α → ℝ} {s t : Set α} {lo hi : ℝ}
    (h : EnclosedOn f s lo hi) (hsub : t ⊆ s) (hfg : Set.EqOn g f t) :
    EnclosedOn g t lo hi := fun x hx ↦ hfg hx ▸ h x (hsub hx)

/-- Glue upper bounds on two patches to an upper bound on their union. -/
theorem boundOn_union {α : Type*} {f : α → ℝ} {s t : Set α} {c : ℝ}
    (hs : BoundOn f s c) (ht : BoundOn f t c) : BoundOn f (s ∪ t) c := fun x hx ↦
  hx.elim (hs x) (ht x)

/-- Glue two-sided enclosures on two patches to a two-sided enclosure on their union. -/
theorem enclosedOn_union {α : Type*} {f : α → ℝ} {s t : Set α} {lo hi : ℝ}
    (hs : EnclosedOn f s lo hi) (ht : EnclosedOn f t lo hi) :
    EnclosedOn f (s ∪ t) lo hi := fun x hx ↦ hx.elim (hs x) (ht x)

/-- Forget the lower endpoint of an enclosure and keep only the upper bound. -/
theorem enclosedOn_upper {α : Type*} {f : α → ℝ} {s : Set α} {lo hi : ℝ}
    (h : EnclosedOn f s lo hi) : BoundOn f s hi := fun x hx ↦ (h x hx).2

/-- An enclosure `lo ≤ residual ≤ hi` with `[lo, hi] ⊆ [-ε, ε]` is a residual bound of size
`ε`. This is how an interval evaluation of a PDE residual becomes an `ApproxOn` certificate;
the two endpoint hypotheses are exactly the containment `[lo, hi] ⊆ [-ε, ε]`. -/
theorem enclosedOn_residualBound {α : Type*} {residual : α → ℝ} {s : Set α}
    {lo hi ε : ℝ}
    (h : EnclosedOn residual s lo hi)
    (hlo : -ε ≤ lo) (hhi : hi ≤ ε) :
    ResidualBound residual s ε := fun x hx ↦ by
  simpa [ResidualBound, ApproxOn, Real.norm_eq_abs] using
    abs_le.mpr ⟨hlo.trans (h x hx).1, (h x hx).2.trans hhi⟩

/-- A constant function is enclosed by the degenerate interval `[c, c]` on any domain. -/
theorem enclosedOn_const {α : Type*} (c : ℝ) (s : Set α) :
    EnclosedOn (fun _ : α ↦ c) s c c := fun _ _ ↦ ⟨le_rfl, le_rfl⟩

/-- Interval addition: enclosures of `f` and `g` add endpoint-wise to enclose `f + g`. -/
theorem enclosedOn_add {α : Type*} {f g : α → ℝ} {s : Set α}
    {loF hiF loG hiG : ℝ}
    (hf : EnclosedOn f s loF hiF) (hg : EnclosedOn g s loG hiG) :
    EnclosedOn (fun x ↦ f x + g x) s (loF + loG) (hiF + hiG) := fun x hx ↦
  ⟨add_le_add (hf x hx).1 (hg x hx).1, add_le_add (hf x hx).2 (hg x hx).2⟩

/-- Negation reflects an enclosure: `-f` lies in `[-hi, -lo]`. -/
theorem enclosedOn_neg {α : Type*} {f : α → ℝ} {s : Set α} {lo hi : ℝ}
    (hf : EnclosedOn f s lo hi) :
    EnclosedOn (fun x ↦ -f x) s (-hi) (-lo) := fun x hx ↦
  ⟨neg_le_neg (hf x hx).2, neg_le_neg (hf x hx).1⟩

/-- Interval subtraction: `f - g` lies in `[loF - hiG, hiF - loG]`. -/
theorem enclosedOn_sub {α : Type*} {f g : α → ℝ} {s : Set α}
    {loF hiF loG hiG : ℝ}
    (hf : EnclosedOn f s loF hiF) (hg : EnclosedOn g s loG hiG) :
    EnclosedOn (fun x ↦ f x - g x) s (loF - hiG) (hiF - loG) := by
  simpa [sub_eq_add_neg] using enclosedOn_add hf (enclosedOn_neg hg)

/-- Scaling by a nonnegative constant `c` scales both endpoints of an enclosure by `c`. -/
theorem enclosedOn_scale_nonneg {α : Type*} {f : α → ℝ} {s : Set α}
    {lo hi c : ℝ}
    (hc : 0 ≤ c) (hf : EnclosedOn f s lo hi) :
    EnclosedOn (fun x ↦ c * f x) s (c * lo) (c * hi) := fun x hx ↦
  ⟨mul_le_mul_of_nonneg_left (hf x hx).1 hc, mul_le_mul_of_nonneg_left (hf x hx).2 hc⟩

/-- Scaling by a nonpositive constant `c` scales the endpoints by `c` and swaps them. -/
theorem enclosedOn_scale_nonpos {α : Type*} {f : α → ℝ} {s : Set α}
    {lo hi c : ℝ}
    (hc : c ≤ 0) (hf : EnclosedOn f s lo hi) :
    EnclosedOn (fun x ↦ c * f x) s (c * hi) (c * lo) := fun x hx ↦
  ⟨mul_le_mul_of_nonpos_left (hf x hx).2 hc, mul_le_mul_of_nonpos_left (hf x hx).1 hc⟩

/-- Interval multiplication in the special case where both enclosures lie in `[0, ∞)`: then the
product is enclosed by the product of the endpoints. The sign hypotheses `0 ≤ loF`, `0 ≤ loG`
avoid the four-way case split of general interval multiplication; backends that need mixed
signs split the domain first. -/
theorem enclosedOn_mul_nonneg {α : Type*} {f g : α → ℝ} {s : Set α}
    {loF hiF loG hiG : ℝ}
    (hf : EnclosedOn f s loF hiF) (hg : EnclosedOn g s loG hiG)
    (hloF : 0 ≤ loF) (hloG : 0 ≤ loG) :
    EnclosedOn (fun x ↦ f x * g x) s (loF * loG) (hiF * hiG) := by
  intro x hx
  obtain ⟨hf₁, hf₂⟩ := hf x hx
  obtain ⟨hg₁, hg₂⟩ := hg x hx
  exact ⟨mul_le_mul hf₁ hg₁ hloG (hloF.trans hf₁),
    mul_le_mul hf₂ hg₂ (hloG.trans hg₁) ((hloF.trans hf₁).trans hf₂)⟩

/-!
## Uniform approximation laws

Algebraic laws for `ApproxOn`: reflexivity, symmetry, transitivity with
added errors, domain restriction, and gluing over patches.
-/

/-- Every function approximates itself with zero error. -/
theorem approxOn_refl {α E : Type*} [NormedAddCommGroup E]
    (f : α → E) (s : Set α) : ApproxOn f f s 0 := fun x _ ↦ by simp

/-- Uniform approximation is symmetric, since `‖g x - f x‖ = ‖f x - g x‖`. -/
theorem approxOn_symm {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} {ε : ℝ}
    (h : ApproxOn f g s ε) : ApproxOn g f s ε := fun x hx ↦
  (norm_sub_rev _ _).trans_le (h x hx)

/-- Errors add along a chain of approximations: this is the triangle inequality applied
pointwise, and it is the rule by which multi-step CEGA routes accumulate their tolerance. -/
theorem approxOn_trans {α E : Type*} [NormedAddCommGroup E]
    {f g h : α → E} {s : Set α} {ε δ : ℝ}
    (hfg : ApproxOn f g s ε) (hgh : ApproxOn g h s δ) :
    ApproxOn f h s (ε + δ) := fun x hx ↦
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hfg x hx) (hgh x hx))

/-- An approximation with error `ε` is also one with any larger error `δ`. -/
theorem approxOn_mono_error {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} {ε δ : ℝ}
    (h : ApproxOn f g s ε) (hεδ : ε ≤ δ) : ApproxOn f g s δ := fun x hx ↦ (h x hx).trans hεδ

/-- Restrict an approximation claim to a smaller patch. -/
theorem approxOn_mono_domain {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s t : Set α} {ε : ℝ}
    (h : ApproxOn f g s ε) (hsub : t ⊆ s) : ApproxOn f g t ε := fun x hx ↦ h x (hsub hx)

/--
Transport an approximation across pointwise equality of both functions and
domain restriction.
-/
theorem approxOn_congr {α E : Type*} [NormedAddCommGroup E]
    {f g f' g' : α → E} {s t : Set α} {ε : ℝ}
    (h : ApproxOn f g s ε) (hsub : t ⊆ s)
    (hf : Set.EqOn f' f t) (hg : Set.EqOn g' g t) :
    ApproxOn f' g' t ε := fun x hx ↦ by
  simpa [hf hx, hg hx] using h x (hsub hx)

/-- Glue approximations on two patches to an approximation on their union. -/
theorem approxOn_union {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s t : Set α} {ε : ℝ}
    (hs : ApproxOn f g s ε) (ht : ApproxOn f g t ε) :
    ApproxOn f g (s ∪ t) ε := fun x hx ↦ hx.elim (hs x) (ht x)

/-- Pointwise equality on the domain is uniform approximation with error `0`; together with
`eqOn_of_approxOn_zero` this identifies exact symbolic results with the `ε = 0` case. -/
theorem approxOn_of_eqOn {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} (h : Set.EqOn f g s) :
    ApproxOn f g s 0 := fun x hx ↦ by simp [h hx]

/-- In a normed additive group, zero uniform approximation gives equality on the domain. -/
theorem eqOn_of_approxOn_zero {α E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {s : Set α} (h : ApproxOn f g s 0) :
    Set.EqOn f g s := fun x hx ↦ sub_eq_zero.mp (norm_le_zero_iff.mp (h x hx))

/-!
## Residual-bound laws

A residual bound is a uniform approximation to zero, so PDE residual checks,
Taylor and interval estimates, and exact symbolic zero proofs all use the same
route and certificate machinery.
-/

/-- Restrict a residual bound to a smaller patch. -/
theorem residualBound_mono_domain {α E : Type*} [NormedAddCommGroup E]
    {residual : α → E} {s t : Set α} {ε : ℝ}
    (h : ResidualBound residual s ε) (hsub : t ⊆ s) :
    ResidualBound residual t ε :=
  approxOn_mono_domain h hsub

/-- Glue residual bounds on two patches to a residual bound on their union. -/
theorem residualBound_union {α E : Type*} [NormedAddCommGroup E]
    {residual : α → E} {s t : Set α} {ε : ℝ}
    (hs : ResidualBound residual s ε) (ht : ResidualBound residual t ε) :
    ResidualBound residual (s ∪ t) ε :=
  approxOn_union hs ht

end CAS.Certificate
