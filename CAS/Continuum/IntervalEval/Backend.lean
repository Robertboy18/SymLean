/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalBackend
public import CAS.Expr.Syntax

/-!
# Backend-neutral interval evaluation

`IntervalExprOps.eval` is the common executable traversal of the algebraic and
trigonometric fragment of `Verified.Expr`. A concrete implementation supplies
partial operations through `IntervalExprOps` and proves their enclosure
contracts through `IntervalExprBackend`; the recursion over the symbolic AST
and its induction proof are written once.

Every operation is partial. A backend may reject overflow, unsupported
constants, or unsupported transcendental ranges by returning `none`. The
generic evaluator propagates that failure and never substitutes an arbitrary
wide interval.

## Main definitions

* `IntervalExprOps`: a table of partial interval operations.
* `IntervalExprBackend`: the enclosure contract of each operation of a table.

## Main results

* `IntervalExprOps.eval`: the shared partial traversal of the algebraic and
  trigonometric fragment of `Verified.Expr`.
* `IntervalExprBackend.eval_sound`: the inclusion property for the whole
  expression, by induction on the AST from the per-operation contracts. If the
  environment intervals enclose the point `ρ` and evaluation succeeds, the result
  encloses `expr.eval ρ`.

## Implementation notes

Replacing every operation of the expression by its interval counterpart is Moore's natural
interval extension, and `eval_sound` is its inclusion property, proved the classical way: by
induction on the expression from the inclusion property of each operation. The contract is a
`Prop` structure kept apart from the executable table, so a table can compute while its proof
is used only when a successful result becomes a theorem. Two tables instantiate it, the exact
rational operations `RationalInterval.verifiedExprOps` and the precision-parametric
`DigitsEval.ops`. Division here calls the raw `div?`; division that consults the denominator
expression, the remaining elementary functions and real powers go through the callback layer
`IntervalExprOps.evalWithCallbacks`.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 5 for interval
  extensions of real functions and their fundamental properties.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Verified

universe u

/-- Executable operations used by the shared symbolic interval traversal. -/
structure IntervalExprOps (I : Type u) where
  /-- Enclose an exact rational constant. -/
  const? : ℚ → Option I
  /-- Optional enclosure of `π`. -/
  pi? : Option I
  /-- Optional enclosure of Euler's number. -/
  e? : Option I
  /-- Partial interval addition. -/
  add? : I → I → Option I
  /-- Partial interval multiplication. -/
  mul? : I → I → Option I
  /-- Partial interval natural power. -/
  pow? : I → Nat → Option I
  /-- Partial interval division. -/
  div? : I → I → Option I
  /-- Partial interval negation. -/
  neg? : I → Option I
  /-- Optional interval sine. -/
  sin? : I → Option I
  /-- Optional interval cosine. -/
  cos? : I → Option I

/--
Real-enclosure contract for an executable interval operation table.

The executable data and its soundness witness are separate structures.
Concrete backends whose real semantics are noncomputable, such as exact
IEEE-754 decoding into `ℝ`, can still run `IntervalExprOps.eval`; proofs use
the corresponding `IntervalExprBackend` only when promoting a successful
computation to a theorem.
-/
structure IntervalExprBackend {I : Type u} (ops : IntervalExprOps I)
    [RealIntervalBackend I] : Prop where
  /-- Rational constants are enclosed when construction succeeds. -/
  const_sound :
    ∀ q result, ops.const? q = some result →
      RealIntervalBackend.MemReal result (q : ℝ)
  /-- The optional `π` interval is sound. -/
  pi_sound :
    ∀ result, ops.pi? = some result →
      RealIntervalBackend.MemReal result Real.pi
  /-- The optional Euler interval is sound. -/
  e_sound :
    ∀ result, ops.e? = some result →
      RealIntervalBackend.MemReal result (Real.exp 1)
  /-- Successful addition encloses the exact sum. -/
  add_sound :
    ∀ A B result x y, ops.add? A B = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal B y →
      RealIntervalBackend.MemReal result (x + y)
  /-- Successful multiplication encloses the exact product. -/
  mul_sound :
    ∀ A B result x y, ops.mul? A B = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal B y →
      RealIntervalBackend.MemReal result (x * y)
  /-- Successful natural-power evaluation encloses the exact real power. -/
  pow_sound :
    ∀ A k result x, ops.pow? A k = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal result (x ^ k)
  /-- Successful division encloses the exact quotient. -/
  div_sound :
    ∀ A B result x y, ops.div? A B = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal B y →
      RealIntervalBackend.MemReal result (x / y)
  /-- Successful negation encloses the exact negation. -/
  neg_sound :
    ∀ A result x, ops.neg? A = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal result (-x)
  /-- Successful sine evaluation encloses the exact sine. -/
  sin_sound :
    ∀ A result x, ops.sin? A = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal result (Real.sin x)
  /-- Successful cosine evaluation encloses the exact cosine. -/
  cos_sound :
    ∀ A result x, ops.cos? A = some result →
      RealIntervalBackend.MemReal A x →
      RealIntervalBackend.MemReal result (Real.cos x)

namespace IntervalExprOps

variable {I : Type u}

/-- Derived subtraction, preserving backend failure. -/
def sub? (ops : IntervalExprOps I) (A B : I) : Option I := do
  let negB ← ops.neg? B
  ops.add? A negB

/--
Evaluate the backend-supported fragment of a verified expression.

Malformed rational literals and unsupported operations return `none`.
Division uses the backend's raw `div?` operation. Expression-dependent
denominator facts and advanced unary ranges require the callback layer.
-/
def eval (ops : IntervalExprOps I) {ι : Type*}
    (env : ι → I) : Verified.Expr ι → Option I
  | .nat n => ops.const? n
  | .int z => ops.const? z
  | .rat num den =>
      if den = 0 then none else ops.const? ((num : ℚ) / (den : ℚ))
  | .pi => ops.pi?
  | .e => ops.e?
  | .var i => some (env i)
  | .add a b => do
      let IA ← ops.eval env a
      let IB ← ops.eval env b
      ops.add? IA IB
  | .mul a b => do
      let IA ← ops.eval env a
      let IB ← ops.eval env b
      ops.mul? IA IB
  | .sub a b => do
      let IA ← ops.eval env a
      let IB ← ops.eval env b
      ops.sub? IA IB
  | .div a b => do
      let IA ← ops.eval env a
      let IB ← ops.eval env b
      ops.div? IA IB
  | .neg a => do
      let IA ← ops.eval env a
      ops.neg? IA
  | .pow a k => do
      let IA ← ops.eval env a
      ops.pow? IA k
  | .sin a => do
      let IA ← ops.eval env a
      ops.sin? IA
  | .cos a => do
      let IA ← ops.eval env a
      ops.cos? IA
  | .atan _ | .asin _ | .acos _ | .exp _ | .log _ | .sqrt _ => none
  | .rpow _ _ => none

end IntervalExprOps

namespace IntervalExprBackend

variable {I : Type u} [RealIntervalBackend I] {ops : IntervalExprOps I}

/-- Successful derived subtraction encloses exact subtraction. -/
theorem sub?_sound (backend : IntervalExprBackend ops)
    {A B result : I} {x y : ℝ}
    (hresult : ops.sub? A B = some result)
    (hx : RealIntervalBackend.MemReal A x)
    (hy : RealIntervalBackend.MemReal B y) :
    RealIntervalBackend.MemReal result (x - y) := by
  simp only [IntervalExprOps.sub?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hresult
  obtain ⟨negB, hneg, h⟩ := hresult
  simpa [sub_eq_add_neg] using
    backend.add_sound A negB result x (-y) h hx (backend.neg_sound B negB y hneg hy)

/-- The shared partial evaluator encloses the expression whenever it succeeds. -/
theorem eval_sound (backend : IntervalExprBackend ops)
    {ι : Type*} (env : ι → I) (ρ : ι → ℝ)
    (henv : ∀ i, RealIntervalBackend.MemReal (env i) (ρ i)) :
    ∀ expr result, ops.eval env expr = some result →
      RealIntervalBackend.MemReal result (expr.eval ρ) := by
  intro expr
  induction expr <;> intro result hresult <;>
    simp only [IntervalExprOps.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hresult
  case nat n => exact backend.const_sound n result hresult
  case int z => exact backend.const_sound z result hresult
  case rat num den =>
    split_ifs at hresult
    simpa using backend.const_sound ((num : ℚ) / (den : ℚ)) result hresult
  case pi => exact backend.pi_sound result hresult
  case e => exact backend.e_sound result hresult
  case var i =>
    obtain rfl := Option.some.inj hresult
    exact henv i
  case add a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact backend.add_sound IA IB result _ _ h (iha IA hA) (ihb IB hB)
  case mul a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact backend.mul_sound IA IB result _ _ h (iha IA hA) (ihb IB hB)
  case sub a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact backend.sub?_sound h (iha IA hA) (ihb IB hB)
  case div a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact backend.div_sound IA IB result _ _ h (iha IA hA) (ihb IB hB)
  case neg a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact backend.neg_sound IA result _ h (iha IA hA)
  case pow a k iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact backend.pow_sound IA k result _ h (iha IA hA)
  case sin a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact backend.sin_sound IA result _ h (iha IA hA)
  case cos a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact backend.cos_sound IA result _ h (iha IA hA)
  all_goals cases hresult

end IntervalExprBackend

end CAS.Continuum
