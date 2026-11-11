/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Backend

/-!
# Provider callbacks for verified interval evaluation

The base evaluator handles operations whose interval semantics depend only on
their input intervals. Division with symbolic side conditions, branch-sensitive
unary functions and real powers may additionally depend on the original
argument expression and checked provider data.

`IntervalExprCallbacks` contains exactly those executable extension points.
`IntervalExprCallbacks.Sound` states their semantic contracts for one
environment. The shared `evalWithCallbacks` traversal and
`evalWithCallbacks_sound` theorem are independent of any concrete interval
representation or provider implementation.

## Main definitions

* `UnaryKind`: the unary operations whose ranges come from a provider.
* `IntervalExprCallbacks`, `IntervalExprCallbacks.Sound`: the callbacks and their contracts.
* `IntervalExprOps.evalWithCallbacks`: the traversal of the full `Verified.Expr`
  language, delegating `div`, the unary operations in `UnaryKind`, and the real
  power `rpow` to the callbacks.

## Main results

* `IntervalExprCallbacks.evalWithCallbacks_sound`: if the base operations
  satisfy `IntervalExprBackend` and the callbacks satisfy `Sound` for the
  environment `env` enclosing the point `ρ`, then every successful evaluation
  encloses `expr.eval ρ`.

## Implementation notes

The proof is the same induction as `IntervalExprBackend.eval_sound`; the callback cases use
`Sound`. Each callback contract assumes that the traversal computed the argument intervals it is
given, so a provider may tie an answer to the exact interval of the argument expression, and a
denominator fact proved for the expression `b` applies even when the interval of `b` contains
zero.

The unary operations are interpreted through Mathlib's total real functions
(`UnaryKind.apply`). For `log`, the singleton input `[0, 0]` therefore has
the exact range `[0, 0]`. A nontrivial interval containing zero also contains
nonzero points approaching zero, where `Real.log` is unbounded below; the
assigned value `Real.log 0 = 0` does not give that interval a finite range.
The rational registry handles the singleton zero and intervals bounded away
from zero, and rejects the remaining logarithm intervals.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Verified

universe u

/-- Unary operations whose ranges may be supplied by a checked provider. -/
inductive UnaryKind where
  /-- Reciprocal `x ↦ x⁻¹` (Lean's totalized inverse, `0⁻¹ = 0`). -/
  | inv
  /-- The real exponential. -/
  | exp
  /-- The real logarithm (Mathlib's total `Real.log`, with `log 0 = 0` and `log (-x) = log x`). -/
  | log
  /-- The real arctangent. -/
  | atan
  /-- The real arcsine (Mathlib's total `Real.arcsin`, clamped outside `[-1, 1]`). -/
  | asin
  /-- The real arccosine (Mathlib's total `Real.arccos`, clamped outside `[-1, 1]`). -/
  | acos
  /-- The real square root (Mathlib's total `Real.sqrt`, zero on negative inputs). -/
  | sqrt
deriving DecidableEq, Repr

namespace UnaryKind

/-- Real interpretation of a provider-supported unary operation. -/
noncomputable def apply : UnaryKind → ℝ → ℝ
  | .inv => fun x ↦ x⁻¹
  | .exp => Real.exp
  | .log => Real.log
  | .atan => Real.arctan
  | .asin => Real.arcsin
  | .acos => Real.arccos
  | .sqrt => Real.sqrt

/-- Compact label for provider diagnostics. -/
def label : UnaryKind → String
  | .inv => "inv"
  | .exp => "exp"
  | .log => "log"
  | .atan => "atan"
  | .asin => "asin"
  | .acos => "acos"
  | .sqrt => "sqrt"

end UnaryKind

/--
Expression-aware extension points for interval evaluation.

The division callback receives both original operand expressions, allowing a
provider to attach semantic denominator facts to the exact syntax being
evaluated. The generic unary callback handles `atan`, `asin`, `acos`, `exp`, `log`,
and `sqrt`; `.inv` is retained in `UnaryKind` because division providers use the
same certificate format for reciprocal ranges.
-/
structure IntervalExprCallbacks (I : Type u) (ι : Type*) where
  /-- Evaluate a quotient of two already enclosed arguments. -/
  div? : Verified.Expr ι → Verified.Expr ι → I → I → Option I
  /-- Evaluate an advanced unary operation on an already enclosed argument. -/
  unary? : UnaryKind → Verified.Expr ι → I → Option I
  /-- Evaluate a real power `a ^ b` of two already enclosed arguments.

  The default fails closed, so a backend without a real-power route rejects every
  `rpow` node instead of enclosing Mathlib's total `Real.rpow` at a nonpositive base. -/
  rpow? : Verified.Expr ι → Verified.Expr ι → I → I → Option I := fun _ _ _ _ ↦ none

namespace IntervalExprOps

variable {I : Type u} {ι : Type*}

/--
Evaluate the full verified-expression language, using the expression-aware callbacks for
division, the unary operations of `UnaryKind`, and real powers.
-/
def evalWithCallbacks (ops : IntervalExprOps I)
    (callbacks : IntervalExprCallbacks I ι) (env : ι → I) :
    Verified.Expr ι → Option I
  | .nat n => ops.const? n
  | .int z => ops.const? z
  | .rat num den =>
      if den = 0 then none else ops.const? ((num : ℚ) / (den : ℚ))
  | .pi => ops.pi?
  | .e => ops.e?
  | .var i => some (env i)
  | .add a b => do
      let IA ← ops.evalWithCallbacks callbacks env a
      let IB ← ops.evalWithCallbacks callbacks env b
      ops.add? IA IB
  | .mul a b => do
      let IA ← ops.evalWithCallbacks callbacks env a
      let IB ← ops.evalWithCallbacks callbacks env b
      ops.mul? IA IB
  | .sub a b => do
      let IA ← ops.evalWithCallbacks callbacks env a
      let IB ← ops.evalWithCallbacks callbacks env b
      ops.sub? IA IB
  | .div a b => do
      let IA ← ops.evalWithCallbacks callbacks env a
      let IB ← ops.evalWithCallbacks callbacks env b
      callbacks.div? a b IA IB
  | .neg a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      ops.neg? IA
  | .pow a k => do
      let IA ← ops.evalWithCallbacks callbacks env a
      ops.pow? IA k
  | .sin a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      ops.sin? IA
  | .cos a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      ops.cos? IA
  | .atan a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .atan a IA
  | .asin a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .asin a IA
  | .acos a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .acos a IA
  | .exp a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .exp a IA
  | .log a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .log a IA
  | .sqrt a => do
      let IA ← ops.evalWithCallbacks callbacks env a
      callbacks.unary? .sqrt a IA
  | .rpow a b => do
      let IA ← ops.evalWithCallbacks callbacks env a
      let IB ← ops.evalWithCallbacks callbacks env b
      callbacks.rpow? a b IA IB

end IntervalExprOps

namespace IntervalExprCallbacks

variable {I : Type u} {ι : Type*} [RealIntervalBackend I]
  {ops : IntervalExprOps I} {callbacks : IntervalExprCallbacks I ι}
  {env : ι → I} {ρ : ι → ℝ}

/-- Semantic contracts for expression-aware callbacks in one environment. -/
structure Sound : Prop where
  /-- Every symbolic variable is enclosed by its interval environment. -/
  vars : ∀ i, RealIntervalBackend.MemReal (env i) (ρ i)
  /-- Every successful division callback encloses the exact quotient. -/
  div :
    ∀ a b IA IB result,
      ops.evalWithCallbacks callbacks env a = some IA →
      ops.evalWithCallbacks callbacks env b = some IB →
      callbacks.div? a b IA IB = some result →
      RealIntervalBackend.MemReal IA (a.eval ρ) →
      RealIntervalBackend.MemReal IB (b.eval ρ) →
      RealIntervalBackend.MemReal result (a.eval ρ / b.eval ρ)
  /-- Every successful advanced unary callback encloses its exact real image. -/
  unary :
    ∀ op arg IA result,
      ops.evalWithCallbacks callbacks env arg = some IA →
      callbacks.unary? op arg IA = some result →
      RealIntervalBackend.MemReal IA (arg.eval ρ) →
      RealIntervalBackend.MemReal result (op.apply (arg.eval ρ))
  /-- Every successful real-power callback encloses the exact real power `a ^ b`. -/
  rpow :
    ∀ a b IA IB result,
      ops.evalWithCallbacks callbacks env a = some IA →
      ops.evalWithCallbacks callbacks env b = some IB →
      callbacks.rpow? a b IA IB = some result →
      RealIntervalBackend.MemReal IA (a.eval ρ) →
      RealIntervalBackend.MemReal IB (b.eval ρ) →
      RealIntervalBackend.MemReal result (a.eval ρ ^ b.eval ρ)

/-- The callback-extended traversal is sound whenever its primitives and callbacks are sound. -/
theorem evalWithCallbacks_sound
    (base : IntervalExprBackend ops)
    (extensions : Sound (ops := ops) (callbacks := callbacks) (env := env) (ρ := ρ)) :
    ∀ expr result,
      ops.evalWithCallbacks callbacks env expr = some result →
      RealIntervalBackend.MemReal result (expr.eval ρ) := by
  intro expr
  induction expr <;> intro result hresult <;>
    simp only [IntervalExprOps.evalWithCallbacks, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hresult
  case nat n => exact base.const_sound n result hresult
  case int z => exact base.const_sound z result hresult
  case rat num den =>
    split_ifs at hresult
    simpa using base.const_sound ((num : ℚ) / (den : ℚ)) result hresult
  case pi => exact base.pi_sound result hresult
  case e => exact base.e_sound result hresult
  case var i =>
    obtain rfl := Option.some.inj hresult
    exact extensions.vars i
  case add a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact base.add_sound IA IB result _ _ h (iha IA hA) (ihb IB hB)
  case mul a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact base.mul_sound IA IB result _ _ h (iha IA hA) (ihb IB hB)
  case sub a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact base.sub?_sound h (iha IA hA) (ihb IB hB)
  case div a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact extensions.div a b IA IB result hA hB h (iha IA hA) (ihb IB hB)
  case neg a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact base.neg_sound IA result _ h (iha IA hA)
  case pow a k iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact base.pow_sound IA k result _ h (iha IA hA)
  case sin a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact base.sin_sound IA result _ h (iha IA hA)
  case cos a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    exact base.cos_sound IA result _ h (iha IA hA)
  case atan a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .atan a IA result hA h (iha IA hA)
  case asin a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .asin a IA result hA h (iha IA hA)
  case acos a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .acos a IA result hA h (iha IA hA)
  case exp a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .exp a IA result hA h (iha IA hA)
  case log a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .log a IA result hA h (iha IA hA)
  case sqrt a iha =>
    obtain ⟨IA, hA, h⟩ := hresult
    simpa [UnaryKind.apply] using extensions.unary .sqrt a IA result hA h (iha IA hA)
  case rpow a b iha ihb =>
    obtain ⟨IA, hA, IB, hB, h⟩ := hresult
    exact extensions.rpow a b IA IB result hA hB h (iha IA hA) (ihb IB hB)

end IntervalExprCallbacks

end CAS.Continuum
