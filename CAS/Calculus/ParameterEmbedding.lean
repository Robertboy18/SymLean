/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Euclidean
/-!
# Parameter embeddings for checked derivatives of ordinary functions

The derivative tactics reflect an ordinary function of `n` real coordinates, whose body may also
mention binder-independent real parameters `c₀, …, c_{k-1}`, as a checked expression
`expr : Verified.Expr (Fin (n + k))`: the coordinates are its first `n` variables and the
parameters its last `k`. `paramEmbed c q` places the coordinates of `q : ℝ^n` in front of the
parameter values `c : Fin k → ℝ`, and `lineEmbed c s` does the same for one coordinate `s : ℝ`.
The theorems carry `HasFDerivAt` and `HasDerivAt` of evaluation along these affine embeddings and
read the derivative off the symbolic derivative `expr.diff`.

## Main definitions

* `paramEmbed`, `lineEmbed`: the two embeddings; `paramEmbedL` is the linear part of `paramEmbed`.
* `reduceFinAppend`: a `dsimproc` that evaluates `Fin.append u v i` at a numeric literal `i`.

## Main results

* `hasFDerivAt_eval_paramEmbed`, `hasDerivAt_eval_lineEmbed`: the derivative of evaluation along
  the embeddings at a valid point.
* `eventually_validAt_paramEmbed`, `eventually_validAt_lineEmbed`: validity persists near a valid
  point.
* `deriv_eval_lineEmbed_eventuallyEq`: near a valid point, the derivative function is the
  evaluated symbolic derivative.

## Implementation notes

We build `paramEmbed` from `Fin.append` because `Fin.append` reduces definitionally on literal
indices, so the reflected function `fun q ↦ expr.eval (paramEmbed c q)` is definitionally equal
to the user's function and no simplification is needed to identify the two. The line forms take
the derivative index as an explicit `i' : Fin (1 + k)` with the equation `(i' : ℕ) = 0`, so the
tactics can quote a literal index whose comparisons `dsimp` decides directly. `simp` normalizes
the quoted indices `Fin.castAdd k i` and `Fin.natAdd n j` to literals before the lemmas
`Fin.append_left` and `Fin.append_right` can fire; `reduceFinAppend` therefore evaluates
`Fin.append` at a literal by definitional unfolding, as `Matrix.cons_val` evaluates vector
literals.

`deriv_eval_lineEmbed_eventuallyEq` assumes validity at the point only, and
`eventually_validAt_lineEmbed` supplies the neighbourhood. `eliminateNestedNear`
(`CAS.Tactic.DerivativeBridge.NestedScalar`) relies on it to remove nested derivatives under
conditions at the point alone, such as `deriv (fun x ↦ deriv Real.sqrt x) x` under `0 < x`.
-/

@[expose] public section

namespace CAS

open scoped Topology
open scoped BigOperators

section FinAppendLiteral

open Lean Meta

/-- Evaluate `Fin.append u v i` for a numeric literal index `i`, selecting the entry of `u`
or of `v`. The result is definitionally equal to the input, so this is a `dsimproc`. -/
dsimproc reduceFinAppend (Fin.append _ _ _) := fun e ↦ do
  let_expr Fin.append m n _ u v i := e | return .continue
  let position? : Option Nat :=
    match i.nat? with
    | some position => some position
    | none =>
        match i with
        | .app (.app (.app (.const ``Fin.mk _) _) value) _ => value.nat? <|> value.rawNatLit?
        | _ => none
  let some position := position? | return .continue
  -- The lengths of vector literals elaborate to `Nat.succ` chains, which `Nat.fromExpr?` does
  -- not evaluate; `evalNat` does.
  let some m ← (Meta.evalNat m).run | return .continue
  let some n ← (Meta.evalNat n).run | return .continue
  if position < m then
    let index ← mkAppOptM ``OfNat.ofNat
      #[some (mkApp (mkConst ``Fin) (toExpr m)), some (mkRawNatLit position), none]
    return .visit (mkApp u index)
  else if position < m + n then
    let index ← mkAppOptM ``OfNat.ofNat
      #[some (mkApp (mkConst ``Fin) (toExpr n)), some (mkRawNatLit (position - m)), none]
    return .visit (mkApp v index)
  else
    return .continue

end FinAppendLiteral

namespace Verified.Expr

variable {n k : ℕ}

/-- Embed `ℝ^n` into `ℝ^(n + k)`, filling the last `k` coordinates with the
parameter values `c`. -/
noncomputable def paramEmbed (c : Fin k → ℝ) (q : ℝ^n) : ℝ^(n + k) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp q) c)

/-- The coordinates of an embedded point are the appended coordinate vectors. -/
@[simp] theorem ofLp_paramEmbed (c : Fin k → ℝ) (q : ℝ^n) :
    WithLp.ofLp (paramEmbed c q) = Fin.append (WithLp.ofLp q) c :=
  rfl

/-- The linear part of the parameter embedding. -/
noncomputable def paramEmbedLinear (n k : ℕ) : ℝ^n →ₗ[ℝ] ℝ^(n + k) where
  toFun q := paramEmbed (fun _ ↦ 0) q
  map_add' q r := by
    apply PiLp.ext
    intro j
    cases j using Fin.addCases <;> simp [paramEmbed]
  map_smul' a q := by
    apply PiLp.ext
    intro j
    cases j using Fin.addCases <;> simp [paramEmbed]

/-- The linear part of the parameter embedding as a continuous linear map. -/
noncomputable def paramEmbedL (n k : ℕ) : ℝ^n →L[ℝ] ℝ^(n + k) :=
  LinearMap.toContinuousLinearMap (paramEmbedLinear n k)

/-- The continuous linear part of the embedding is the embedding with zero parameters. -/
theorem paramEmbedL_apply (q : ℝ^n) :
    paramEmbedL n k q = paramEmbed (fun _ ↦ 0) q :=
  rfl

/-- The parameter embedding is affine: its linear part plus the embedded origin. -/
theorem paramEmbed_eq_linear_add (c : Fin k → ℝ) (q : ℝ^n) :
    paramEmbed c q = paramEmbedL n k q + paramEmbed c 0 := by
  ext j
  cases j using Fin.addCases <;> simp [paramEmbed, paramEmbedL_apply]

/-- The parameter embedding has its linear part as Fréchet derivative everywhere. -/
theorem hasFDerivAt_paramEmbed (c : Fin k → ℝ) (p : ℝ^n) :
    HasFDerivAt (paramEmbed c) (paramEmbedL n k) p := by
  rw [funext (paramEmbed_eq_linear_add c)]
  exact (paramEmbedL n k).hasFDerivAt.add_const _

/-- The linear part of the embedding sends coordinate basis vectors to coordinate basis
vectors. -/
theorem paramEmbedL_single (i : Fin n) :
    paramEmbedL n k (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (Fin.castAdd k i) (1 : ℝ) := by
  ext j
  cases j using Fin.addCases with
  | left j =>
    simp [paramEmbedL_apply, paramEmbed, PiLp.single_apply, Pi.single_apply, Fin.castAdd_inj]
  | right j =>
    have hlt : Fin.castAdd k i < Fin.natAdd n j :=
      (Fin.castAdd_lt k i).trans_le (Nat.le_add_right _ _)
    simp [paramEmbedL_apply, paramEmbed, hlt.ne']

/-- Evaluation of a checked expression along the parameter embedding is differentiable,
with derivative the formal derivative composed with the linear part of the embedding. -/
theorem hasFDerivAt_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    HasFDerivAt (fun q : ℝ^n ↦ expr.eval (paramEmbed c q))
      ((symbolicFDeriv expr (paramEmbed c p)).comp (paramEmbedL n k)) p :=
  (hasFDerivAt_eval expr (paramEmbed c p) h).comp p (hasFDerivAt_paramEmbed c p)

/-- Validity of an embedded checked expression persists near a valid point. -/
theorem eventually_validAt_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    ∀ᶠ q : ℝ^n in 𝓝 p, expr.ValidAt (paramEmbed c q) :=
  (hasFDerivAt_paramEmbed c p).continuousAt.tendsto.eventually
    (eventually_validAt expr (paramEmbed c p) h)

/-- The affine coordinate line `s ↦ (s, c)` in `ℝ^(1 + k)`. -/
noncomputable def lineEmbed (c : Fin k → ℝ) (s : ℝ) : ℝ^(1 + k) :=
  paramEmbed c (WithLp.toLp 2 ![s])

/-- The coordinates of `lineEmbed c s` are the line coordinate `s` followed by the
parameters `c`. -/
@[simp] theorem ofLp_lineEmbed (c : Fin k → ℝ) (s : ℝ) :
    WithLp.ofLp (lineEmbed c s) = Fin.append ![s] c :=
  rfl

/-- The one-dimensional coordinate map `s ↦ (s)` has derivative the unit vector. -/
theorem hasDerivAt_toLp_vecCons (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (WithLp.toLp 2 ![s] : ℝ^1))
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) t := by
  have hfun : (fun s : ℝ ↦ (WithLp.toLp 2 ![s] : ℝ^1)) =
      fun s ↦ s • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    ext s j
    fin_cases j
    simp
  rw [hfun]
  simpa using (hasDerivAt_id t).smul_const (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

/-- The scalar derivative of a checked expression along the affine coordinate line is the
evaluated symbolic derivative with respect to the line coordinate. -/
theorem hasDerivAt_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (i' : Fin (1 + k)) (hi : (i' : ℕ) = 0)
    (h : expr.ValidAt (lineEmbed c t)) :
    HasDerivAt (fun s : ℝ ↦ expr.eval (lineEmbed c s))
      ((expr.diff i').eval (lineEmbed c t)) t := by
  obtain rfl : i' = Fin.castAdd k (0 : Fin 1) := Fin.ext (by simpa using hi)
  have hcomp := (hasFDerivAt_eval_paramEmbed expr c (WithLp.toLp 2 ![t]) h).comp_hasDerivAt t
    (hasDerivAt_toLp_vecCons t)
  rwa [ContinuousLinearMap.comp_apply, paramEmbedL_single,
    symbolicFDeriv_apply_single_eq_diff_eval expr (paramEmbed c (WithLp.toLp 2 ![t]))
      (Fin.castAdd k (0 : Fin 1))] at hcomp

/-- Validity of a checked expression along the affine coordinate line persists near a valid
point. -/
theorem eventually_validAt_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (h : expr.ValidAt (lineEmbed c t)) :
    ∀ᶠ s in 𝓝 t, expr.ValidAt (lineEmbed c s) :=
  (hasDerivAt_toLp_vecCons t).continuousAt.tendsto.eventually
    (eventually_validAt_paramEmbed expr c _ h)

/-- Near a valid point, the derivative of evaluation along the affine coordinate line is the
evaluated symbolic derivative. Only validity at the point itself is assumed: the neighbourhood
on which the identity holds comes from `eventually_validAt_lineEmbed`. -/
theorem deriv_eval_lineEmbed_eventuallyEq (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (i' : Fin (1 + k)) (hi : (i' : ℕ) = 0)
    (h : expr.ValidAt (lineEmbed c t)) :
    deriv (fun s : ℝ ↦ expr.eval (lineEmbed c s)) =ᶠ[𝓝 t]
      fun s ↦ (expr.diff i').eval (lineEmbed c s) := by
  filter_upwards [eventually_validAt_lineEmbed expr c t h] with s hs
  exact (hasDerivAt_eval_lineEmbed expr c s i' hi hs).deriv

end Verified.Expr

end CAS
