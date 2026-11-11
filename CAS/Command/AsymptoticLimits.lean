/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Limits
public import CAS.Command.Systems
public import CAS.Command.Integration
public import CAS.Command.Series
public import CAS.Calculus.ConditionFree
public meta import CAS.Calculus.ConditionFree
public import CAS.Calculus.AsymptoticExpansion
public meta import CAS.Calculus.AsymptoticExpansion
public import CAS.Command.Sum
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Limits at infinity by asymptotic comparison

`#cas [limit x → ∞] f` and `#cas [limit x → -∞] f` for expressions built from `x`, rational
constants, `π`, `e`, `+`, `-`, `*`, `/`, natural powers, `exp` of an affine function or of a
function tending to `0`, `log`, `sqrt` and `arctan`. The theorem is `Tendsto f atTop (𝓝 L)`,
`Tendsto f atTop atTop` or `Tendsto f atTop atBot` (at `-∞` with `atBot`). Oscillating
functions are not treated. Rational functions and other expressions without `exp`, `log`, `sqrt`,
`arctan`, `π` or `e` stay with the substitution `x = 1 / t` of `CAS/Command/Limits.lean`, which
also runs when the comparison fails; when both fail, the error gives the reason of each. Bare
`cas` proves `Tendsto` goals at `atTop` and `atBot` with the same theorem (`asymptoticTheorem`).

## Implementation notes

Every subexpression gets an asymptotic equivalent `c xᵃ eᵇˣ (log x)ᵏ` with `c = q C`, `q`
rational and `C` a positive constant such as `π`, `e ^ d` or `√r` (`CAS.Asymptotic.Asym`).
`analyze` finds the equivalent and builds its proof in the same recursion over the expression,
with the rules of `CAS/Calculus/AsymptoticScale.lean` and `CAS/Calculus/AsymptoticExpansion.lean`.
Sums keep their dominant term in the lexicographic order of `(b, a, k)` (`compareTriple`), so
`(x ^ 2 + e ^ x) / (e ^ x + 1)` is equivalent to `1` and `x ^ 2 e ^ (-x)` to itself, whose limit
is `0`. When the dominant terms of a sum cancel, the next term comes from the conjugate of a
square root (`sqrt (x ^ 2 + 1) - x = 1 / (sqrt (x ^ 2 + 1) + x)`), from
`log P - log Q = log (P / Q)`, from `P / Q - 1 = (P - Q) / Q`, from `e ^ u - 1 ~ u` and
`log P ~ P - 1` for `u → 0`, `P → 1`, or from expanding a polynomial
(`CAS.Asymptotic.sqrt_sub_eq`, `asym_exp_sub_one`, `asym_log_of_sub_one`). The side conditions
of the rules, such as the sign of a difference of exponents (`NegTriple`) or a positive
constant, are proved by tactics such as `norm_num` and `positivity`, and the kernel checks the
finished proof (`CAS.Tactic.Explanation.kernelCheckedProof`). At `-∞` we prove the limit of
`f (-t)` at `∞` and transport it with Mathlib's `Filter.tendsto_comp_neg_atTop_iff`.

The scale is fixed, with rules we proved for it. It is not Gruntz's algorithm, which compares the
growth classes of nested exponentials: here the exponent of `e` must be affine in `x` or tend to
`0`, so `exp (x ^ 2)` and `exp (exp x)` are refused.
-/

public meta section

namespace CAS.Command.AsymptoticLimits

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Verified.Expr
open CAS.Asymptotic

/-- An asymptotic equivalent `f ~ q C scale a b k` and its proof `Asym f (q C) a b k`. -/
structure Info where
  /-- A proof of `Asym f (q C) a b k`. -/
  proof : Lean.Expr
  /-- The rational factor `q` of the constant `q C`. -/
  q : ℚ
  /-- The positive real factor `C`, an expression such as `π`, `e ^ d` or `√r`. -/
  C : Lean.Expr
  /-- The power `a` of `x`. -/
  a : ℚ
  /-- The rate `b` of `e ^ (b x)`. -/
  b : ℚ
  /-- The power `k` of `log x`. -/
  k : ℚ

/-- A rational as a real number. -/
def realOf (q : ℚ) : TermElabM Lean.Expr := do
  let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let magnitude ← if q.den = 1 then pure numerator else
    let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
    `($numerator / $denominator)
  let stx ← if q.num < 0 then `((-$magnitude : ℝ)) else `(($magnitude : ℝ))
  let e ← elabTerm stx (some (mkConst ``Real))
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Prove a proposition by a tactic. -/
def byTactic (type : Lean.Expr) (tactic : TSyntax `tactic) : TermElabM Lean.Expr := do
  let value ← withoutErrToSorry <| elabTermEnsuringType (← `(by $tactic:tactic)) type
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasSorry then throwError "limit: a side condition failed: {type}"
  return value

/-- `NegTriple a b k` by `norm_num`, for real expressions in the form the rule expects. -/
def negTripleOf (a b k : Lean.Expr) : TermElabM Lean.Expr := do
  let type ← mkAppM ``NegTriple #[a, b, k]
  byTactic type (← `(tactic| (unfold CAS.Asymptotic.NegTriple; norm_num)))

/-- `NegTriple a b k` for rationals. -/
def negTriple (a b k : ℚ) : TermElabM Lean.Expr := do
  negTripleOf (← realOf a) (← realOf b) (← realOf k)

/-- `NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)`. -/
def negDifference (a₂ b₂ k₂ a₁ b₁ k₁ : ℚ) : TermElabM Lean.Expr := do
  let d (u v : ℚ) : TermElabM Lean.Expr := do mkAppM ``HSub.hSub #[← realOf u, ← realOf v]
  negTripleOf (← d a₂ a₁) (← d b₂ b₁) (← d k₂ k₁)

/-- `NegTriple (-a) (-b) (-k)`. -/
def negOpposite (a b k : ℚ) : TermElabM Lean.Expr := do
  let n (u : ℚ) : TermElabM Lean.Expr := do mkAppM ``Neg.neg #[← realOf u]
  negTripleOf (← n a) (← n b) (← n k)

/-- The lexicographic comparison of `(b, a, k)`. -/
def compareTriple (x y : Info) : Ordering :=
  if x.b != y.b then compare x.b y.b
  else if x.a != y.a then compare x.a y.a
  else compare x.k y.k

/-- The constant `q C`. -/
def constantOf (q : ℚ) (C : Lean.Expr) : TermElabM Lean.Expr := do
  mkAppM ``HMul.hMul #[← realOf q, C]

/-- Restate `Asym f c a b k` as `Asym f (q C) a' b' k'` with the exponents as rationals,
the equalities by `ring` and `norm_num`. -/
def normalize (_ proof : Lean.Expr) (q : ℚ) (C : Lean.Expr) (a b k : ℚ) : TermElabM Info := do
  -- The function stays as the rule produced it; it is matched with the expression at the end.
  let f := (← instantiateMVars (← inferType proof)).getAppArgs[0]!
  let target ← mkAppM ``Asym #[f, ← constantOf q C, ← realOf a, ← realOf b, ← realOf k]
  let proofT ← exprToSyntax proof
  let value ← withoutErrToSorry <| elabTermEnsuringType (← `(by
    have h := $proofT
    convert h using 1 <;> first | ring | norm_num | (push_cast; ring))) target
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasSorry then throwError "limit: normalization failed"
  return { proof := value, q, C, a, b, k }

/-- `c ≠ 0` for `c = q C`. -/
def nonzero (q : ℚ) (C : Lean.Expr) : TermElabM Lean.Expr := do
  let type ← mkAppM ``Ne #[← constantOf q C, ← realOf 0]
  byTactic type (← `(tactic| exact mul_ne_zero (by norm_num) (ne_of_gt (by positivity))))

/-- The asymptotic equivalent of an expression at `+∞`. -/
partial def analyze (expr : Verified.Expr (Fin 1)) : TermElabM Info := do
  let quoted ← quoteVerifiedExpr expr
  let f ← elabTerm (← `(fun x : ℝ ↦ Verified.Expr.univariateEval
    $(← exprToSyntax quoted) x)) none
  let f ← instantiateMVars f
  let sub (part : Verified.Expr (Fin 1)) : TermElabM (Lean.Expr × Info) := do
    let info ← analyze part
    let quoted ← quoteVerifiedExpr part
    let g ← elabTerm (← `(fun x : ℝ ↦ Verified.Expr.univariateEval
      $(← exprToSyntax quoted) x)) none
    return (← instantiateMVars g, info)
  let one ← realOf 1
  match expr with
  | .var _ =>
      normalize f (mkConst ``asym_id) 1 one 1 0 0
  | .nat n => constant n
  | .int n => constant n
  | .rat p d => if d = 0 then throwError "limit: zero denominator" else constant ((p : ℚ) / d)
  | .pi => do
      let pi ← elabTerm (← `(Real.pi)) none
      normalize f (← mkAppM ``asym_const #[pi]) 1 pi 0 0 0
  | .e => do
      let e1 ← elabTerm (← `(Real.exp 1)) none
      normalize f (← mkAppM ``asym_const #[e1]) 1 e1 0 0 0
  | .neg a => do
      let (_, x) ← sub a
      normalize f (← mkAppM ``asym_neg #[x.proof]) (-x.q) x.C x.a x.b x.k
  | .mul a b => do
      let (_, x) ← sub a
      let (_, y) ← sub b
      normalize f (← mkAppM ``asym_mul #[x.proof, y.proof]) (x.q * y.q)
        (← mkAppM ``HMul.hMul #[x.C, y.C]) (x.a + y.a) (x.b + y.b) (x.k + y.k)
  | .div a b => do
      let (_, x) ← sub a
      let (_, y) ← sub b
      normalize f (← mkAppM ``asym_div #[x.proof, y.proof]) (x.q / y.q)
        (← mkAppM ``HDiv.hDiv #[x.C, y.C]) (x.a - y.a) (x.b - y.b) (x.k - y.k)
  | .pow a n => do
      let (_, x) ← sub a
      normalize f (← mkAppM ``asym_pow #[x.proof, toExpr n]) (x.q ^ n)
        (← mkAppM ``HPow.hPow #[x.C, toExpr n]) (n * x.a) (n * x.b) (n * x.k)
  | .add a b => sum f a b false
  | .sub a b => sum f a b true
  | .exp arg => do
      let some (bq, dq) := (Systems.affineCoefficients arg).map fun (c, d) ↦ (c[0]!, d)
        | -- An argument tending to `0`: `e ^ u ~ 1`.
          let (_, x) ← sub arg
          let h ← try negTriple x.a x.b x.k catch _ =>
            throwError "limit: the argument of exp is neither affine nor tending to 0"
          let hu ← mkAppM ``tendsto_of_asym_zero #[x.proof, h]
          normalize f (← mkAppM ``asym_exp_of_tendsto_zero #[hu]) 1 one 0 0 0
      let (g, _) ← (do
          let quotedArg ← quoteVerifiedExpr arg
          let g ← elabTerm (← `(fun x : ℝ ↦ Verified.Expr.univariateEval
            $(← exprToSyntax quotedArg) x)) none
          return (← instantiateMVars g, ()))
      let bR ← realOf bq
      let dR ← realOf dq
      let hgType ← elabType (← `(∀ x : ℝ, $(← exprToSyntax g) x =
        $(← exprToSyntax bR) * x + $(← exprToSyntax dR)))
      let hg ← byTactic hgType (← `(tactic| (intro x; simp only [Verified.Expr.univariateEval,
        Verified.Expr.euclideanSingle_eq_const, Verified.Expr.eval, Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_neg, Nat.cast_one,
        Nat.cast_zero, Int.cast_one, Int.cast_zero]; try ring)))
      let expd ← mkAppM ``Real.exp #[dR]
      normalize f (← mkAppM ``asym_exp_affine #[hg]) 1 expd 0 bq 0
  | .log arg => do
      let (_, x) ← sub arg
      let isOne ← if x.a = 0 && x.b = 0 && x.k = 0 && x.q = 1 then
          try
            let _ ← byTactic (← mkAppM ``Eq #[x.C, one]) (← `(tactic| norm_num))
            pure true
          catch _ => pure false
        else pure false
      if isOne then
        -- `log P ~ P - 1` for `P → 1`.
        let shifted : Verified.Expr (Fin 1) := .sub arg (.nat 1)
        let (_, y) ← sub shifted
        let h ← try negTriple y.a y.b y.k catch _ =>
          throwError "limit: log of an argument tending to 1 too slowly"
        let argT ← exprToSyntax (← quoteVerifiedExpr arg)
        let shiftedT ← exprToSyntax (← quoteVerifiedExpr shifted)
        let heqType ← elabType (← `(∀ᶠ x in Filter.atTop, Verified.Expr.univariateEval $argT x - 1 =
          Verified.Expr.univariateEval $shiftedT x))
        let heq ← byTactic heqType (← `(tactic| (
          refine Filter.Eventually.of_forall fun x ↦ ?_
          simp only [Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const,
            Verified.Expr.eval, Nat.cast_one])))
        let hshift ← mkAppM ``asym_congr #[heq, y.proof]
        return ← normalize f (← mkAppM ``asym_log_of_sub_one #[hshift, h]) y.q y.C y.a y.b y.k
      unless 0 < x.q && x.b = 0 && x.k = 0 && x.a ≠ 0 do
        throwError "limit: log of an argument that is not equivalent to a positive power"
      let hc ← byTactic (← mkAppM ``LT.lt #[← realOf 0, ← constantOf x.q x.C])
        (← `(tactic| positivity))
      let ha ← byTactic (← mkAppM ``Ne #[← realOf x.a, ← realOf 0]) (← `(tactic| norm_num))
      normalize f (← mkAppM ``asym_log_rpow #[x.proof, hc, ha]) x.a one 0 0 1
  | .sqrt arg => do
      let (_, x) ← sub arg
      unless 0 < x.q do throwError "limit: square root of a negative equivalent"
      -- A rational square under the root, with constant `1`, keeps a rational constant.
      let square? : Option ℚ :=
        let (n, d) := (x.q.num.toNat, x.q.den)
        let (rn, rd) := (Nat.sqrt n, Nat.sqrt d)
        if rn * rn = n && rd * rd = d then some ((rn : ℚ) / rd) else none
      if let some r := square? then
        let CT ← exprToSyntax x.C
        let heqType ← mkAppM ``Eq #[← mkAppM ``Real.sqrt #[← constantOf x.q x.C],
          ← constantOf r one]
        let heq? ← try some <$> byTactic heqType (← `(tactic| (
            rw [show $CT = (1 : ℝ) by norm_num]
            exact CAS.Asymptotic.sqrt_mul_one_eq (by norm_num) (by norm_num))))
          catch _ => pure none
        if let some heq := heq? then
          let rule ← mkAppM ``asym_sqrt #[x.proof]
          let ruleType ← instantiateMVars (← inferType rule)
          let args := ruleType.getAppArgs
          let motive ← withLocalDeclD `c (mkConst ``Real) fun c ↦
            mkLambdaFVars #[c] (mkAppN ruleType.getAppFn
              #[args[0]!, c, args[2]!, args[3]!, args[4]!])
          let rule ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, heq], rule]
          return ← normalize f rule r one (x.a / 2) (x.b / 2) (x.k / 2)
      let root ← mkAppM ``Real.sqrt #[← constantOf x.q x.C]
      normalize f (← mkAppM ``asym_sqrt #[x.proof]) 1 root (x.a / 2) (x.b / 2) (x.k / 2)
  | .atan arg => do
      let (_, x) ← sub arg
      let positive := x.b > 0 || (x.b = 0 && (x.a > 0 || (x.a = 0 && x.k > 0)))
      unless positive do throwError "limit: arctan of an argument with a finite limit"
      let h ← negOpposite x.a x.b x.k
      let halfPi ← elabTerm (← `(Real.pi / 2)) none
      if 0 < x.q then
        let hc ← byTactic (← mkAppM ``LT.lt #[← realOf 0, ← constantOf x.q x.C])
          (← `(tactic| positivity))
        normalize f (← mkAppM ``asym_arctan_atTop #[x.proof, hc, h]) 1 halfPi 0 0 0
      else
        let hc ← byTactic (← mkAppM ``LT.lt #[← constantOf x.q x.C, ← realOf 0])
          (← `(tactic| exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)))
        normalize f (← mkAppM ``asym_arctan_atBot #[x.proof, hc, h]) (-1) halfPi 0 0 0
  | _ => throwError "limit: unsupported function at infinity"
where
  /-- A nonzero constant. -/
  constant (c : ℚ) : TermElabM Info := do
    if c = 0 then throwError "limit: a zero term"
    let cR ← realOf c
    -- The function is the evaluation of the literal, whose value is `c` after the casts.
    let quoted ← quoteVerifiedExpr expr
    let hType ← elabType (← `(∀ x : ℝ, Verified.Expr.univariateEval
      $(← exprToSyntax quoted) x = $(← exprToSyntax cR)))
    let tac ← `(tactic| (
      intro x
      simp only [Verified.Expr.univariateEval, Verified.Expr.eval, Nat.cast_ofNat, Int.cast_ofNat,
        Int.cast_neg, Nat.cast_one, Int.cast_one]
      try norm_num))
    let h ← byTactic hType tac
    normalize cR (← mkAppM ``asym_of_eq_const #[h]) c (← realOf 1) 0 0 0
  /-- A sum or difference: the dominant term, or equal exponents with their constants. -/
  sum (f : Lean.Expr) (a b : Verified.Expr (Fin 1)) (minus : Bool) : TermElabM Info := do
    let x ← analyze a
    let y ← analyze b
    match compareTriple x y with
    | .gt =>
        let hc ← nonzero x.q x.C
        let h ← negDifference y.a y.b y.k x.a x.b x.k
        let rule := if minus then ``asym_sub_left else ``asym_add_left
        normalize f (← mkAppM rule #[x.proof, y.proof, hc, h]) x.q x.C x.a x.b x.k
    | .lt =>
        let hc ← nonzero y.q y.C
        let h ← negDifference x.a x.b x.k y.a y.b y.k
        let rule := if minus then ``asym_sub_right else ``asym_add_right
        normalize f (← mkAppM rule #[x.proof, y.proof, hc, h]) (if minus then -y.q else y.q)
          y.C y.a y.b y.k
    | .eq =>
        unless ← isDefEq x.C y.C do
          -- Constants equal in value: the dominant terms may still cancel.
          let same ← try
              let _ ← byTactic (← mkAppM ``Eq #[x.C, y.C]) (← `(tactic| norm_num))
              pure true
            catch _ => pure false
          if same && (if minus then x.q - y.q else x.q + y.q) = 0 then
            return ← cancel f a b minus x y
          throwError "limit: equal exponents with different constants"
        let total := if minus then x.q - y.q else x.q + y.q
        if total = 0 then return ← cancel f a b minus x y
        let cx ← constantOf x.q x.C
        let cy ← constantOf y.q y.C
        let combined ← if minus then mkAppM ``HSub.hSub #[cx, cy] else mkAppM ``HAdd.hAdd #[cx, cy]
        let hcType ← mkAppM ``Ne #[combined, ← realOf 0]
        let totalT ← exprToSyntax (← realOf total)
        let CT ← exprToSyntax x.C
        let hc ← byTactic hcType (← `(tactic| (
          rw [show $(← exprToSyntax combined) = $totalT * $CT by ring]
          exact mul_ne_zero (by norm_num) (ne_of_gt (by positivity)))))
        let rule := if minus then ``asym_sub_same else ``asym_add_same
        normalize f (← mkAppM rule #[x.proof, y.proof, hc]) total x.C x.a x.b x.k
  /-- `0 < f x` eventually, from a positive equivalent. -/
  eventuallyPos (part : Verified.Expr (Fin 1)) (info : Info) : TermElabM Lean.Expr := do
    let hc ← byTactic (← mkAppM ``LT.lt #[← realOf 0, ← constantOf info.q info.C])
      (← `(tactic| positivity))
    let partT ← exprToSyntax (← quoteVerifiedExpr part)
    let type ← elabType (← `(∀ᶠ x in Filter.atTop, 0 < Verified.Expr.univariateEval $partT x))
    let proofT ← exprToSyntax (← mkAppM ``asym_eventually_pos #[info.proof, hc])
    byTactic type (← `(tactic| exact $proofT))
  /-- `f x < 0` eventually, from a negative equivalent. -/
  eventuallyNeg (part : Verified.Expr (Fin 1)) (info : Info) : TermElabM Lean.Expr := do
    let hc ← byTactic (← mkAppM ``LT.lt #[← realOf 0, ← mkAppM ``Neg.neg
        #[← constantOf info.q info.C]])
      (← `(tactic| (have : (0 : ℝ) < $(← exprToSyntax info.C) := by positivity
                    nlinarith)))
    let partT ← exprToSyntax (← quoteVerifiedExpr part)
    let type ← elabType (← `(∀ᶠ x in Filter.atTop, Verified.Expr.univariateEval $partT x < 0))
    let negated ← mkAppM ``asym_neg #[info.proof]
    let proofT ← exprToSyntax (← mkAppM ``asym_eventually_pos #[negated, hc])
    byTactic type (← `(tactic| exact ($proofT).mono fun _ h ↦ neg_pos.mp h))
  /-- The equivalent of `f` from that of `g`, with `f = g` eventually. -/
  through (f : Lean.Expr) (fE g : Verified.Expr (Fin 1)) (proofTac : TSyntax `tactic) :
      TermElabM Info := do
    let y ← analyze g
    let fT ← exprToSyntax (← quoteVerifiedExpr fE)
    let gT ← exprToSyntax (← quoteVerifiedExpr g)
    let heqType ← elabType (← `(∀ᶠ x in Filter.atTop, Verified.Expr.univariateEval $fT x =
      Verified.Expr.univariateEval $gT x))
    let heq ← byTactic heqType proofTac
    normalize f (← mkAppM ``asym_congr #[heq, y.proof]) y.q y.C y.a y.b y.k
  /-- Dominant terms that cancel: the conjugate of a square root, `e ^ u - 1`, or the
  expanded polynomial. -/
  cancel (f : Lean.Expr) (a b : Verified.Expr (Fin 1)) (minus : Bool) (_x y : Info) :
      TermElabM Info := do
    let original : Verified.Expr (Fin 1) := if minus then .sub a b else .add a b
    let unfoldSimp ← `(tactic| simp only [Verified.Expr.univariateEval,
      Verified.Expr.euclideanSingle_eq_const, Verified.Expr.eval, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_neg, Nat.cast_one,
      Nat.cast_zero, Int.cast_one, Int.cast_zero] at *)
    -- `e ^ u - 1 ~ u` for `u → 0`.
    if minus then
      if let .exp u := a then
        if let .nat 1 := b then
          let xu ← analyze u
          let h ← negTriple xu.a xu.b xu.k
          let uT ← exprToSyntax (← quoteVerifiedExpr u)
          let oT ← exprToSyntax (← quoteVerifiedExpr original)
          let heqType ← elabType (← `(∀ᶠ x in Filter.atTop,
            Verified.Expr.univariateEval $oT x =
              Real.exp (Verified.Expr.univariateEval $uT x) - 1))
          let heq ← byTactic heqType (← `(tactic| (
            refine Filter.Eventually.of_forall fun x ↦ ?_
            simp only [Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const,
              Verified.Expr.eval, Nat.cast_one])))
          let rule ← mkAppM ``asym_exp_sub_one #[xu.proof, h]
          return ← normalize f (← mkAppM ``asym_congr #[heq, rule]) xu.q xu.C xu.a xu.b xu.k
    -- Square roots: multiply by the conjugate.
    let conj (rule : Name) (g : Verified.Expr (Fin 1)) (hP hQ : Lean.Expr) :
        TermElabM Info := do
      let hPT ← exprToSyntax hP
      let hQT ← exprToSyntax hQ
      let lemmaT := mkIdent rule
      through f original g (← `(tactic| (
        filter_upwards [$hPT:term, $hQT:term] with x hp hq
        $unfoldSimp:tactic
        exact $lemmaT:ident hp.le hq)))
    match minus, a, b with
    | true, .sqrt P, .sqrt Q =>
        let xP ← analyze P
        let xQ ← analyze Q
        return ← conj ``sqrt_sub_sqrt_eq (.div (.sub P Q) (.add (.sqrt P) (.sqrt Q)))
          (← eventuallyPos P xP) (← eventuallyPos Q xQ)
    | true, .sqrt P, Q =>
        let xP ← analyze P
        return ← conj ``sqrt_sub_eq (.div (.sub P (.pow Q 2)) (.add (.sqrt P) Q))
          (← eventuallyPos P xP) (← eventuallyPos Q y)
    | true, Q, .sqrt P =>
        let xP ← analyze P
        return ← conj ``sub_sqrt_eq (.div (.sub (.pow Q 2) P) (.add Q (.sqrt P)))
          (← eventuallyPos P xP) (← eventuallyPos Q _x)
    | false, .sqrt P, Q =>
        let xP ← analyze P
        let hPT ← exprToSyntax (← eventuallyPos P xP)
        let hQT ← exprToSyntax (← eventuallyNeg Q y)
        return ← through f original (.div (.sub P (.pow Q 2)) (.sub (.sqrt P) Q)) (← `(tactic| (
          filter_upwards [$hPT:term, $hQT:term] with x hp hq
          $unfoldSimp:tactic
          exact sqrt_add_eq hp.le hq)))
    | false, Q, .sqrt P =>
        let xP ← analyze P
        let hPT ← exprToSyntax (← eventuallyPos P xP)
        let hQT ← exprToSyntax (← eventuallyNeg Q _x)
        return ← through f original (.div (.sub P (.pow Q 2)) (.sub (.sqrt P) Q)) (← `(tactic| (
          filter_upwards [$hPT:term, $hQT:term] with x hp hq
          $unfoldSimp:tactic
          exact add_sqrt_eq hp.le hq)))
    | true, .log P, .log Q =>
        -- `log P - log Q = log (P / Q)`.
        let hPT ← exprToSyntax (← eventuallyPos P (← analyze P))
        let hQT ← exprToSyntax (← eventuallyPos Q (← analyze Q))
        return ← through f original (.log (.div P Q)) (← `(tactic| (
          filter_upwards [$hPT:term, $hQT:term] with x hp hq
          $unfoldSimp:tactic
          rw [Real.log_div hp.ne' hq.ne'])))
    | true, .div P Q, .nat 1 =>
        -- `P / Q - 1 = (P - Q) / Q`.
        let xQ ← analyze Q
        let hQT ← exprToSyntax (← if 0 < xQ.q then eventuallyPos Q xQ
          else do
            let h ← eventuallyNeg Q xQ
            pure h)
        let hne ← if 0 < xQ.q then `(tactic| exact (div_sub_one hq.ne').symm ▸ rfl)
          else `(tactic| exact (div_sub_one hq.ne).symm ▸ rfl)
        return ← through f original (.div (.sub P Q) Q) (← `(tactic| (
          filter_upwards [$hQT:term] with x hq
          $unfoldSimp:tactic
          first
            | exact div_sub_one hq.ne'
            | exact div_sub_one hq.ne
            | $hne:tactic)))
    | _, _, _ => pure ()
    -- Polynomials: expand.
    if let some g := Sum.toGeoPoly original then
      if g.all (·.1 == 1) then
        let coefficients := g.foldl (fun total (_, P) ↦
          (Array.range (max total.size P.size)).map fun j ↦ total.getD j 0 + P.getD j 0) #[]
        if coefficients.all (· == 0) then throwError "limit: the expression vanishes identically"
        let expanded := Sum.polyExpr coefficients
        return ← through f original expanded (← `(tactic| (
          refine Filter.Eventually.of_forall fun x ↦ ?_
          $unfoldSimp:tactic
          ring)))
    throwError "limit: the dominant terms cancel"

/-- Whether the expression has `exp`, `log`, `sqrt`, `arctan`, `π` or `e`. -/
partial def transcendental : Verified.Expr (Fin 1) → Bool
  | .exp _ | .log _ | .sqrt _ | .atan _ | .pi | .e => true
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => transcendental a || transcendental b
  | .neg a | .pow a _ | .sin a | .cos a | .asin a | .acos a => transcendental a
  | _ => false

/-- The limit of `expr` at `+∞` (`positive`) or `-∞` from its asymptotic equivalent: a theorem
`Tendsto (fun x ↦ univariateEval expr x) atTop l` (`atBot` at `-∞`), the limit `l` and the
equivalent. -/
def asymptoticTheorem (expr : Verified.Expr (Fin 1)) (positive : Bool) :
    TermElabM (Lean.Expr × Limits.LimitValue × Info) := do
  let target : Verified.Expr (Fin 1) :=
    if positive then expr else expr.mapVars fun _ ↦ .neg (.var 0)
  let info ← analyze target
  let cR ← constantOf info.q info.C
  let zeroTriple := info.a = 0 && info.b = 0 && info.k = 0
  let negative := info.b < 0 || (info.b = 0 && (info.a < 0 || (info.a = 0 && info.k < 0)))
  let (limit, value) : Lean.Expr × Limits.LimitValue ← if zeroTriple then do
      pure (← mkAppM ``tendsto_of_asym_const #[info.proof], .real cR)
    else if negative then do
      let h ← negTriple info.a info.b info.k
      pure (← mkAppM ``tendsto_of_asym_zero #[info.proof, h], .finite 0)
    else do
      let h ← negOpposite info.a info.b info.k
      if 0 < info.q then
        let hc ← byTactic (← mkAppM ``LT.lt #[← realOf 0, cR]) (← `(tactic| positivity))
        pure (← mkAppM ``tendsto_of_asym_atTop #[info.proof, hc, h], .top)
      else
        let hc ← byTactic (← mkAppM ``LT.lt #[cR, ← realOf 0])
          (← `(tactic| exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)))
        pure (← mkAppM ``tendsto_of_asym_atBot #[info.proof, hc, h], .bot)
  -- The function of the theorem is the expression, up to unfolding the evaluation.
  let fTarget ← elabTerm (← `(fun x : ℝ ↦ Verified.Expr.univariateEval
    $(← exprToSyntax (← quoteVerifiedExpr target)) x)) none
  let fTarget ← instantiateMVars fTarget
  let limitType ← instantiateMVars (← inferType limit)
  let expected := mkAppN limitType.getAppFn (limitType.getAppArgs.set! 2 fTarget)
  unless ← isDefEq limitType expected do
    throwError "limit: the expression does not match its equivalent"
  let limit ← mkExpectedTypeHint limit expected
  let proof ← if positive then pure limit else do
    -- From `f (-t)` at `+∞` to `f` at `-∞`.
    let quoted ← quoteVerifiedExpr expr
    let limitT ← exprToSyntax limit
    let value ← elabTerm (← `((Filter.tendsto_comp_neg_atTop_iff
      (f := fun x : ℝ ↦ Verified.Expr.univariateEval $(← exprToSyntax quoted) x)).mp (by
        convert ($limitT) using 1
        funext t
        simp [Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const])))
      none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasSorry then throwError "limit: the reflection to -∞ failed"
    pure value
  return (proof, value, info)

/-- Run `#cas [limit x → ±∞] f` by asymptotic comparison, and by the substitution `x = 1 / t` of
`CAS.Command.Limits` when the comparison fails. -/
def logAsymLimit (ref : Syntax) (coordinate : TSyntax `ident) (positive : Bool)
    (input : Syntax) : CommandElabM Unit := do
  let reified ← try parseExact input [coordinate.getId] catch _ => throwUnsupportedSyntax
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwUnsupportedSyntax
  unless transcendental expr do throwUnsupportedSyntax
  let result : Except MessageData (Lean.Expr × String × Info) ← liftTermElabM do
    let saved ← saveState
    try
      let (proof, value, info) ← asymptoticTheorem expr positive
      let cleaned ← Digits.cleanProof proof (Series.seriesCleanLemmas ++ [``one_mul,
          ``Int.cast_ofNat, ``Int.cast_neg, ``Real.exp_zero, ``one_pow, ``Real.sqrt_one,
          ``div_self, ``ne_eq, ``one_ne_zero, ``not_false_eq_true])
        [``Verified.Expr.univariateEval] (simprocs := true)
      let cleaned ← Digits.evaluateNumerals cleaned
      let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``div_one, ``Real.sqrt_one,
          ``neg_one_mul]
        (simprocs := true)
      let checked ← CAS.Tactic.Explanation.kernelCheckedProof "limit"
        (← inferType cleaned) cleaned
      let value ← match value with
        | .real _ => do
            -- The value as the cleaned statement shows it: `Tendsto f atTop (𝓝 v)`.
            let type ← instantiateMVars (← inferType cleaned)
            let target := type.getAppArgs.getD 4 type
            renderTerm (target.getAppArgs.back?.getD target)
        | value => value.render
      pure (.ok (checked, value, info))
    catch ex =>
      saved.restore
      pure (.error ex.toMessageData)
  let name := renderName coordinate.getId
  match result with
  | .error asymptotic =>
      try Limits.logLimit ref coordinate (.infinity positive) input
      catch inversion =>
        throwErrorAt input "limit: no route proved the limit at \
          {if positive then "∞" else "-∞"}.\nAsymptotic comparison:{indentD asymptotic}\n\
          Substitution {name} = 1 / t:{indentD inversion.toMessageData}"
  | .ok (proof, value, info) =>
      let report ← liftTermElabM do
        evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            "Limit by asymptotic comparison" proof]
      logReport ref {
        domain := if positive then s!"{name} → ∞" else s!"{name} → -∞"
        input := reified.render
        inputType := "scalar ℝ"
        output := value
        outputType := "limit from the dominant term"
      } #[computationNode "Asymptotic equivalent" #[
          m!"f ~ c x^{info.a} e^({info.b} x) (log x)^{info.k}" ++
            (if positive then m!"" else m!" in t = -x")], report]

end CAS.Command.AsymptoticLimits

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [limit $x:ident → ∞] $expr:term) =>
      AsymptoticLimits.logAsymLimit expr x true expr
  | `(#cas [limit $x:ident → - ∞] $expr:term) =>
      AsymptoticLimits.logAsymLimit expr x false expr

end CAS.Command
