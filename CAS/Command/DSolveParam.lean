/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.DSolveOrder
public import CAS.Command.ParamSystems
public import CAS.Calculus.ExpTrigPrimitive
public meta import CAS.Integration.ExponentialTrig
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# First-order equations with symbolic coefficients: `#cas [dsolve y x]`

`#cas [dsolve y x] (y' + p * y = q)` with `p` a constant expression in other variables and `q` a
sum of terms `c xᵏ e ^ (a x) cos (b x)`, `c xᵏ e ^ (a x) sin (b x)` (parameters allowed) uses
the integrating factor `e ^ (p x)` and proves, for all values of the parameters, that the
solutions are `y = (Q + C) e ^ (-p x)` with `Q` a primitive of `e ^ (p x) q`. The conditions
with parameters that the primitive needs, such as `(p + a) ^ 2 + b ^ 2 ≠ 0`, are hypotheses of
the theorem. Equations of higher order and initial values are refused.

## Implementation notes

`logParam` reads the coefficients of `y'` and of `y` as partial derivatives of `lhs - rhs`; the
first must be a nonzero rational constant, the second free of `x`. `terms?` (see
`CAS/Integration/ExponentialTrig.lean`) splits `q` into terms `c xᵏ e ^ (a x) cos (b x)` and
`c xᵏ e ^ (a x) sin (b x)`, and the factor `e ^ (p x)` turns each rate `a` into `p + a`. Each term
has its primitive in closed form, `CAS.ExpTrig.primPair` or `CAS.ExpTrig.primExp`, and
`CAS.ExpTrig.hasDerivAt_primPair` and `CAS.ExpTrig.hasDerivAt_primExp` prove its derivative for
all real rates and frequencies under `(p + a) ^ 2 + b ^ 2 ≠ 0` or `p + a ≠ 0`, so the parameters
stay symbolic; see `CAS/Calculus/ExpTrigPrimitive.lean`. A condition without parameters is
proved by `norm_num`, the others become the hypotheses `h0`, `h1`, …. A tactic proof restates the
equation as `y' + p y = q` (`simp`, `push_cast`, `linear_combination`), and
`LinearODE.firstOrder_iff` gives the family; see `CAS/Calculus/LinearODEVariable.lean`.
-/

public meta section

namespace CAS.Command.DSolveParam

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.ExpPolynomials
open CAS.IntegrationPlanner.ExponentialTrig
open CAS.Verified.Expr

/-- The primitive of a sum of terms, the theorem term for its derivative, and the conditions
that are not numeric (named `h0`, `h1`, … in order). The coefficients are evaluated in
`env0`, with `x` replaced by `0`. -/
def buildPrimitive {N : Nat} (env0 xT : TSyntax `term)
    (ts : List (Bool × CAS.IntegrationPlanner.ExponentialTrig.Term N)) :
    TermElabM (TSyntax `term × TSyntax `term × Array (TSyntax `term)) := do
  let quote (source : Verified.Expr (Fin N)) : TermElabM (TSyntax `term) := do
    exprToSyntax (← quoteVerifiedExpr source)
    -- For each term: the coefficient, `a`, `b`, the component, the condition.
  let mut pieces :
      Array (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term × Bool) := #[]
  for (negative, t) in ts do
    let cT ← `(Verified.Expr.eval $env0 $(← quote t.coeff))
    let cT ← if negative then `(-$cT) else pure cT
    let kT : TSyntax `term := ⟨Syntax.mkNumLit (toString t.power)⟩
    let numeric := t.rate.all isConst && t.freq.all fun (b, _) ↦ isConst b
    -- The primitive, its derivative theorem, and its condition.
    let (comp, rule, cond) ← match t.rate, t.freq with
      | some a, some (b, isSin) => do
          let aT ← `(Verified.Expr.eval $env0 $(← quote a))
          let bT ← `(Verified.Expr.eval $env0 $(← quote b))
          let cond ← `($aT ^ 2 + $bT ^ 2 ≠ 0)
          if isSin then
            pure (← `((CAS.ExpTrig.primPair $aT $bT $kT).2 $xT),
              ← `(fun h ↦ (CAS.ExpTrig.hasDerivAt_primPair h $kT $xT).2), cond)
          else
            pure (← `((CAS.ExpTrig.primPair $aT $bT $kT).1 $xT),
              ← `(fun h ↦ (CAS.ExpTrig.hasDerivAt_primPair h $kT $xT).1), cond)
      | some a, none => do
          let aT ← `(Verified.Expr.eval $env0 $(← quote a))
          pure (← `(CAS.ExpTrig.primExp $aT $kT $xT),
            ← `(fun h ↦ CAS.ExpTrig.hasDerivAt_primExp h $kT $xT), ← `($aT ≠ 0))
      | none, _ => throwError "dsolve: a term without exponential factor"
    pieces := pieces.push (← `($cT * $comp), rule, cT, cond, numeric)
  -- The primitive and the derivative.
  let mut Fbody : Option (TSyntax `term) := none
  let mut hyps : Array (TSyntax `term) := #[]
  let mut haves : Array (TSyntax `term) := #[]
  for (piece, rule, cT, cond, numeric) in pieces do
    Fbody := some (← match Fbody with
      | none => pure piece
      | some acc => `($acc + $piece))
    let condProof ← if numeric then `((by norm_num [Verified.Expr.eval] : $cond))
      else do
        let hname := mkIdent (Name.mkSimple s!"h{hyps.size}")
        hyps := hyps.push cond
        pure ⟨hname.raw⟩
    haves := haves.push (← `((($rule) $condProof).const_mul $cT))
  let some Fb := Fbody | throwError "dsolve: no term"
  let mut total := haves[0]!
  for h in haves.toList.drop 1 do
    total ← `(($total).fun_add $h)
  return (Fb, total, hyps)

/-- The parameters of `e`: its identifiers other than `x`, `y`, the derivatives of `y` up to
`order` and the names of functions and constants. -/
def parameters (y x : Name) (order : Nat) (e : Syntax) : List Name :=
  let skip := ParamSystems.functionNames ++ [`Real.exp, `Real.sin, `Real.cos, `Real.pi, `e]
  let derivatives := (List.range (order + 1)).map (DSolveOrder.primed y)
  ((ExpPolynomials.identifiers e).toList.filter fun n ↦ !n.isAnonymous && n != x &&
    !derivatives.contains n && !skip.contains n).eraseDups

/-- Run `#cas [dsolve y x] (a y' + p y = q)` with symbolic `p`, for an equation of order
`order` whose parameters are not empty. -/
def logParam (ref : Syntax) (y x : TSyntax `ident) (conditions : Array (TSyntax `term))
    (input : Syntax) (order : Nat) : CommandElabM Unit := do
  let (lhs, rhs) ← match unparen input with
    | `($l:term = $r:term) => pure (l, r)
    | _ => throwErrorAt input "dsolve: expected an equation lhs = rhs"
  let yName := y.getId
  let d1 := DSolveOrder.primed yName 1
  let params := parameters yName x.getId order input
  if order ≥ 2 then
    throwErrorAt input "dsolve: symbolic coefficients are treated for first-order equations"
  unless conditions.isEmpty do
    throwErrorAt input "dsolve: initial values with symbolic coefficients are not treated"
  let names := [x.getId, yName, d1] ++ params
  let reified ← parseExact (← `($lhs - $rhs)) names
  let N := reified.names.length
  let E := reified.expr
  unless 3 ≤ N do throwErrorAt input "dsolve: the equation could not be read"
  let varIs (i : Fin N) (k : Nat) : Bool := i.val = k
  let coefficient (k : Nat) : Verified.Expr (Fin N) :=
    if h : k < N then Verified.Expr.simplify (E.diff ⟨k, h⟩) else .nat 0
  let cTop := coefficient 2
  let cY := coefficient 1
  let mentions (c : Verified.Expr (Fin N)) (ks : List Nat) : Bool :=
    (List.finRange N).any fun i ↦ ks.contains i.val && c.containsVar i
  if mentions cTop ((List.range N)) || mentions cY [0, 1, 2] then
    throwErrorAt input "dsolve: the equation must be linear, with a coefficient of y free of x"
  let some top := exactValue? (fun _ ↦ (0 : ℚ)) cTop
    | throwErrorAt input "dsolve: the coefficient of {d1} must be a rational constant"
  if top = 0 then throwErrorAt input "dsolve: the coefficient of {d1} vanishes"
  let F0 : Verified.Expr (Fin N) := Verified.Expr.simplify (E.mapVars fun i ↦
    if varIs i 1 || varIs i 2 then .nat 0 else .var i)
  let constant (q : ℚ) : Verified.Expr (Fin N) :=
    (ratExpr q).mapVars fun _ ↦ (.nat 0 : Verified.Expr (Fin N))
  let pE : Verified.Expr (Fin N) := .mul (constant (1 / top)) cY
  let qE : Verified.Expr (Fin N) := .mul (constant (-1 / top)) F0
  let some ts := terms? qE
    | throwErrorAt input "dsolve: the right side is not a sum of terms x ^ k e ^ (a x) \
        cos (b x) and x ^ k e ^ (a x) sin (b x)"
  -- `e ^ (p x) q`: every term gets the exponent `p + a`.
  let shifted := ts.map fun (s, t) ↦
    (s, { t with rate := some (match t.rate with | some a => .add pE a | none => pE) })
  let xT : TSyntax `term := ⟨x.raw⟩
  let yT : TSyntax `term := ⟨y.raw⟩
  let paramIdents : Array (TSyntax `ident) := params.toArray.map mkIdent
  let paramTerms : Array (TSyntax `term) := paramIdents.map fun i ↦ ⟨i.raw⟩
  let proof ← liftTermElabM do
    let quote (source : Verified.Expr (Fin N)) : TermElabM (TSyntax `term) := do
      exprToSyntax (← quoteVerifiedExpr source)
    let zero : TSyntax `term ← `((0 : ℝ))
    let envEntries := #[xT, ← `($yT $xT), ← `(deriv $yT $xT)] ++ paramTerms
    let env0Entries := #[zero, zero, zero] ++ paramTerms
    let envXEntries := #[xT, zero, zero] ++ paramTerms
    let env ← `(![$envEntries,*])
    let env0 ← `(![$env0Entries,*])
    let envX ← `(![$envXEntries,*])
    let ET ← quote E
    let pT ← `(Verified.Expr.eval $env0 $(← quote pE))
    let qT ← `(fun $x:ident ↦ Verified.Expr.eval $envX $(← quote qE))
    let (Qb, total, hyps) ← buildPrimitive env0 xT shifted
    let topT ← real top
    let simpEval ← `(tactic| simp only [Verified.Expr.eval, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_ofNat, Int.cast_neg,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_zero])
    let C := mkIdent `C
    let mut core : TSyntax `term ← `(∀ $y:ident : ℝ → ℝ, Differentiable ℝ $yT →
      ((∀ $x:ident, Verified.Expr.eval $env $ET = 0) ↔
        ∃ $C:ident : ℝ, ∀ $x:ident, $yT $xT = ($Qb + $C) * Real.exp (-($pT * $xT))))
    for c in hyps.reverse do
      core ← `($c → $core)
    for p in paramIdents.reverse do
      core ← `(∀ $p:ident : ℝ, $core)
    let introHyps : Array (TSyntax `term) := (Array.range hyps.size).map fun i ↦
      ⟨(mkIdent (Name.mkSimple s!"h{i}")).raw⟩
    let introArgs : Array (TSyntax `term) := paramTerms ++ introHyps ++ #[⟨y.raw⟩]
    let proofT ← `(by
      intro $introArgs* hy
      have hP : ∀ $x:ident, HasDerivAt (fun $x:ident ↦ $pT * $xT) $pT $xT := fun $x:ident ↦ by
        simpa using (hasDerivAt_id $xT).const_mul $pT
      have hQ : ∀ $x:ident, HasDerivAt (fun $x:ident ↦ $Qb)
          (Real.exp ($pT * $xT) * $qT $xT) $xT := fun $x:ident ↦ by
        refine ($total).congr_deriv ?_
        $simpEval:tactic
        try simp only [add_mul, Real.exp_add]
        ring_nf
      have hbridge : (∀ $x:ident, Verified.Expr.eval $env $ET = 0) ↔
          ∀ $x:ident, deriv $yT $xT + ((fun _ ↦ $pT) $xT) * $yT $xT = $qT $xT := by
        apply forall_congr'
        intro $x:ident
        $simpEval:tactic
        push_cast
        constructor
        · intro h
          linear_combination (1 / $topT) * h
        · intro h
          linear_combination ($topT) * h
      rw [hbridge]
      exact LinearODE.firstOrder_iff hP hQ hy)
    elabCheckedProof "dsolve" core proofT
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof (DSolveOrder.orderCleanLemmas ++
        [``Matrix.head_cons, ``add_zero, ``sub_zero])
      [``Verified.Expr.univariateEval, ``CAS.ExpTrig.primPair,
        ``CAS.ExpTrig.baseCos, ``CAS.ExpTrig.baseSin,
        ``CAS.ExpTrig.primExp] (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "dsolve" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The general solution by the integrating factor, and every solution has this form"
        proof]
  let answer ← liftTermElabM do
    let some rhs ← solutionRhs (← inferType proof) | pure "see the statement"
    pure s!"{yName}({x.getId}) = {rhs}"
  logReport ref {
    domain := s!"{x.getId} ∈ ℝ"
    input := surfaceText input
    inputType := "linear equation of order one with symbolic coefficients"
    output := answer
    outputType := "integrating factor e ^ (p x)"
  } #[report]

end CAS.Command.DSolveParam
