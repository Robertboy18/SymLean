/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.RootSplit
public import CAS.Command.ExpPolynomials
public import CAS.Command.LinearAlgebra.Basic
public import CAS.Command.ParamSystems
public import CAS.Calculus.LinearODEOrder
public import CAS.Calculus.LinearODEVariable
public meta import CAS.Calculus.LinearODEOrder
public meta import CAS.Integration
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public meta import CAS.Tactic.RouteRegistry

/-!
# Linear differential equations with exact characteristic roots: `#cas [dsolve y x]`

`#cas [dsolve y x] (y''' - 6*y'' + 11*y' - 6*y = 0)` solves a linear equation of any order with
rational constant coefficients and a right side made of terms `xᵏ e ^ (a x) cos (b x)`,
`xᵏ e ^ (a x) sin (b x)`, when every root of the characteristic polynomial is known exactly, and
proves

`∀ y, (∀ k < n, Differentiable ℝ (iteratedDeriv k y)) → ((∀ x, equation) ↔`
`∃ c₁ … cₙ, ∀ x, y x = yp x + c₁ φ₁ x + ⋯ + cₙ φₙ x)`,

where the hypothesis reads `Differentiable ℝ y` at order one. With initial values
`y x₀ = v₀, y' x₀ = v₁, …` the answer is the single solution. A first-order equation
`y' + p(x) y = q(x)` with a coefficient depending on `x` is solved by the integrating factor,
`y = (Q + C) e ^ (-P)` with `P' = p` and `Q' = e ^ P q`. Characteristic roots known only by
enclosures are treated by `CAS.Command.DSolveRoot`; `CAS.Command.DSolve` reads the equation and
chooses the route.

## Implementation notes

For constant coefficients the search is untrusted. `CAS.Command.RootSplit` splits the
characteristic polynomial over `ℚ` into rational roots and the roots of quadratic factors
(rational root test, square-free decomposition, quadratic formula, and the factor provider of
`CASHex` when it is loaded), `ExpPolynomials.particular` finds the particular solution `yp` by
undetermined coefficients (see `CAS/Command/ExpPolynomials.lean`), and with initial values
`LinearAlgebra.QMatrix.solve?` solves the rational linear system of the constants. The kernel
decides the certificate: the coefficients recomputed from the factors (`LinearODE.charQ`), the
separation of the roots by rational boxes (`LinearODE.separated`) and the initial values
(`LinearODE.ivpCheck`). Tactic proofs check that `yp` solves the equation, through the symbolic
derivatives `Verified.Expr.iteratedDiff`, and that the equation as written is the monic normal
form `LinearODE.rLop` (`simp`, `push_cast`, `linear_combination`). Then `LinearODE.general_iff`,
or `LinearODE.ivp_general_iff` by uniqueness for the first-order system, gives the theorem; see
`CAS/Calculus/LinearODEOrder.lean`.

For a variable coefficient the checked integrator `integrate?` (see `CAS/Integration.lean`)
proposes a primitive `P` of `p` and a primitive `Q` of `e ^ P q`, and only primitives without
domain conditions are used. The kernel decides that each is an antiderivative
(`IntegrationCheck.route`, see `CAS/Integration/Check.lean`) with no requirements, and
`LinearODE.hasDerivAt_of_cert` with `LinearODE.firstOrder_iff`, or `LinearODE.firstOrder_ivp`
for one initial value, gives the theorem; see `CAS/Calculus/LinearODEVariable.lean`.
-/

public meta section

namespace CAS.Command.DSolveOrder

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.RootSplit
open CAS.Command.ExpPolynomials
open CAS.Command.Algebra (Dense)
open CAS.Verified.Expr
open CAS.LinearODE (CharRoot)

/-! ## Syntax for the certificate -/

/-- The functions of `CharRoot.funs ρ j`, written as `basisList` unfolds to them. -/
def funsSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (x : TSyntax `ident) (ρ : CharRoot)
    (j : Nat) : m (Array (TSyntax `term)) := do
  let jT ← natLit j
  match ρ with
  | .real r =>
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp ((($(← ratQ r) : ℚ) : ℝ) * $x))]
  | .realPair α c n => do
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ (n : ℚ)))
      let a ← `((($(← ratQ α) : ℚ) : ℝ))
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp (($a + $w) * $x)),
        ← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp (($a - $w) * $x))]
  | .pair α c n => do
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ (n : ℚ)))
      let a ← `((($(← ratQ α) : ℚ) : ℝ))
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp ($a * $x) * Real.cos ($w * $x)),
        ← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp ($a * $x) * Real.sin ($w * $x))]

/-- The functions of `CharRoot.ivpFuns ρ j`. -/
def ivpFunsSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (x : TSyntax `ident)
    (ρ : CharRoot) (j : Nat) : m (Array (TSyntax `term)) := do
  let jT ← natLit j
  match ρ with
  | .real r =>
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * Real.exp ((($(← ratQ r) : ℚ) : ℝ) * $x))]
  | .realPair α c n => do
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ (n : ℚ)))
      let a ← `((($(← ratQ α) : ℚ) : ℝ))
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * (Real.exp ($a * $x) * Real.cosh ($w * $x))),
        ← `(fun $x:ident : ℝ ↦ $x ^ $jT * (Real.exp ($a * $x) * (Real.sinh ($w * $x) / $w)))]
  | .pair α c n => do
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ (n : ℚ)))
      let a ← `((($(← ratQ α) : ℚ) : ℝ))
      return #[← `(fun $x:ident : ℝ ↦ $x ^ $jT * (Real.exp ($a * $x) * Real.cos ($w * $x))),
        ← `(fun $x:ident : ℝ ↦ $x ^ $jT * (Real.exp ($a * $x) * (Real.sin ($w * $x) / $w)))]

/-- The lemmas that restate the answer in ordinary notation. -/
def orderCleanLemmas : List Name :=
  ExpPolynomials.cleanLemmas ++ [``Rat.cast_neg, ``Rat.cast_div,
    ``Rat.cast_natCast, ``Rat.cast_intCast, ``Rat.cast_one, ``Rat.cast_zero, ``pow_zero,
    ``pow_one, ``one_mul, ``mul_one, ``zero_add, ``add_zero, ``zero_mul, ``mul_zero,
    ``Real.sqrt_one, ``div_one, ``neg_zero, ``zero_sub, ``iteratedDeriv_zero,
    ``iteratedDeriv_one]

/-- `y`, `y'`, `y''`, … -/
def primed (y : Name) (k : Nat) : Name :=
  Name.mkSimple (y.toString (escape := false) ++ String.ofList (List.replicate k '\''))

/-- The hypothesis on `y` in the stated theorems: `Differentiable ℝ y` at order one and
`∀ k < n, Differentiable ℝ (iteratedDeriv k y)` above, with `j` for `k` when the function is
named `k`. -/
def regularity (y : TSyntax `term) (n : Nat) : TermElabM (TSyntax `term) := do
  if n = 1 then `(Differentiable ℝ $y)
  else
    let k := mkIdent (if y.raw.getId == `k then `j else `k)
    `(∀ $k:ident < $(← natLit n), Differentiable ℝ (iteratedDeriv $k $y))

/-- A proof `hy` of `regularity y n`, in the form `∀ k < n, …` of `LinearODE.general_iff`. -/
def regularityProof (hy : TSyntax `term) (n : Nat) : TermElabM (TSyntax `term) :=
  if n = 1 then `(LinearODE.forall_lt_one_of_differentiable $hy) else pure hy

/-- The environment `![x, y x, y' x, y⁽²⁾ x, …]` of the reflected equation. -/
def envSyntax (x y : TSyntax `term) (n : Nat) : TermElabM (TSyntax `term) := do
  let mut entries : Array (TSyntax `term) := #[x, ← `($y $x)]
  for k in [1:n + 1] do
    entries := entries.push (← if k = 1 then `(deriv $y $x)
      else `(iteratedDeriv $(⟨Syntax.mkNumLit (toString k)⟩) $y $x))
  `(![$entries,*])

/-! ## Constant coefficients, any order -/

/-- Run `#cas [dsolve y x, conditions] equation` for an equation of order `order` with the
rational constant coefficients `coefficients` (constant term first) whose characteristic roots
`rs` are all known exactly and separated at precision `prec`. -/
def logOrder (ref : Syntax) (y x : TSyntax `ident) (conditions : Array (TSyntax `term))
    (input : Syntax) (order : Nat) {N : Nat} (E : Verified.Expr (Fin N))
    (coefficients : Array ℚ) (rs : List (CharRoot × Nat)) (prec : Nat) :
    CommandElabM Unit := do
  let yName := y.getId
  let xName := x.getId
  let n := order
  let top := coefficients.getD n 1
  let monic := coefficients.map (· / top)
  -- The forcing and a particular solution.
  let F0 : Verified.Expr (Fin 1) := E.mapVars fun i ↦
    if i.val = 0 then (.var 0 : Verified.Expr (Fin 1)) else .nat 0
  let F : Verified.Expr (Fin 1) := .neg F0
  let some forcing := toExpPoly F
    | throwErrorAt input "dsolve: the right side is not a sum of terms x ^ k e ^ (a x) \
        cos (b x) and x ^ k e ^ (a x) sin (b x) with rational a, b"
  let some Y := particular monic (epScale (GaussianRat.ofRat (1 / top)) forcing)
    | throwErrorAt input "dsolve: no particular solution was found"
  unless conditionFree Y do throwErrorAt input "dsolve: unexpected particular solution"
  -- The characteristic polynomial, factored.
  let d := LinearODE.degQ rs
  unless d = n && (List.range (n + 1)).all (fun k ↦ LinearODE.charQ rs k == monic.getD k 0) do
    throwErrorAt input "dsolve: the factorization of the characteristic polynomial failed"
  -- Initial values.
  let mut x₀ : ℚ := 0
  let mut values : Array (Option ℚ) := Array.replicate n none
  for condition in conditions do
    match condition with
    | `($f:ident $point:term = $value:term) =>
        let point ← parseRational "dsolve" point
        let value ← parseRational "dsolve" value
        let some k := (List.range n).find? fun k ↦ primed yName k == f.getId
          | throwErrorAt condition "dsolve: expected {yName} x₀ = …, {primed yName 1} x₀ = …, \
              up to the derivative of order {n - 1}"
        if values.any (·.isSome) then
          unless point = x₀ do
            throwErrorAt condition "dsolve: the initial values must be given at one point"
        x₀ := point
        values := values.set! k (some value)
    | _ => throwErrorAt condition "dsolve: expected an initial value such as {yName} 0 = 1"
  let ivp := !conditions.isEmpty
  if ivp && values.any (·.isNone) then
    throwErrorAt ref "dsolve: give the values of {yName} and its derivatives up to order \
      {n - 1} at one point"
  let yT : TSyntax `term := ⟨y.raw⟩
  let xT : TSyntax `term := ⟨x.raw⟩
  let topT ← real top
  let surdText (c : ℚ) (m : ℚ) : String :=
    if m = 1 then s!"{c}" else if c = 1 then s!"√{m}" else s!"{c}√{m}"
  let pairText (α : ℚ) (w : String) (i : String) : String :=
    let wi := if w == "1" && i != "" then "i" else w ++ i
    if α = 0 then s!"±{wi}" else s!"{α} ± {wi}"
  let caseText : String := s!"order {n}, characteristic roots: " ++ ", ".intercalate
    (rs.map fun (ρ, k) ↦ (match ρ with
      | .real r => s!"{r}"
      | .realPair α c m => pairText α (surdText c m) ""
      | .pair α c m => pairText α (surdText c m) " i") ++
        (if k > 1 then s!" (multiplicity {k})" else ""))
  let proof ← liftTermElabM do
    let quote (source : Verified.Expr (Fin 1)) : TermElabM (TSyntax `term) := do
      exprToSyntax (← quoteVerifiedExpr source)
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let FT ← quote F
    let YT ← quote Y
    let RS ← listSyntax (← rs.toArray.mapM fun (ρ, k) ↦ do
      `(($(← rootSyntax ρ), $(← natLit k))))
    let A ← listSyntax (← (monic.map id).mapM ratQ)
    let dT ← natLit n
    let precT ← natLit prec
    let hcf ← certified (← `(Verified.Expr.conditionFree $YT = true))
    let hv ← certified (← `(∀ e ∈ ($RS : List (LinearODE.CharRoot × ℕ)), e.1.Valid))
    let hsep ← certified (← `(LinearODE.separated $RS $precT = true))
    let hc ← certified (← `((List.range (LinearODE.degQ $RS + 1)).map (LinearODE.charQ $RS) =
      ($A : List ℚ)))
    let env ← envSyntax xT yT n
    let equation ← `(∀ $x:ident, Verified.Expr.eval $env $ET = 0)
    let hdeg ← `((show LinearODE.degQ $RS = $dT by rfl))
    let sumSimp ← `(tactic| simp only [LinearODE.rLop, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ,
      iteratedDeriv_zero, iteratedDeriv_one])
    let evalSimp ← `(tactic| simp only [Verified.Expr.univariateEval,
      Verified.Expr.euclideanSingle_eq_const, Verified.Expr.eval, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_ofNat, Int.cast_neg,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_zero])
    -- `equation ↔ ∀ x, rLop … y x = F x / top`.
    let bridgeStatement ← `(∀ $y:ident : ℝ → ℝ, ($equation) ↔ ∀ $x:ident,
      LinearODE.rLop (LinearODE.degQ $RS) (fun k ↦ ((($A : List ℚ).getD k 0 : ℚ) : ℝ)) $yT $xT =
        Verified.Expr.univariateEval $FT $xT / $topT)
    let bridgeProof ← `(by
      intro $y:ident
      rw [$hdeg:term]
      apply forall_congr'
      intro $x:ident
      $sumSimp:tactic
      $evalSimp:tactic
      push_cast
      constructor
      · intro h
        linear_combination (1 / $topT) * h
      · intro h
        linear_combination ($topT) * h)
    let bridge ← exprToSyntax (← elabCheckedProof "dsolve" bridgeStatement bridgeProof)
    let partStatement ← `(∀ $x:ident, LinearODE.rLop (LinearODE.degQ $RS)
      (fun k ↦ ((($A : List ℚ).getD k 0 : ℚ) : ℝ)) (Verified.Expr.univariateEval $YT) $xT =
        Verified.Expr.univariateEval $FT $xT / $topT)
    let partProof ← `(by
      intro $x:ident
      rw [$hdeg:term]
      simp only [LinearODE.rLop, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        List.getD_cons_zero, List.getD_cons_succ, LinearODE.iteratedDeriv_univariateEval $hcf]
      simp only [Verified.Expr.iteratedDiff, Verified.Expr.diff, ↓reduceIte]
      $evalSimp:tactic
      push_cast
      ring_nf)
    let part ← exprToSyntax (← elabCheckedProof "dsolve" partStatement partProof)
    let hy' ← `((by rw [$hdeg:term]; exact $(← regularityProof (← `(hy)) n)))
    let regular ← regularity yT n
    if ivp then
      -- Constants of the combination: `∑ cᵢ ψᵢ⁽ᵏ⁾ (0) = vₖ - yp⁽ᵏ⁾ (x₀)`.
      let targets ← (Array.range n).mapM fun k ↦ do
        let some b := exactValue? (fun _ ↦ x₀) (Y.iteratedDiff 0 k)
          | throwError "dsolve: the particular solution has no exact derivative at {x₀}"
        pure ((values.getD k none).getD 0 - b)
      let rows := (Array.range n).map fun k ↦ (LinearODE.ivpValues rs k).toArray
      let some cs := LinearAlgebra.QMatrix.solve? rows targets n
        | throwError "dsolve: the initial values do not determine the constants"
      let CS ← listSyntax (← cs.mapM ratQ)
      let V ← listSyntax (← (values.map (·.getD 0)).mapM ratQ)
      let x₀Q ← ratQ x₀
      let hcheck ← certified (← `(LinearODE.ivpCheck $YT $x₀Q $RS $CS $V = true))
      -- The explicit combination.
      let mut ψs : Array (TSyntax `term) := #[]
      for (ρ, k) in rs do
        for j in [0:k] do
          ψs := ψs ++ (← ivpFunsSyntax x ρ j)
      let t := mkIdent `t
      let mut combT : TSyntax `term ← `(0)
      for (ψ, c) in (ψs.zip cs).reverse do
        combT ← `((($(← ratQ c) : ℚ) : ℝ) * $ψ $t + $combT)
      let x₀R ← `((($x₀Q : ℚ) : ℝ))
      let hcomb ← `((show ∀ $t:ident : ℝ,
        LinearODE.comb (LinearODE.ivpList $RS) $CS $t = $combT from fun _ ↦ rfl))
      let mut inits : Array (TSyntax `term) := #[]
      for k in [0:n] do
        let vT ← `((($(← ratQ ((values.getD k none).getD 0)) : ℚ) : ℝ))
        inits := inits.push (← if k = 0 then `($yT $x₀R = $vT)
          else if k = 1 then `(deriv $yT $x₀R = $vT)
          else `(iteratedDeriv $(⟨Syntax.mkNumLit (toString k)⟩) $yT $x₀R = $vT))
      let initConj ← inits.pop.foldrM (fun a acc ↦ `($a ∧ $acc)) (inits.back!)
      let combAt ← `(fun $t:ident ↦ $combT)
      let statement ← `(∀ $y:ident : ℝ → ℝ, $regular →
        (($equation) ∧ $initConj ↔ ∀ $x:ident, $yT $xT =
          Verified.Expr.univariateEval $YT $xT + $combAt ($xT - $x₀R)))
      let initProof ← `(by
        rw [$hdeg:term]
        intro h k hk
        interval_cases k <;> simp_all)
      let pieces ← (Array.range n).mapM fun k ↦ do
        `(by simpa using h $(← natLit k) (by norm_num))
      let initProof' ← if n = 1 then `(by
          rw [$hdeg:term]
          intro h
          exact $(pieces[0]!))
        else `(by
          rw [$hdeg:term]
          intro h
          exact ⟨$pieces,*⟩)
      let body ← `(fun $y:ident hy ↦ (and_congr ($bridge $yT)
          ⟨($initProof : _ → _), ($initProof' : _ → _)⟩).trans
        ((LinearODE.ivp_general_iff $RS $hv $A $hc $hcf $part $x₀Q $CS $V rfl $hcheck
          $hy').trans (forall_congr' fun $x:ident ↦ by rw [$hcomb:term])))
      elabCheckedProof "dsolve" statement body
    else
      -- The general solution.
      let mut φs : Array (TSyntax `term) := #[]
      for (ρ, k) in rs do
        for j in [0:k] do
          φs := φs ++ (← funsSyntax x ρ j)
      let cIdents : Array (TSyntax `ident) := (Array.range n).map fun i ↦
        mkIdent (Name.mkSimple s!"c{(Nat.toSubscriptString (i + 1))}")
      let mut family : TSyntax `term ← `(Verified.Expr.univariateEval $YT $xT)
      for (φ, c) in φs.zip cIdents do
        family ← `($family + $c * $φ $xT)
      let mut exists_ : TSyntax `term ← `(∀ $x:ident, $yT $xT = $family)
      for c in cIdents.reverse do
        exists_ ← `(∃ $c:ident : ℝ, $exists_)
      let statement ← `(∀ $y:ident : ℝ → ℝ, $regular → (($equation) ↔ $exists_))
      let hbasis ← `((show LinearODE.basisList $RS = $(← listSyntax φs) by rfl))
      let mut conv : TSyntax `term ← `(forall_congr' fun $x:ident ↦
        ⟨fun h ↦ by linear_combination h, fun h ↦ by linear_combination h⟩)
      for c in cIdents.reverse do
        conv ← `(exists_congr fun $c:ident ↦ $conv)
      let body ← `(fun $y:ident hy ↦ by
        rw [$bridge $yT, LinearODE.general_iff $RS $hv $hsep $A $hc
          (Verified.Expr.contDiff_of_conditionFree $hcf _) $part $hy', $hbasis:term]
        simp only [LinearODE.mem_span_cons_iff, LinearODE.mem_span_nil_iff]
        exact $conv)
      elabCheckedProof "dsolve" statement body
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof orderCleanLemmas
      [``Verified.Expr.univariateEval, ``LinearODE.CharRoot.width] (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``zero_add, ``add_zero,
      ``sub_zero, ``zero_mul, ``mul_zero, ``neg_mul, ``Real.exp_zero, ``zero_sub, ``neg_zero]
      (simprocs := true)
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "dsolve" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        (if ivp then "The unique solution of the initial-value problem"
          else "The general solution, and every solution has this form") proof]
  let answer ← liftTermElabM do
    let some rhs ← solutionRhs (← inferType proof) | pure "see the statement"
    pure s!"{yName}({xName}) = {rhs}"
  logReport ref {
    domain := s!"{xName} ∈ ℝ"
    input := surfaceText input
    inputType := s!"linear equation of order {n} with constant coefficients"
    output := answer
    outputType := caseText
  } #[report]

/-! ## First order with a variable coefficient -/

/-- The primitive of `integrand` that the checked integrator finds, when its certificate has no
domain requirements. -/
def primitiveIn {m : Type → Type} [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (command : String) (integrand : Verified.Expr (Fin 1)) (what : String) :
    m (Verified.Expr (Fin 1)) := do
  let provider? := (← Tactic.RouteRegistry.factorProvider?).map
    CAS.Polynomial.Sparse.Univariate.RationalFactorization.ofDense
  let some cert := integrate? (0 : Fin 1) integrand provider?
    | throwError "{command}: the checked integrator found no primitive of {what}"
  unless cert.requirements.nonzero.isEmpty && cert.requirements.positive.isEmpty do
    throwError "{command}: the primitive of {what} holds only under domain conditions, which \
      this command does not treat"
  return cert.candidate

/-- Run `#cas [dsolve y x, conditions] (a y' + p(x) y = q(x))`. -/
def logVariable (ref : Syntax) (y x : TSyntax `ident) (conditions : Array (TSyntax `term))
    (input : Syntax) {N : Nat} (E : Verified.Expr (Fin N)) (top : ℚ)
    (coefficient : Verified.Expr (Fin 1)) : CommandElabM Unit := do
  let yName := y.getId
  let xName := x.getId
  let F0 : Verified.Expr (Fin 1) := E.mapVars fun i ↦
    if i.val = 0 then (.var 0 : Verified.Expr (Fin 1)) else .nat 0
  let p : Verified.Expr (Fin 1) := .mul (ratExpr (1 / top)) coefficient
  let q : Verified.Expr (Fin 1) := .mul (ratExpr (-1 / top)) F0
  let P ← primitiveIn "dsolve" p "the coefficient"
  let Q ← primitiveIn "dsolve" (.mul (.exp P) q) "e ^ P times the right side"
  let mut ivpData : Option (ℚ × ℚ) := none
  for condition in conditions do
    match condition with
    | `($f:ident $point:term = $value:term) =>
        unless f.getId == yName && ivpData.isNone do
          throwErrorAt condition "dsolve: a first-order equation takes one value {yName} x₀ = y₀"
        ivpData := some (← parseRational "dsolve" point, ← parseRational "dsolve" value)
    | _ => throwErrorAt condition "dsolve: expected an initial value such as {yName} 0 = 1"
  let yT : TSyntax `term := ⟨y.raw⟩
  let xT : TSyntax `term := ⟨x.raw⟩
  let topT ← real top
  let proof ← liftTermElabM do
    let quote (source : Verified.Expr (Fin 1)) : TermElabM (TSyntax `term) := do
      exprToSyntax (← quoteVerifiedExpr source)
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let pT ← quote p
    let qT ← quote q
    let PT ← quote P
    let QT ← quote Q
    let integrandT ← `(Verified.Expr.mul (Verified.Expr.exp $PT) $qT)
    let routeP ← certified (← `((IntegrationCheck.route (0 : Fin 1) $pT $PT).rhs = 0))
    let routeQ ← certified (← `((IntegrationCheck.route (0 : Fin 1) $integrandT $QT).rhs = 0))
    let certP ← `((IntegrationCheck.AntiderivativeCert.mk $PT $routeP :
      IntegrationCheck.AntiderivativeCert (0 : Fin 1) $pT))
    let certQ ← `((IntegrationCheck.AntiderivativeCert.mk $QT $routeQ :
      IntegrationCheck.AntiderivativeCert (0 : Fin 1) $integrandT))
    let reqP ← certified (← `(($certP).requirements.nonzero.isEmpty &&
      ($certP).requirements.positive.isEmpty = true))
    let reqQ ← certified (← `(($certQ).requirements.nonzero.isEmpty &&
      ($certQ).requirements.positive.isEmpty = true))
    let hP ← `(fun t ↦ LinearODE.hasDerivAt_of_cert $certP $reqP t)
    let hQ ← `(fun t ↦ LinearODE.hasDerivAt_of_cert $certQ $reqQ t)
    let env ← envSyntax xT yT 1
    let equation ← `(∀ $x:ident, Verified.Expr.eval $env $ET = 0)
    let bridgeStatement ← `(∀ $y:ident : ℝ → ℝ, ($equation) ↔ ∀ $x:ident,
      deriv $yT $xT + (Verified.Expr.univariateEval $pT $xT) * $yT $xT =
        Verified.Expr.univariateEval $qT $xT)
    let bridgeProof ← `(by
      intro $y:ident
      apply forall_congr'
      intro $x:ident
      simp only [Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const,
        Verified.Expr.eval, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Int.cast_ofNat, Int.cast_neg, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_zero, Int.cast_one, Int.cast_zero]
      push_cast
      constructor
      · intro h
        linear_combination (1 / $topT) * h
      · intro h
        linear_combination ($topT) * h)
    let bridge ← exprToSyntax (← elabCheckedProof "dsolve" bridgeStatement bridgeProof)
    match ivpData with
    | none =>
        let C := mkIdent `C
        let statement ← `(∀ $y:ident : ℝ → ℝ, Differentiable ℝ $yT →
          (($equation) ↔ ∃ $C:ident : ℝ, ∀ $x:ident, $yT $xT =
            (Verified.Expr.univariateEval $QT $xT + $C) *
              Real.exp (-Verified.Expr.univariateEval $PT $xT)))
        let body ← `(fun $y:ident hy ↦ ($bridge $yT).trans (LinearODE.firstOrder_iff $hP $hQ hy))
        elabCheckedProof "dsolve" statement body
    | some (x₀, y₀) =>
        let x₀T ← real x₀
        let y₀T ← real y₀
        let statement ← `(∀ $y:ident : ℝ → ℝ, Differentiable ℝ $yT →
          ((($equation) ∧ $yT $x₀T = $y₀T) ↔ ∀ $x:ident, $yT $xT =
            (Verified.Expr.univariateEval $QT $xT + ($y₀T *
              Real.exp (Verified.Expr.univariateEval $PT $x₀T) -
                Verified.Expr.univariateEval $QT $x₀T)) *
              Real.exp (-Verified.Expr.univariateEval $PT $xT)))
        let body ← `(fun $y:ident hy ↦ (and_congr_left' ($bridge $yT)).trans
          (LinearODE.firstOrder_ivp $hP $hQ $x₀T $y₀T hy))
        elabCheckedProof "dsolve" statement body
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof orderCleanLemmas
      [``Verified.Expr.univariateEval, ``LinearODE.CharRoot.width] (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``zero_add, ``add_zero,
      ``sub_zero, ``zero_mul, ``mul_zero, ``neg_mul, ``Real.exp_zero, ``zero_sub, ``neg_zero]
      (simprocs := true)
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "dsolve" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        (if ivpData.isSome then "The unique solution of the initial-value problem"
          else "The general solution by the integrating factor, and every solution has this \
            form") proof]
  let answer ← liftTermElabM do
    let some rhs ← solutionRhs (← inferType proof) | pure "see the statement"
    pure s!"{yName}({xName}) = {rhs}"
  logReport ref {
    domain := s!"{xName} ∈ ℝ"
    input := surfaceText input
    inputType := "linear equation of order one with a variable coefficient"
    output := answer
    outputType := "integrating factor e ^ P"
  } #[report]

end CAS.Command.DSolveOrder
