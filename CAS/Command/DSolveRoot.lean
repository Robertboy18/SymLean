/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.DSolveOrder
public import CAS.Command.RootSplit
public import CAS.Calculus.LinearODERoots
public meta import CAS.Calculus.LinearODERoots
public meta import CAS.Command.DSolveOrder
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Characteristic roots without closed form: `#cas [dsolve y x]`

When some roots of the characteristic polynomial of a linear equation with constant rational
coefficients are not known exactly, as for `y'''' + y = 0` or `y''' - 2 y = 0` (irreducible over
`ℚ`), `#cas [dsolve y x]` names each root of the product `R` of the factors that
`CAS.Command.RootSplit` leaves without closed form by an enclosure that contains no other root of
`R`: `AlgRoot.real R lo hi` for a real root in `(lo, hi)` and `AlgRoot.complex R u v ρ` for a
complex root within `ρ` of `u + v i`, one of each conjugate pair. The theorem states the
enclosures with the equation `R (r) = 0` of each root, as `let` bindings `r₁, z₁, …`, and

`∀ y, (∀ k < n, Differentiable ℝ (iteratedDeriv k y)) → ((∀ x, equation) ↔`
`∃ c₁ … cₙ, ∀ x, y x = yp x + c₁ φ₁ x + ⋯ + cₙ φₙ x)`

with `φ` among `xʲ e ^ (r x)`, `e ^ (Re z x) cos (Im z x)` and `e ^ (Re z x) sin (Im z x)`.
`CAS.Command.DSolve` refuses initial values in this case.

## Implementation notes

The enclosures are computed numerically and refined by Newton steps in exact arithmetic, both
untrusted, in `CAS/Command/RootSplit.lean`; the particular solution `yp` comes from
`ExpPolynomials.particular` and is checked as in `CAS.Command.DSolveOrder`. The kernel decides
the certificate: `LinearODE.Enclosures.check` (sign changes, the bounds for the Newton
contraction, disjointness and the count), a Bézout identity `U ∏ ρᵏ + V R = 1` that separates
the enclosed roots from the exact ones, and the product of the exact factors and `R`
(`CAS.Polynomial.coeffMul`), which must give the monic coefficients. From these
`LinearODE.nodup_combined` and `LinearODE.charC_combined` give distinct roots and the
characteristic polynomial, and `LinearODE.general_iff_rr` gives the theorem; see
`CAS/Calculus/LinearODERoots.lean`.
-/

public meta section

namespace CAS.Command.DSolveRoot

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.RootSplit
open CAS.Command.ExpPolynomials
open CAS.Command.DSolveOrder
open CAS.Command.Algebra (Dense)
open CAS.Verified.Expr
open CAS.LinearODE (CharRoot Enclosures)

/-! ## The command -/

/-- Run `#cas [dsolve y x] equation` when some characteristic roots are known only by
enclosures; `roots` is the split of the characteristic polynomial by `RootSplit.rootsHere`. -/
def logRoot (ref : Syntax) (y x : TSyntax `ident) (input : Syntax) (order : Nat) {N : Nat}
    (E : Verified.Expr (Fin N)) (coefficients : Array ℚ) (roots : RootSplit.Roots) :
    CommandElabM Unit := do
  let yName := y.getId
  let xName := x.getId
  let n := order
  let top := coefficients.getD n 1
  let monic := coefficients.map (· / top)
  let F0 : Verified.Expr (Fin 1) := E.mapVars fun i ↦
    if i.val = 0 then (.var 0 : Verified.Expr (Fin 1)) else .nat 0
  let F : Verified.Expr (Fin 1) := .neg F0
  let some forcing := toExpPoly F
    | throwErrorAt input "dsolve: the right side is not a sum of terms x ^ k e ^ (a x) \
        cos (b x) and x ^ k e ^ (a x) sin (b x) with rational a, b"
  let some Y := particular monic (epScale (GaussianRat.ofRat (1 / top)) forcing)
    | throwErrorAt input "dsolve: no particular solution was found"
  unless conditionFree Y do throwErrorAt input "dsolve: unexpected particular solution"
  let rs := roots.split.exact
  let D := roots.D
  let yT : TSyntax `term := ⟨y.raw⟩
  let xT : TSyntax `term := ⟨x.raw⟩
  let topT ← real top
  let proof ← liftTermElabM do
    let quote (source : Verified.Expr (Fin 1)) : TermElabM (TSyntax `term) := do
      exprToSyntax (← quoteVerifiedExpr source)
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let FT ← quote F
    let YT ← quote Y
    let t ← roots.terms
    let RSq := t.rs
    let RT := t.R
    let DT := t.D
    let RS := t.all
    let A := t.a
    let UT := t.U
    let VT := t.V
    let dT := t.d
    let hv := t.hv
    let hsep := t.hsep
    let hpos := t.hpos
    let hD := t.hD
    let hA := t.hA
    let hb := t.hb
    let hlen := t.hlen
    let hcf ← certified (← `(Verified.Expr.conditionFree $YT = true))
    let env ← envSyntax xT yT n
    let equation ← `(∀ $x:ident, Verified.Expr.eval $env $ET = 0)
    let sumSimp ← `(tactic| simp only [LinearODE.rLop, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ,
      iteratedDeriv_zero, iteratedDeriv_one])
    let evalSimp ← `(tactic| simp only [Verified.Expr.univariateEval,
      Verified.Expr.euclideanSingle_eq_const, Verified.Expr.eval, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_ofNat, Int.cast_neg,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_zero])
    let bridgeStatement ← `(∀ $y:ident : ℝ → ℝ, ($equation) ↔ ∀ $x:ident,
      LinearODE.rLop $dT (fun k ↦ ((($A : List ℚ).getD k 0 : ℚ) : ℝ)) $yT $xT =
        Verified.Expr.univariateEval $FT $xT / $topT)
    let bridgeProof ← `(by
      intro $y:ident
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
    let partStatement ← `(∀ $x:ident, LinearODE.rLop $dT
      (fun k ↦ ((($A : List ℚ).getD k 0 : ℚ) : ℝ)) (Verified.Expr.univariateEval $YT) $xT =
        Verified.Expr.univariateEval $FT $xT / $topT)
    let partProof ← `(by
      intro $x:ident
      simp only [LinearODE.rLop, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        List.getD_cons_zero, List.getD_cons_succ, LinearODE.iteratedDeriv_univariateEval $hcf]
      simp only [Verified.Expr.iteratedDiff, Verified.Expr.diff, ↓reduceIte]
      $evalSimp:tactic
      push_cast
      ring_nf)
    let part ← exprToSyntax (← elabCheckedProof "dsolve" partStatement partProof)
    -- The basis.
    let mut φs : Array (TSyntax `term) := #[]
    for (ρ, k) in rs do
      for j in [0:k] do
        φs := φs ++ (← funsSyntax x ρ j)
    for (lo, hi) in D.reals do
      let r ← `(AlgRoot.real $RT $(← boundQ lo) $(← boundQ hi))
      φs := φs.push (← `(fun $x:ident : ℝ ↦ $x ^ 0 * Real.exp ($r * $x)))
    for (u, v, ρ, _) in D.discs do
      let z ← `(AlgRoot.complex $RT $(← boundQ u) $(← boundQ v) $(← boundQ ρ))
      φs := φs.push (← `(fun $x:ident : ℝ ↦ $x ^ 0 * Real.exp (($z).re * $x) *
        Real.cos (($z).im * $x)))
      φs := φs.push (← `(fun $x:ident : ℝ ↦ $x ^ 0 * Real.exp (($z).re * $x) *
        Real.sin (($z).im * $x)))
    let (enclosuresT, enclosureProofs) ← enclosureParts roots.R D RT
    let cIdents : Array (TSyntax `ident) := (Array.range n).map fun i ↦
      mkIdent (Name.mkSimple s!"c{(Nat.toSubscriptString (i + 1))}")
    let mut family : TSyntax `term ← `(Verified.Expr.univariateEval $YT $xT)
    for (φ, c) in φs.zip cIdents do
      family ← `($family + $c * $φ $xT)
    let mut exists_ : TSyntax `term ← `(∀ $x:ident, $yT $xT = $family)
    for c in cIdents.reverse do
      exists_ ← `(∃ $c:ident : ℝ, $exists_)
    let general ← `(∀ $y:ident : ℝ → ℝ, $(← regularity yT n) → (($equation) ↔ $exists_))
    let statement ← enclosuresT.foldrM (fun e acc ↦ `($e ∧ $acc)) general
    let hbasis ← `((show LinearODE.rrBasis $RS = $(← listSyntax φs) by rfl))
    let mut conv : TSyntax `term ← `(forall_congr' fun $x:ident ↦
      ⟨fun h ↦ by linear_combination h, fun h ↦ by linear_combination h⟩)
    for c in cIdents.reverse do
      conv ← `(exists_congr fun $c:ident ↦ $conv)
    let hnd ← `(LinearODE.nodup_combined $RSq $hv $hsep $hpos $RT $DT $hD $UT $VT $hb)
    let hc ← `(LinearODE.charC_combined $RSq $hv $RT $DT $hD $A $hA)
    let hn ← `((LinearODE.length_rrList_combined $RSq $RT $DT $hD).trans $hlen)
    let body ← `(fun $y:ident hy ↦ by
      rw [$bridge $yT, LinearODE.general_iff_rr $RS $hnd $A $hc $hn
        (Verified.Expr.contDiff_of_conditionFree $hcf _) $part
        $(← regularityProof (← `(hy)) n), $hbasis:term]
      simp only [LinearODE.mem_span_cons_iff, LinearODE.mem_span_nil_iff]
      exact $conv)
    let proofT ← `(⟨$enclosureProofs,*, $body⟩)
    let proof ← elabCheckedProof "dsolve" statement proofT
    let cleaned ← Digits.cleanProof proof orderCleanLemmas
      [``Verified.Expr.univariateEval, ``LinearODE.CharRoot.width] (simprocs := true)
    let cleaned ← evaluateNumerals cleaned
    let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``zero_add, ``add_zero,
      ``sub_zero, ``zero_mul, ``mul_zero, ``neg_mul, ``Real.exp_zero, ``zero_sub, ``neg_zero]
      (simprocs := true)
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let withLets ← letRoots named
    let cleaned ← mkExpectedTypeHint cleaned withLets
    CAS.Tactic.Explanation.kernelCheckedProof "dsolve" withLets cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The roots of the characteristic factor without closed form, by certified \
          enclosures, and the general solution" proof]
  let answer ← liftTermElabM do
    let type ← inferType proof
    lambdaLetTelescope type fun _ body ↦ do
      let some rhs ← solutionRhs (lastConjunct body) | pure "see the statement"
      pure s!"{yName}({xName}) = {rhs}"
  let rText := polyString roots.R "r"
  let realText := (D.reals.zipIdx.map fun ((lo, hi), i) ↦
    s!"r{Nat.toSubscriptString (i + 1)} ∈ ({decimal lo}, {decimal hi})")
  let discText := (D.discs.zipIdx.map fun ((u, v, ρ, _), i) ↦
    s!"z{Nat.toSubscriptString (i + 1)} = α ± iβ, α ∈ [{decimal (u - ρ)}, {decimal (u + ρ)}], \
      β ∈ [{decimal (v - ρ)}, {decimal (v + ρ)}]")
  let surdText (c : ℚ) (m : ℚ) : String :=
    if m = 1 then s!"{c}" else if c = 1 then s!"√{m}" else s!"{c}√{m}"
  let pairText (α : ℚ) (w : String) (i : String) : String :=
    let wi := if w == "1" && i != "" then "i" else w ++ i
    if α = 0 then s!"±{wi}" else s!"{α} ± {wi}"
  let closedText := rs.map fun (ρ, k) ↦ (match ρ with
    | .real r => s!"{r}"
    | .realPair α c m => pairText α (surdText c m) ""
    | .pair α c m => pairText α (surdText c m) " i") ++
      (if k > 1 then s!" (multiplicity {k})" else "")
  let caseText := s!"order {n}, " ++
    (if closedText.isEmpty then "" else
      "characteristic roots: " ++ ", ".intercalate closedText ++ " and ") ++
    s!"the roots of {rText} = 0: " ++ ", ".intercalate (realText ++ discText)
  logReport ref {
    domain := s!"{xName} ∈ ℝ"
    input := surfaceText input
    inputType := s!"linear equation of order {n} with constant coefficients"
    output := answer
    outputType := caseText
  } #[report]

end CAS.Command.DSolveRoot
