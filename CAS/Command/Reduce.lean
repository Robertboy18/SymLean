/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Roots
public import CAS.Command.Solving
public import CAS.Polynomial.RealRoot.SignReduce
public import CAS.Polynomial.RealRoot.Solve
public meta import CAS.Polynomial.RealRoot.SignReduce
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Polynomial and rational inequalities: `#cas [reduce x]`

`#cas [reduce x] (p < q)` for polynomials `p`, `q` with rational coefficients, of degree two or
more (or an equation of degree three or more), gives the exact real solution set as a union of
intervals whose endpoints are the real roots of `p - q`. Rational roots are endpoints themselves;
an irrational root appears as `ρ j`, a real number located in a rational interval of width
`10 ^ (-20)` and characterized as the only root there. A quotient `p / q` on the left of `< 0`,
`≤ 0`, `> 0`, `≥ 0` or `= 0` is reduced through the product `p q`, which has the same sign with
Lean's division by zero.

The theorem is `∃ ρ, (ρ j ∈ …) ∧ … ∧ ∀ x, (p x < q x ↔ …)` from `of_reduceCheck`, with the
rational roots written as rationals and `∃ ρ` dropped when every root is rational. Affine
relations and equations of degree at most two stay with the `reduce` command of
`CAS.Command.Solving`.

`#cas [solve x] (p = q)` of degree three or more states the real solutions exactly, as
`x = r₁ ∨ ⋯ ∨ x = rₖ`, from `solve_of_solveCheck`. A rational root is written as a rational and
an irrational one as `AlgRoot.real a lo hi`, the only root of the polynomial `a` in the rational
interval `(lo, hi)` of width `10 ^ (-8)`, so that the polynomial and the interval name the root
exactly; the theorem also states the bounds `lo < AlgRoot.real a lo hi < hi`. Equations of
degree at most two stay with the `solve` command of `CAS.Command.Solving`, which writes their
roots with square roots.

## Implementation notes

The roots come from `RootIsolation.generate` of `CAS/Command/RootIsolation.lean`, which proposes
a `RootListCertificate` in compiled code; `realRootCheck` of
`CAS/Polynomial/RealRoot/RootList.lean` checks it by multiplying out its identities rather than
recomputing them. Between consecutive roots we cut at a rational that is not a root (`cutsOf`,
`RootIsolation.nonRootNear`). `reduceCheck` of `CAS/Polynomial/RealRoot/SignReduce.lean` checks
the certificate, the cuts and the signs of the polynomial at the cuts, all in one kernel
evaluation (`CAS.CEGA.Elaboration.decideClosedCertificate`), and `of_reduceCheck` gives the
solution set, since the polynomial keeps one sign between consecutive roots. For `[solve x]`,
`solveCheck` of `CAS/Polynomial/RealRoot/Solve.lean` checks the certificate, the coefficient list
`a` of its covered polynomial and a sign change of `a` across each interval, so that
`AlgRoot.real a lo hi`, a choice by `Classical.epsilon` (`CAS/Polynomial/CoefficientEval.lean`),
is a root in `(lo, hi)`.
-/

public meta section

namespace CAS.Command.Reduce

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Polynomial
open CAS.Polynomial.RealRoot
open CAS.Command.SpecialFunctions

/-- The relations. -/
inductive Relation where
  | lt | le | gt | ge | eq | ne
  deriving BEq

/-- Read `lhs rel rhs`. -/
partial def parseRelation (input : Syntax) : CommandElabM (Relation × Syntax × Syntax) := do
  match unparen input with
  | `($l:term < $r:term) => pure (.lt, l, r)
  | `($l:term ≤ $r:term) => pure (.le, l, r)
  | `($l:term > $r:term) => pure (.gt, l, r)
  | `($l:term ≥ $r:term) => pure (.ge, l, r)
  | `($l:term = $r:term) => pure (.eq, l, r)
  | `($l:term ≠ $r:term) => pure (.ne, l, r)
  | _ => throwUnsupportedSyntax

/-- The polynomial degree of a one-variable expression, if it is a polynomial. -/
def degree? (expr : Verified.Expr (Fin 1)) : Option Nat := do
  let p ← Verified.Expr.Alg.mvPolyOf? expr
  let trimmed := ((Sparse.coeffs p).reverse.dropWhile (· == 0)).reverse
  return trimmed.length - 1

/-- Cuts separating the root locations `locs` of `p`, which are sorted and disjoint and hold every
real root: an integer below the first location, between two locations the upper end of the
first when it is not a root and lies below the next, and otherwise a nonroot strictly between
them, and an integer above the last location; `[0]` when there are no roots. -/
def cutsOf (p : Sparse.Univariate) (locs : List RootLoc) : List ℚ := Id.run do
  let some first := locs.head? | return [0]
  let some last := locs.getLast? | return [0]
  let mut cuts : List ℚ := [((first.lower.floor : ℤ) : ℚ) - 1]
  for j in [1:locs.length] do
    let previous := locs.getD (j - 1) default
    let next := locs.getD j default
    let cut :=
      if Sparse.evalRat p previous.upper != 0 && previous.upper ≤ next.lower then previous.upper
      else RootIsolation.nonRootNear p previous.upper next.lower
    cuts := cuts ++ [cut]
  return cuts ++ [((last.upper.ceil : ℤ) : ℚ) + 1]

/-- The data of `reduceCheck` for a polynomial: the root-list certificate, the root locations,
the cuts and the signs. -/
structure RootData where
  /-- The root-list certificate of the polynomial, from `RootIsolation.generate`. -/
  cert : RootListCertificate
  /-- The real roots in increasing order, as rational points or isolating intervals. -/
  locs : List RootLoc
  /-- Rationals separating consecutive roots, with one below the first root and one above the
  last; `[0]` without roots. -/
  cuts : List ℚ
  /-- Whether the polynomial is positive at each cut. -/
  signs : List Bool

/-- Isolate the real roots of a nonzero polynomial and choose the cuts between them. The points
of `marks` that are not roots stay outside the root intervals. -/
def rootData (poly : Sparse.Univariate) (marks : List ℚ := []) : Except String RootData := do
  let (cert, locs) ← RootIsolation.generate (Sparse.coeffs poly) 20 marks
  let cuts := cutsOf poly locs
  return { cert, locs, cuts, signs := cuts.map fun c ↦ decide (0 < Sparse.evalRat poly c) }

/-- The root locations as a Lean list, with interval endpoints written over `10 ^ digits`. -/
def quoteLocs (locs : List RootLoc) (digits : Nat := 20) : MetaM Lean.Expr := do
  mkListLit (mkConst ``RootLoc) (← locs.mapM fun l ↦ match l with
    | .interval lo hi => do
        pure (mkApp2 (mkConst ``RootLoc.interval) (← quoteDecimal digits lo)
          (← quoteDecimal digits hi))
    | .exact q => do pure (mkApp (mkConst ``RootLoc.exact) (← quoteRat q)))

/-- `theoremName expr cert locs cuts signs h`, with `h : reduceCheck … = true` evaluated by the
kernel. -/
def applyChecked (theoremName : Name) (expr : Verified.Expr (Fin 1)) (data : RootData) :
    MetaM Lean.Expr := do
  let locTerm ← quoteLocs data.locs
  let cutsTerm ← mkListLit (mkConst ``Rat) (← data.cuts.mapM fun c ↦ quoteRat c)
  let signsTerm ← mkListLit (mkConst ``Bool) (data.signs.map toExpr)
  let partialProof ← mkAppM theoremName
    #[← quoteVerifiedExpr expr, ← Roots.quoteCertificate 20 data.cert, locTerm, cutsTerm,
      signsTerm]
  let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
    | throwError "reduce: unexpected certificate theorem shape"
  let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
  return mkApp partialProof check

/-- Run `#cas [reduce x] relation` for a polynomial or rational relation. -/
def logReduce (ref : Syntax) (coordinate : TSyntax `ident) (input : Syntax) :
    CommandElabM Unit := do
  let (relation, lhs, rhs) ← parseRelation input
  let left : TSyntax `term := ⟨lhs⟩
  let right : TSyntax `term := ⟨rhs⟩
  let difference ← if (unparen rhs).isNatLit? == some 0 then pure left
    else `($left - $right)
  let reified ← try parseExact difference [coordinate.getId] catch _ => throwUnsupportedSyntax
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwUnsupportedSyntax
  -- A quotient is reduced through the product of numerator and denominator.
  let (polyExpr, quotient) : Verified.Expr (Fin 1) × Bool :=
    match expr with
    | .div num den =>
        if (rhs.isNatLit? == some 0 || (unparen rhs).isNatLit? == some 0) &&
            (degree? num).isSome && (degree? den).isSome then (.mul num den, true)
        else (expr, false)
    | _ => (expr, false)
  let some d := degree? polyExpr | throwUnsupportedSyntax
  if !quotient && (d ≤ 1 || (relation == .eq && d ≤ 2)) then throwUnsupportedSyntax
  let some poly := Verified.Expr.Alg.mvPolyOf? polyExpr | throwUnsupportedSyntax
  let data ← match rootData poly with
    | .ok data => pure data
    | .error message => throwErrorAt input "reduce: {message}"
  let locs := data.locs
  let cuts := data.cuts
  let signs := data.signs
  let theoremName := match relation with
    | .gt => ``of_reduceCheck_pos
    | .lt => ``of_reduceCheck_neg
    | .ge => ``of_reduceCheck_nonneg
    | .le => ``of_reduceCheck_nonpos
    | .eq => ``of_reduceCheck_zero
    | .ne => ``of_reduceCheck_ne
  let proof ← liftTermElabM do
    let proof ← applyChecked theoremName polyExpr data
    Digits.cleanProof proof (ratCastLemmas ++ [``Matrix.cons_val_zero, ``Matrix.cons_val_fin_one,
      ``Rat.cast_pow, ``sub_pos, ``sub_neg, ``sub_nonneg, ``sub_nonpos, ``sub_eq_zero,
      ``ne_eq, ``true_and, ``Bool.false_eq_true, ``false_and, ``false_or, ``or_false,
      ``true_or, ``or_true, ``and_true, ``Nat.zero_sub, ``Nat.add_sub_cancel, ``Nat.sub_self,
      ``Nat.succ_sub_one, ``eq_self_iff_true, ``List.length_cons, ``List.length_nil,
      ``not_or, ``ne_eq, ``List.getD_cons_zero, ``List.getD_cons_succ, ``exists_const])
      [``BoundsAll, ``GapsFormula, ``Gap, ``RootsFormula, ``RootLoc.Bounds, ``rootVal,
        ``RootLoc.value] (simprocs := true)
      (reversed := if quotient then [``div_pos_iff_mul_pos, ``div_neg_iff_mul_neg,
        ``div_nonneg_iff_mul_nonneg, ``div_nonpos_iff_mul_nonpos, ``div_eq_zero_iff_mul_eq_zero]
        else [])
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "Solution set for every real value" proof]
  -- Rendering of the solution set: consecutive included gaps and roots merge into intervals.
  let name := renderName coordinate.getId
  let k := locs.length
  let rootName (j : Nat) : String :=
    match locs.getD j default with
    | .exact q => toString q
    | .interval _ _ => s!"ρ{j}"
  let want : Option Bool := match relation with
    | .gt | .ge => some true
    | .lt | .le => some false
    | _ => none
  let includeRoots := relation == .ge || relation == .le || relation == .eq
  -- Positions 0 … 2k: gap j at 2j, root j at 2j + 1.
  let included (position : Nat) : Bool :=
    if position % 2 = 0 then
      match want with
      | some w => signs.getD (position / 2) false == w
      | none => relation == .ne
    else includeRoots
  let mut pieces : Array String := #[]
  let mut start : Option Nat := none
  for position in [0:2 * k + 2] do
    let inside := position ≤ 2 * k && included position
    match start, inside with
    | none, true => start := some position
    | some first, false =>
        let last := position - 1
        let lower := if first = 0 then none
          else if first % 2 = 0 then some (s!"{rootName (first / 2 - 1)} <")
          else some (s!"{rootName (first / 2)} ≤")
        let upper := if last = 2 * k then none
          else if last % 2 = 0 then some (s!"< {rootName (last / 2)}")
          else some (s!"≤ {rootName (last / 2)}")
        let piece := match lower, upper with
          | none, none => "True"
          | some l, none => s!"{l} {name}"
          | none, some u => s!"{name} {u}"
          | some l, some u =>
              if first = last && first % 2 = 1 then s!"{name} = {rootName (first / 2)}"
              else s!"{l} {name} {u}"
        pieces := pieces.push piece
        start := none
    | _, _ => pure ()
  let irrational := (List.range k).filterMap fun j ↦
    match locs.getD j default with
    | .interval lo hi => some s!"ρ{j} = {renderRoot 20 (lo, hi)}…"
    | .exact _ => none
  let body := if pieces.isEmpty then "False" else " ∨ ".intercalate pieces.toList
  let output := if irrational.isEmpty then body
    else body ++ ", where " ++ ", ".intercalate irrational
  logReport ref {
    domain := s!"{name} ∈ ℝ"
    input := surfaceText input
    inputType := if quotient then "rational relation" else "polynomial relation"
    output
    outputType := "equivalent condition on the real roots"
  } #[
    computationNode "Certified roots" #[
      m!"{countText k "real root"} of the {if quotient then "product of numerator and denominator"
        else "polynomial"}, {countText data.cert.cells.length "cell"}; cuts {cuts}; signs \
        {signs}"],
    report]

/-- The number of decimals of the root intervals of `#cas [solve x]`. -/
def solveDigits : Nat := 8

/-- An interval endpoint as a decimal with `digits` places when it has at most that many, and as
a fraction otherwise. -/
def endpointText (digits : Nat) (q : ℚ) : String :=
  let m := q * 10 ^ digits
  if q.den = 1 then toString q
  else if m.den = 1 then Digits.renderSigned m.num digits
  else toString q

/-- Run `#cas [solve x] (p = q)` for a polynomial equation of degree three or more: the complete
list of real solutions, exact, from `solve_of_solveCheck`. Lower degrees and other relations go
to the `solve` command of `CAS.Command.Solving`. -/
def logSolvePolynomial (ref : Syntax) (coordinate : TSyntax `ident) (input : Syntax) :
    CommandElabM Unit := do
  let (relation, lhs, rhs) ← parseRelation input
  unless relation == .eq do throwUnsupportedSyntax
  let left : TSyntax `term := ⟨lhs⟩
  let right : TSyntax `term := ⟨rhs⟩
  let zeroRight := (unparen rhs).isNatLit? == some 0
  let difference ← if zeroRight then pure left else `($left - $right)
  let reified ← try parseExact difference [coordinate.getId] catch _ => throwUnsupportedSyntax
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwUnsupportedSyntax
  let some d := degree? expr | throwUnsupportedSyntax
  if d ≤ 2 then throwUnsupportedSyntax
  let some poly := Verified.Expr.Alg.mvPolyOf? expr | throwUnsupportedSyntax
  let (cert, locs) ← match RootIsolation.generate (Sparse.coeffs poly) solveDigits with
    | .ok result => pure result
    | .error message => throwErrorAt input "solve: {message}"
  let a := Sparse.coeffs cert.covered
  let report ← liftTermElabM do
    let coefficients : List Lean.Expr ← (a.mapM quoteRat : MetaM (List Lean.Expr))
    let partialProof ← mkAppOptM ``solve_of_solveCheck
      #[some (← quoteVerifiedExpr expr), some (← Roots.quoteCertificate solveDigits cert),
        some (← quoteLocs locs solveDigits), some (← mkListLit (mkConst ``Rat) coefficients)]
    let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
      | throwError "solve: unexpected certificate theorem shape"
    let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
    let proof ← Digits.cleanProof (mkApp partialProof check)
      (ratCastLemmas ++ [``List.forall_mem_cons, ``List.not_mem_nil, ``List.mem_cons,
        ``List.mem_nil_iff, ``exists_eq_or_imp, ``exists_eq_left, ``or_false,
        ``forall_eq_or_imp, ``forall_eq, ``IsEmpty.forall_iff, ``forall_const, ``and_true,
        ``true_and, ``false_and, ``exists_false, ``Rat.cast_pow, ``Matrix.cons_val_zero,
        ``Matrix.cons_val_fin_one] ++ (if zeroRight then [] else [``sub_eq_zero]))
      [``RootLoc.Bounds, ``RootLoc.real]
    evidenceReportMessage #[← proofStep "Complete list of real solutions"
      ``solve_of_solveCheck proof]
  let name := renderName coordinate.getId
  let polynomial := (renderPolynomial a).replace "x" name
  let rootName (j : Nat) : String :=
    match locs.getD j default with
    | .exact q => toString q
    | .interval _ _ => s!"ρ{j}"
  let output := if locs.isEmpty then "False"
    else " ∨ ".intercalate ((List.range locs.length).map fun j ↦ s!"{name} = {rootName j}")
  let algebraic := (List.range locs.length).filterMap fun j ↦
    match locs.getD j default with
    | .interval lo hi => some (s!"ρ{j}", s!"the root of {polynomial} in \
        ({endpointText solveDigits lo}, {endpointText solveDigits hi})")
    | .exact _ => none
  let guarantee := if algebraic.isEmpty then
      "Guarantee: the input and output are equivalent for every real value"
    else s!"Guarantee: the input and output are equivalent for every real value; each ρj is the \
      algebraic number AlgRoot.real a lo hi, the only root of {polynomial} in the interval (lo, hi)"
  logReport ref {
    domain := s!"{name} ∈ ℝ"
    input := surfaceText input
    inputType := "real relation"
    output
    outputType := "equivalent real solution predicate"
    furtherResults := algebraic.toArray
  } #[
    computationNode "Certified roots" #[m!"{Roots.isolationText cert}", m!"{guarantee}"],
    report]

end CAS.Command.Reduce

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [reduce $x:ident] $input:term) => Reduce.logReduce input x input
  | `(#cas [solve $x:ident] $input:term) => Reduce.logSolvePolynomial input x input

end CAS.Command
