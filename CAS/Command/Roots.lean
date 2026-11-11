/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.FullSimplify
public import CAS.Command.SpecialFunctions
public import CAS.Command.RootIsolation
public import CAS.Polynomial.RealRoot.SignReduce
public meta import CAS.Polynomial.RealRoot.SignReduce
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# All real roots of a polynomial: `#cas [roots x]`

`#cas [roots x] (p = q)` lists every real solution of a polynomial equation with rational
coefficients in one variable, of any degree, and proves the list complete. Rational roots are
reported exactly; the other roots are reported by `d = 20` certified decimals
(`#cas (digits := d) [roots x]` changes the count, up to 60). The reported theorem states that
each decimal interval contains exactly one solution, that each rational is a solution, and that
there are no other real solutions; the same check makes the intervals and rationals pairwise
disjoint, so the reported count is the number of real solutions. An equation whose two sides are
the same polynomial is refused, since every real number solves it.

## Implementation notes

The certificate is found in compiled code by `RootIsolation.generate`
(`CAS/Command/RootIsolation.lean`) and checked by the kernel in one evaluation of
`exprRootCheck`; `of_exprRootCheck` (`CAS/Polynomial/RealRoot/RootList.lean`) turns the check into
the reported theorem. The certificate records the identity `p = c · ∏ (x - rᵢ) · q`, which splits
off the rational roots `rᵢ` with their multiplicities, the square-free radical of `q` when `q` has
repeated factors (`RadicalCertificate`, `CAS/Polynomial/RealRoot/Radical.lean`), a Cauchy bound
`B` of the polynomial left to cover (`CauchyBoundCertificate`,
`CAS/Polynomial/RealRoot/CauchyBound.lean`), and a cover of `[-B, B]` by root-free cells, exact
root cells and refined root cells. The kernel multiplies out the identities and checks each cell
by interval evaluation; it does not recompute a square-free part. No Sturm sequence is involved:
a cell holds one root because the polynomial changes sign at its ends and its derivative has one
sign on it.
-/

public meta section

namespace CAS.Command.Roots

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Polynomial
open CAS.Polynomial.RealRoot
open CAS.Command.SpecialFunctions

/-- The rational intervals as a Lean list, with decimal endpoints written over `10 ^ d`. -/
def quoteIntervals (digits : Nat) (intervals : List (ℚ × ℚ)) : MetaM Lean.Expr := do
  let pairType ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``Rat]
  mkListLit pairType (← intervals.mapM fun (lo, hi) ↦ do
    mkAppM ``Prod.mk #[← quoteDecimal digits lo, ← quoteDecimal digits hi])

/-- The cells as a Lean list. -/
def quoteCells (digits : Nat) (cells : List (ℚ × RootCell)) : MetaM Lean.Expr := do
  let pairType ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``RootCell]
  let quoteDirection : Direction → Lean.Expr
    | .increasing => mkConst ``Direction.increasing
    | .decreasing => mkConst ``Direction.decreasing
  mkListLit pairType (← cells.mapM fun (t, cell) ↦ do
    let cellTerm ← match cell with
      | .free => pure (mkConst ``RootCell.free)
      | .root direction lo hi =>
          pure (mkApp3 (mkConst ``RootCell.root) (quoteDirection direction)
            (← quoteDecimal digits lo) (← quoteDecimal digits hi))
      | .exact direction r =>
          pure (mkApp2 (mkConst ``RootCell.exact) (quoteDirection direction) (← quoteRat r))
    mkAppM ``Prod.mk #[← quoteRat t, cellTerm])

/-- A sparse univariate polynomial as a Lean list of coefficients and exponents. -/
def quoteSparse (p : Sparse.Univariate) : MetaM Lean.Expr := do
  let finOne := mkApp (mkConst ``Fin) (mkNatLit 1)
  let monomialType := Lean.mkForall `i .default finOne (mkConst ``Nat)
  let pairType := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Rat) monomialType
  mkListLit pairType (← p.mapM fun (c, monomial) ↦ do
    return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Rat) monomialType
      (← quoteRat c) (Lean.mkLambda `i .default finOne (mkNatLit (monomial 0))))

/-- A radical certificate as a Lean term. -/
def quoteRadical (c : RadicalCertificate) : MetaM Lean.Expr := do
  return mkAppN (mkConst ``RadicalCertificate.mk)
    #[← quoteSparse c.radical, ← quoteSparse c.originalOverRadical,
      mkApp (mkConst ``Nat.succPNat) (mkNatLit (c.exponent.val - 1)),
      ← quoteSparse c.radicalPowerOverOriginal, ← quoteSparse c.bezoutLeft,
      ← quoteSparse c.bezoutRight]

/-- A Cauchy bound certificate as a Lean term. -/
def quoteBound (c : CauchyBoundCertificate) : MetaM Lean.Expr := do
  return mkApp3 (mkConst ``CauchyBoundCertificate.mk) (← quoteRat c.scale) (mkNatLit c.degree)
    (← quoteSparse c.lower)

/-- A root-list certificate as a Lean term, with the endpoints of the refined root cells written
over `10 ^ digits`. The kernel checks the certificate as given: it multiplies out the identities
and evaluates the cells, without recomputing the radical or the bound. -/
def quoteCertificate (digits : Nat) (cert : RootListCertificate) : MetaM Lean.Expr := do
  let rats (values : List ℚ) : MetaM Lean.Expr := do
    mkListLit (mkConst ``Rat) (← values.mapM quoteRat)
  let radicalType := mkConst ``RadicalCertificate
  let radical ← match cert.radical with
    | none => pure (mkApp (mkConst ``Option.none [Level.zero]) radicalType)
    | some r => do
        pure (mkApp2 (mkConst ``Option.some [Level.zero]) radicalType (← quoteRadical r))
  return mkAppN (mkConst ``RootListCertificate.mk)
    #[← quoteRat cert.content, ← rats cert.roots, ← rats cert.quotient, radical,
      ← quoteBound cert.bound, ← quoteCells digits cert.cells]

/-- The isolation line of a report: the rational roots split off, the polynomial the cells cover
with its degree and Cauchy bound, and the number of cells. -/
def isolationText (cert : RootListCertificate) : String :=
  let rational := cert.roots.eraseDups.length
  let degree := (Sparse.coeffs cert.covered).length - 1
  let deflation := if rational = 0 then "" else s!"{countText rational "rational root"} split off; "
  let factor :=
    if cert.radical.isSome then "square-free radical"
    else if rational = 0 then "square-free polynomial" else "square-free remaining factor"
  let text :=
    if rational > 0 && degree = 0 then s!"{deflation}the remaining factor is constant"
    else s!"{deflation}{factor} of degree {degree}, Cauchy bound {cert.bound.bound}, \
      {countText cert.cells.length "cell"}"
  text.capitalize

private def parseEquation (input : Syntax) : CommandElabM (TSyntax `term) := do
  match unparen input with
  | `($lhs:term = $rhs:term) =>
      if (unparen rhs).isNatLit? == some 0 then pure lhs else `($lhs - $rhs)
  | other => pure ⟨other⟩

/-- Run `#cas [roots x] (p = q)`. -/
def logRoots (ref : Syntax) (digits : Nat) (coordinate : TSyntax `ident) (input : Syntax) :
    CommandElabM Unit := do
  if digits = 0 || digits > 60 then
    throwErrorAt ref "roots accepts between 1 and 60 digits"
  let difference ← parseEquation input
  let reified ← parseExact difference [coordinate.getId]
  unless reified.names.length = 1 do
    throwErrorAt input "roots needs a polynomial in {coordinate.getId} alone"
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "roots needs a polynomial in {coordinate.getId} alone"
  let some poly := Verified.Expr.Alg.mvPolyOf? expr
    | throwErrorAt input "roots supports polynomial equations with rational coefficients"
  if (Sparse.coeffs poly).all (· == 0) then
    throwErrorAt input "the polynomial is zero; every real number is a solution"
  let (cert, locs) ← match RootIsolation.generate (Sparse.coeffs poly) digits with
    | .ok result => pure result
    | .error message => throwErrorAt input "roots: {message}"
  let intervals := rootIntervals cert.cells
  let points := locs.filterMap RootLoc.pointPart
  let report ← liftTermElabM do
    let partialProof ← mkAppOptM ``of_exprRootCheck
      #[some (← quoteVerifiedExpr expr), some (← quoteCertificate digits cert),
        some (← quoteIntervals digits intervals), some (← mkListLit (mkConst ``Rat)
          (← points.mapM fun r ↦ quoteRat r))]
    let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
      | throwError "roots: unexpected certificate theorem shape"
    let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
    let proof ← Digits.cleanProof (mkApp partialProof check)
      (ratCastLemmas ++ [``List.forall_mem_cons, ``List.not_mem_nil, ``List.mem_cons,
        ``List.mem_nil_iff, ``exists_eq_or_imp, ``exists_eq_left, ``or_false,
        ``forall_eq_or_imp, ``forall_eq, ``IsEmpty.forall_iff, ``forall_const, ``and_true,
        ``false_and, ``exists_false, ``Rat.cast_pow, ``Matrix.cons_val_zero,
        ``Matrix.cons_val_fin_one, ``true_and, ``false_or])
    evidenceReportMessage #[← proofStep "Complete list of real solutions"
      ``of_exprRootCheck proof]
  let rendered := points.map toString ++ intervals.map (renderRoot digits)
  let output := if rendered.isEmpty then "no real solutions" else ", ".intercalate rendered
  let count := rendered.length
  let solutions :=
    if count = 0 then "complete list of real solutions"
    else if count = 1 then "the only real solution"
    else s!"all {count} real solutions"
  let decimals :=
    if intervals.isEmpty then ""
    else if count = 1 then s!", by {digits} decimals, truncated"
    else s!"; enclosed ones by {digits} decimals, truncated"
  logReport ref {
    domain := s!"{coordinate.getId} ∈ ℝ"
    input := surfaceText input
    inputType := "polynomial equation"
    output
    outputType := solutions ++ decimals
  } #[
    computationNode "Certified isolation" #[
      m!"{isolationText cert}",
      m!"Guarantee: the listed solutions are distinct, each rational is a solution, each \
        decimal interval contains exactly one solution, and there are no other real solutions"
    ],
    report
  ]

end CAS.Command.Roots

namespace CAS.Command

open Lean Elab Command

/-- `#cas [roots x] (lhs = rhs)` lists every real solution of a polynomial equation in `x`, the
rational ones exactly and the others as truncated decimals, and proves that the list is
complete.

## Theorem
For each solution that is not a printed rational the report gives a rational interval `(l, u)`
of width `10 ^ (-d)` whose end nearer to zero is the printed decimal. It proves the conjunction of
`∃! x, x ∈ Set.Ioo l u ∧ lhs = rhs` for each interval, of `lhs = rhs` at each printed rational,
and of `∀ x : ℝ, lhs = rhs → (x = r₁ ∨ … ∨ x = rₖ) ∨ x ∈ Set.Ioo l₁ u₁ ∨ …`
(`CAS.Polynomial.RealRoot.of_exprRootCheck`).

## Conditions and limits
`lhs` and `rhs` are polynomials with rational coefficients in `x` alone, of any degree, and a
polynomial `p` alone stands for `p = 0`. Each solution is listed once, whatever its multiplicity:
the check that the kernel evaluates also makes the intervals and the rationals pairwise disjoint,
so the count in the report is the number of real solutions. An equation without real solutions
gives "no real solutions".

## Options
`(digits := d)`, from 1 to 60, default 20: the number of decimals of the enclosed solutions.

## Examples
```lean
#cas [roots x] (x^3 - 2*x - 5 = 0)
```
```output
Output (the only real solution, by 20 decimals, truncated): 2.09455148154232659148
```
```lean
#cas [roots x] ((x - 1)^2 * (x + 2) * (x^2 - 2))
```
```output
Output (all 4 real solutions; enclosed ones by 20 decimals, truncated): -2, 1,
-1.41421356237309504880, 1.41421356237309504880
```
```lean
#cas (digits := 40) [roots x] (x^2 = 2)
```
```output
Output (all 2 real solutions; enclosed ones by 40 decimals, truncated):
-1.4142135623730950488016887242096980785696, 1.4142135623730950488016887242096980785696
```

## In a proof
```lean
theorem roots_cubic : ∃ x : ℝ, x ^ 3 - 2 * x - 5 = 0 ∧ 2 < x ∧ x < 3 := by
  cas
```

## See also
Mathematica `NSolve` over the reals and `CountRoots`, SymPy `real_roots`. The modes
`roots z in ℂ`, `solve`, `reduce` and `findRoot`. The tactic `cas` also proves
`Fintype.card (p.rootSet ℝ) = n` for `p : ℚ[X]`.

## Possible issues
```lean
#cas [roots x] (x = x)
```
```output
the polynomial is zero; every real number is a solution
```
An identity has every real number as a solution, so there is no list.
```lean
#cas [roots x] (sin x = 0)
```
```output
roots supports polynomial equations with rational coefficients
```
For other equations, `#cas [findRoot x in [a, b]] (f = g)` certifies one root in an interval.
```lean
#cas (digits := 61) [roots x] (x^2 = 2)
```
```output
roots accepts between 1 and 60 digits
```
Ask for at most 60 decimals.
-/
syntax (name := casRootsCommand) "#cas" optConfig "[" &"roots" ident "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [roots $x:ident] $expr:term) => do
      Roots.logRoots expr (← parseDigitsOption "roots" cfg 20) x expr

end CAS.Command
