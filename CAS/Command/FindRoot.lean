/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.FindRoot
public import CAS.Command.Algebra.Basic
public import CAS.Command.NIntegrate
public meta import CAS.Calculus.FindRoot

/-!
# Certified roots of equations: `#cas [findRoot x in [a, b]]`

`#cas [findRoot x in [a, b]] f` finds a root of `f` in `[a, b]` and prints it as a decimal `m`
with `d` places (`d = 10`; `(digits := d)` changes it, up to 30). The theorem is exactly that
statement: the interval `[m - 10 ^ (-d), m + 10 ^ (-d)]`, clipped to the sign-change bracket
inside `[a, b]`, contains exactly one root,

`∃! x, x ∈ Set.Icc lo hi ∧ f x = 0`.

An equation `g = h` stands for `g - h = 0`, and the statement is written `g x = h x`. A root
where the derivative vanishes, two roots closer than the tolerance, or a sign change across a
pole is refused rather than reported. Logarithms and square roots are evaluated only at positive
arguments, so a bracket that reaches `x ≤ 0` inside them is refused even where Mathlib's total
functions are defined.

## Implementation notes

The expression is sampled at 65 points of `[a, b]` by FloatLib-backed interval evaluation
(`DigitsEval.eval`, `CAS/Continuum/IntervalEval/Digits.lean`); the first sign change is narrowed
by bisection in compiled code to a tenth of the tolerance, or refused when interval evaluation
stops deciding the sign. None of this is trusted. The kernel then checks
`Verified.Expr.rootCheck` on `[lo, hi]` (strict opposite signs at its endpoints and a derivative
enclosure of one sign on all of it), and the CEGA domain checker `validIteratesOnIcc?`
(`CAS/Continuum/IntervalEval/Validity.lean`) proves the expression valid there;
`existsUnique_root_of_rootCheck` (`CAS/Calculus/FindRoot.lean`) turns both into the statement,
by the intermediate value theorem and strict monotonicity.
-/

public meta section

namespace CAS.Command.FindRoot

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Continuum

/-- The sign of `expr` at `q` by interval evaluation: `some true` when positive, `some false`
when negative, `none` when the enclosure contains zero or evaluation fails. -/
def sign? (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1)) (q : ℚ) : Option Bool := do
  let I ← Verified.Expr.valueOn p expr (.const q)
  if 0 < I.lo then some true else if I.hi < 0 then some false else none

/-- The first pair of consecutive points among `a + k (b - a) / 64` at which `expr` has known
opposite signs, with the sign at the left point. -/
def firstSignChange? (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1)) (a b : ℚ) :
    Option (ℚ × ℚ × Bool) := Id.run do
  let n : Nat := 64
  let point (k : Nat) : ℚ := a + (b - a) * k / n
  let mut previous : Option (ℚ × Bool) := none
  for k in [0:n + 1] do
    match sign? p expr (point k) with
    | some s =>
        if let some (q, s') := previous then
          if s != s' then return some (q, point k, s')
        previous := some (point k, s)
    | none => pure ()
  return none

/-- Narrow `[a, b]`, where `expr` has the sign `sa` at `a` and the opposite sign at `b`, toward
width `width`, choosing points with a known sign near the midpoint. The result may be wider
when no nearby point has a known sign; the caller checks the width. -/
def bisect (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1)) (a b : ℚ) (sa : Bool)
    (width : ℚ) : ℚ × ℚ := Id.run do
  let mut lo := a
  let mut hi := b
  -- Enough halvings for the ratio of the widths, with a margin for the off-center points.
  let halvings := Nat.log2 (⌈(b - a) / width⌉.toNat + 1) + 1
  for _ in [0:min (2 * halvings + 60) 20000] do
    if hi - lo ≤ width then break
    let candidates := [1 / 2, 3 / 8, 5 / 8, 1 / 4, 3 / 4].map fun t : ℚ ↦ lo + (hi - lo) * t
    let mut moved := false
    for m in candidates do
      if moved then break
      match sign? p expr m with
      | some s =>
          if s == sa then lo := m else hi := m
          moved := true
      | none => pure ()
    unless moved do break
  return (lo, hi)

/-- A rational number in decimal notation with `digits` places, rounded to nearest. -/
def decimalText (digits : Nat) (q : ℚ) : String :=
  let scale : ℚ := 10 ^ digits
  let m : ℤ := ⌊q * scale + 1 / 2⌋
  let body := Digits.renderDecimal m.natAbs digits
  if m < 0 then "-" ++ body else body

/-- The decimal or rational term of `q` with `digits` places. -/
def quoteEndpoint (digits : Nat) (q : ℚ) : MetaM Lean.Expr :=
  SpecialFunctions.quoteDecimal digits q

/-- The proof of `∃! x, x ∈ Set.Icc lo hi ∧ expr.univariateEval x = 0`, from the CEGA domain
checker and the kernel-checked `rootCheck`, with `lo` and `hi` given as terms of `ℚ`. -/
def rootCertificate (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1))
    (loTerm hiTerm : Lean.Expr) (lo hi : ℚ) : MetaM Lean.Expr := do
  let quoted ← quoteVerifiedExpr expr
  let real (q : Lean.Expr) := mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some q]
  let order ← mkAppM ``LT.lt #[← real loTerm, ← real hiTerm]
  let orderProof ← Term.TermElabM.run' do
    let proof ← Term.elabTerm (← `(by norm_num)) (some order)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  let query ← mkAppM ``CAS.Continuum.RationalInterval.validIteratesOnIcc?
    #[quoted, toExpr (1 : Nat), loTerm, hiTerm, orderProof]
  let result ← try
      CAS.Tactic.KernelReadBack.kernelWhnf query "findRoot domain checking"
    catch _ => throwError "findRoot: the domain checker could not prove the expression valid \
      on [{lo}, {hi}]"
  unless result.isAppOfArity ``Option.some 2 do
    throwError "findRoot: the expression is not analytically valid on [{lo}, {hi}] (a division \
      by zero, a logarithm or square root at a nonpositive argument)"
  let validity ← mkAppM ``CAS.CertificateRoute.cert #[result.getAppArgs[1]!]
  let partialProof ← mkAppOptM ``Verified.Expr.existsUnique_root_of_rootCheck
    #[some (CAS.CEGA.Integration.quotePrecision p), some quoted, some loTerm, some hiTerm,
      some validity]
  let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
    | throwError "findRoot: unexpected certificate theorem shape"
  return mkApp partialProof (← CAS.CEGA.Elaboration.decideClosedCertificate checkType false)

/-- Run `#cas [findRoot x in [a, b]] f`. -/
def logFindRoot (ref : Syntax) (digits : Nat) (coordinate : TSyntax `ident) (aStx bStx : Syntax)
    (input : Syntax) : CommandElabM Unit := do
  if digits = 0 || digits > 30 then throwErrorAt ref "findRoot accepts between 1 and 30 digits"
  let a ← SpecialFunctions.parseRational "findRoot" aStx
  let b ← SpecialFunctions.parseRational "findRoot" bStx
  unless a < b do throwErrorAt ref "findRoot needs rational endpoints a < b"
  let (equation, function) ← match SpecialFunctions.unparen input with
    | `($l:term = $r:term) => pure (true, ← `(($l) - ($r)))
    | _ => pure (false, ⟨input⟩)
  let (reified, expr) ← Series.parseUnivariate coordinate function
  let p := DigitsEval.precisionFor (digits + 10)
  let some (a', b', sa) := firstSignChange? p expr a b
    | throwErrorAt input "findRoot: no sign change of the expression at 65 equally spaced \
        points of [{a}, {b}]; a root of even multiplicity, or two roots closer than the sample \
        spacing, has no certificate here"
  let ε : ℚ := 1 / 10 ^ digits
  let (lo, hi) := bisect p expr a' b' sa (ε / 10)
  unless hi - lo ≤ ε / 10 do
    throwErrorAt input "findRoot: the sign change could not be narrowed below [{lo}, {hi}] \
      (interval evaluation does not decide the sign near the root); ask for fewer digits"
  -- The printed decimal `m` and the interval `[m - ε, m + ε]`, inside the sign-change bracket.
  let m : ℚ := (⌊(lo + hi) / 2 * 10 ^ digits + 1 / 2⌋ : ℚ) / 10 ^ digits
  let lo := max a' (m - ε)
  let hi := min b' (m + ε)
  unless sign? p expr lo == some sa && sign? p expr hi == some !sa do
    throwErrorAt input "findRoot: the signs at the ends of [{lo}, {hi}] around {m} are not \
      decided by interval evaluation"
  let some D := (if h : lo ≤ hi then Verified.Expr.valueOn p (expr.diff 0) (.ofBounds lo hi h)
      else none)
    | throwErrorAt input "findRoot: the derivative cannot be evaluated on [{lo}, {hi}], where \
        the sign changes; the expression may have a singularity there rather than a root"
  unless 0 < D.lo || D.hi < 0 do
    throwErrorAt input "findRoot: the derivative encloses 0 on [{lo}, {hi}]; a multiple root, \
      or roots closer than 10^-{digits}, has no certificate here"
  -- The endpoints are decimals with `digits` places unless clipped to the bracket.
  let places := if (lo * 10 ^ digits).den = 1 && (hi * 10 ^ digits).den = 1 then digits
    else digits + 1
  let endpointText (q : ℚ) : String :=
    if (q * 10 ^ places).den = 1 then decimalText places q else toString q
  let proof ← liftTermElabM do
    let certificate ← rootCertificate p expr (← quoteEndpoint places lo)
      (← quoteEndpoint places hi) lo hi
    Digits.cleanProof certificate
      (Series.seriesCleanLemmas ++ [``Rat.cast_pow] ++ (if equation then [``sub_eq_zero] else []))
      [``Verified.Expr.univariateEval]
  let x := coordinate.getId
  logReport ref {
    domain := s!"{x} ∈ [{a}, {b}]"
    input := if equation then surfaceText input
      else reified.render
    inputType := if equation then "equation in ℝ" else "scalar ℝ"
    output := s!"{x} = {decimalText digits m} ± 10^-{digits}"
    outputType := "certified simple root"
  } #[
    computationNode "Certified root" #[
      m!"Sign change found by interval sampling and bisection (not proof)",
      m!"Unique root in [{endpointText lo}, {endpointText hi}], within 10^-{digits} of \
        {decimalText digits m}: endpoint signs and a derivative of one sign, checked by the \
        kernel"],
    ← liftTermElabM <| Algebra.checkedEvidence "findRoot" "Unique root in the interval"
      (← liftTermElabM (inferType proof)) proof]

end CAS.Command.FindRoot

namespace CAS.Command

open Lean Elab Command

/-- `#cas [findRoot x in [a, b]] f` finds a simple root of `f` in `[a, b]`, prints it with `d`
decimal places, and proves that exactly one root lies within `10 ^ (-d)` of the printed value.

## Theorem
For the printed `x = m ± 10^-d`, the report proves `∃! x, x ∈ Set.Icc lo hi ∧ f x = 0`, where
`[lo, hi]` is `[m - 10 ^ (-d), m + 10 ^ (-d)]` clipped to the bracket of the sign change
(`CAS.Verified.Expr.existsUnique_root_of_rootCheck`). For an equation `g = h` the statement is
`g x = h x`.

## Conditions and limits
`a < b` are closed rational expressions, such as `-1` or `3/2`; a bound is refused when its
evaluation needs a number with more than `10000` digits (`SpecialFunctions.parseRational`). `f` is
an expression or an equation in `x` alone, in the calculator grammar of `#cas [N d]`. `f` is
sampled at 65 equally spaced points of `[a, b]`, and the first sign change from the left is
narrowed by bisection; the kernel checks opposite signs at the ends of `[lo, hi]` and a derivative
enclosure of one sign on it. A root where the derivative vanishes, two roots closer than the
sample spacing and a sign change across a pole are refused. `log` and `sqrt` are evaluated only at
positive arguments, so a bracket that reaches `x ≤ 0` inside them is refused.

## Options
`(digits := d)`: the number of decimal places, 1 to 30, default 10.

## Examples
```lean
#cas [findRoot x in [0, 1]] (cos x = x)
```
```output
Output (certified simple root): x = 0.7390851332 ± 10^-10
```
```lean
#cas (digits := 20) [findRoot x in [0, 2]] (exp x - 3)
```
```output
Output (certified simple root): x = 1.09861228866810969140 ± 10^-20
```
```lean
#cas [findRoot x in [2, 4]] (sin x)
```
```output
Output (certified simple root): x = 3.1415926536 ± 10^-10
```

## In a proof
```lean
theorem findRoot_cos : ∃ x : ℝ, Real.cos x = x ∧ 0.739 < x ∧ x < 0.74 := by
  cas
```
The tactic `cas` proves that a root exists between two rational bounds.

## See also
Mathematica `FindRoot`, SymPy `nsolve`. The modes `solve`, `roots` and `N`. Oracle route:
`#cas [nsolve x in [a, b], oracle := sympy] (lhs = rhs)`, which checks a root in each interval
that the oracle reports.

## Possible issues
```lean
#cas [findRoot x in [-1, 1]] (x^2)
```
```output
findRoot: no sign change of the expression at 65 equally spaced points of [-1, 1]; a root of even
multiplicity, or two roots closer than the sample spacing, has no certificate here
```
A double root does not change sign. Find the root of the derivative, here `2 * x`, or solve a
polynomial exactly with `#cas [roots x]`.
```lean
#cas [findRoot x in [0, 2]] (1 / (x - 1))
```
```output
findRoot: the derivative cannot be evaluated on [9999999999/10000000000, 10000000001/10000000000],
where the sign changes; the expression may have a singularity there rather than a root
```
`1 / (x - 1)` changes sign at its pole `1` and has no root. Choose an interval without poles.
-/
syntax (name := casFindRootCommand)
  "#cas" optConfig "[" &"findRoot" cegaIntervalBinding "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [findRoot $x:ident in [$a:term, $b:term]] $expr:term) => do
      FindRoot.logFindRoot expr (← parseDigitsOption "findRoot" cfg 10) x a b expr

end CAS.Command
