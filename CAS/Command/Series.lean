/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Series
public import CAS.Command.FullSimplify
public import CAS.Command.SpecialFunctions
public meta import CAS.Calculus.Series
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Taylor series and limits: `#cas [series x a n]`, `#cas [limit x → a]`

`#cas [series x a n] f` prints the Taylor polynomial of degree `n` of `f` at the rational point
`a` with exact rational coefficients, as Mathematica's `Series[f, {x, a, n}]` does, and proves

`(fun x ↦ f x - ∑ k ≤ n, c_k (x - a) ^ k) =o[𝓝 a] fun x ↦ (x - a) ^ n`.

`#cas [limit x → a] f` computes `lim_{x → a} f x`: for a quotient `g / h` whose denominator
vanishes at `a` it proves `Tendsto (fun x ↦ g x / h x) (𝓝[≠] a) (𝓝 L)`, and otherwise
`Tendsto f (𝓝 a) (𝓝 (f a))`. The point is a closed calculator expression with a rational value,
such as `1/10000`. `CAS/Command/Laurent.lean` and `CAS/Command/Limits.lean` add rules for the
same syntax, for Laurent series and poles, which fall back to the rules here. One-sided limits and
limits at infinity have their own forms, in `CAS/Command/Limits.lean` and
`CAS/Command/AsymptoticLimits.lean`.

## Implementation notes

The coefficients are the symbolic derivatives at `a` evaluated exactly (`exactValue?`), which
requires every transcendental subterm to sit at a point with a rational value, such as
`sin 0` or `log 1`. This search only proposes the list: the kernel decides `seriesCheck` for it
(`CAS.CEGA.Elaboration.decideClosedCertificate`), and `series_of_check` of
`CAS/Calculus/Series.lean` turns the check into the little-o statement, from Mathlib's
`taylor_isLittleO`. The validity of the derivatives at `a` comes from the CEGA domain checker
(`CertifiedEvalRegistry.validIteratesOn?` of `CAS/Continuum/IntervalEval/Validity.lean`, evaluated
by the kernel on the interval `[a, a]`), and the theorems extend it to a neighbourhood of `a`
themselves (`eventually_validIterates`), so a point as close to a singularity as `1/10000` for
`sqrt x` is accepted. The centre is a rational literal such as `1/2`, `-3` or `-1/2`, or a closed
calculator expression with a rational value in parentheses.

For a quotient we find the order `m` of the first nonzero derivative of `h` at `a`, check that the
derivatives of `g` below order `m` vanish, and take the quotient of the `m`-th derivatives. The
kernel decides the same facts in the hypothesis of `tendsto_div_of_check`, which proves the limit
from the two Taylor expansions, the form of L'Hôpital's rule that the series give. Otherwise
`tendsto_of_validIteratesOn` gives continuity at a point of validity. `Digits.cleanProof`
restates each theorem in ordinary notation.
-/

public meta section

namespace CAS.Command.Series

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Verified.Expr

/-- Simplification lemmas that restate univariate evaluation in ordinary notation. -/
def seriesCleanLemmas : List Name :=
  ratCastLemmas ++ [``euclideanSingle_eq_const,
    ``Finset.sum_range_succ, ``Finset.sum_range_zero, ``List.getD_cons_zero,
    ``List.getD_cons_succ, ``zero_add, ``zero_mul, ``mul_one, ``pow_zero, ``pow_one,
    ``sub_zero, ``Rat.cast_ofNat, ``Nat.cast_ofNat, ``Matrix.cons_val_zero,
    ``Matrix.cons_val_fin_one, ``one_mul, ``add_zero, ``div_one]

/-- The exact value of the `k`-th derivative of `expr` at `a`. -/
def derivativeAt (expr : Verified.Expr (Fin 1)) (k : Nat) (a : ℚ) : Option ℚ :=
  exactValue? (fun _ ↦ a) (expr.iteratedDiff (0 : Fin 1) k)

/-- Validity of the derivatives of orders below `n` at the rational point `a`, from the CEGA
domain checker evaluated by the kernel on the interval `[a, a]`. The theorems that use it extend
validity at a point to a neighbourhood (`eventually_validIterates`). -/
def validityAt (quoted : Lean.Expr) (n : Nat) (a : ℚ) : MetaM (Option Lean.Expr) := do
  let aTerm ← quoteRat a
  let precision ← Term.TermElabM.run' do
    let precision ← Term.elabTerm (← `(({} : CAS.Continuum.RationalInterval.Precision))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars precision
  let registry ← mkAppM ``CAS.Continuum.RationalInterval.CertifiedEvalRegistry.rationalIcc
    #[aTerm, aTerm, ← mkAppM ``le_refl #[aTerm], precision]
  let query ← mkAppM ``CAS.Continuum.RationalInterval.CertifiedEvalRegistry.validIteratesOn?
    #[registry, quoted, toExpr n]
  let result ← try
      CAS.Tactic.KernelReadBack.kernelWhnf query "domain checking"
    catch _ => return none
  unless result.isAppOfArity ``Option.some 2 do
    return none
  let onInterval ← mkAppM ``CAS.CertificateRoute.cert #[result.getAppArgs[1]!]
  let point ← mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some aTerm]
  let motive ← withLocalDeclD `s (← mkAppM ``Set #[mkConst ``Real]) fun s ↦ do
    mkLambdaFVars #[s] (← mkAppM ``Verified.Expr.ValidIteratesOn #[quoted, toExpr n, s])
  return some (← mkEqMP (← mkCongrArg motive (← mkAppM ``Set.Icc_self #[point])) onInterval)

/-- `validityAt`, or the error of `operation` that the domain checker did not certify the
`part` of the input (`"numerator"`, `"function"`, ...) at `a`. -/
def requireValidityAt (operation part : String) (quoted : Lean.Expr) (n : Nat) (a : ℚ) :
    MetaM Lean.Expr := do
  if let some proof ← validityAt quoted n a then
    return proof
  let subject : MessageData := if n ≤ 1 then m!"the {part} is" else
    m!"the {part} and its derivatives through order {n - 1} are"
  throwError "{operation}: the domain checker did not certify that {subject} defined at {a}"

/-- The centre of `#cas [series x a n]`: a rational literal (`"-"? num (" / " num)?`), or a
term of maximal precedence, such as an expression in parentheses, read by `parseRational`. -/
def parseCentre (centre : Syntax) : CommandElabM ℚ := do
  let inner := centre[0]
  unless inner.getKind == groupKind do
    return ← parseRational "series" inner
  -- The numerals of a literal are read by `parseRational` too, with its size guard. Both are
  -- below the bound, and so are the numerator and the denominator of their quotient.
  let numerator ← parseRational "series" inner[1]
  let denominator ← if inner[2].isNone then pure (1 : ℚ) else parseRational "series" inner[2][1]
  if denominator = 0 then
    throwErrorAt centre "series: expected a rational number"
  let magnitude := numerator / denominator
  return if inner[0].isNone then magnitude else -magnitude

/-- Parse a one-variable expression in the named coordinate. -/
def parseUnivariate (coordinate : TSyntax `ident) (input : Syntax) :
    CommandElabM (ReifiedExpr × Verified.Expr (Fin 1)) := do
  let reified ← parseExact input [coordinate.getId]
  match reified with
  | ⟨[_], expression, _⟩ => return (reified, expression)
  | _ => throwErrorAt input "expected an expression in {coordinate.getId} alone"

/-- `∑ c_k b ^ k` in increasing powers of `b`, as Mathematica prints series. -/
def ascendingForm (b : FullSimplify.Form) (cs : List ℚ) : FullSimplify.Form := Id.run do
  let term (c : ℚ) (k : Nat) : FullSimplify.Form :=
    let power : FullSimplify.Form := if k = 1 then b else .pow b k
    if k = 0 then .num c else if c = 1 then power else .mul (.num c) power
  let terms := (cs.zipIdx.filter (·.1 != 0))
  match terms with
  | [] => return .num 0
  | (c, k) :: rest =>
      let mut total : FullSimplify.Form :=
        if c < 0 && k > 0 then .neg (term (-c) k) else term c k
      for (c, k) in rest do
        total := if c < 0 then .sub total (term (-c) k) else .add total (term c k)
      return total

/-- Run `#cas [series x a n] f`. -/
def logSeries (ref : Syntax) (coordinate : TSyntax `ident) (centre : Syntax) (n : Nat)
    (input : Syntax) : CommandElabM Unit := do
  if n > 12 then throwErrorAt ref "series accepts orders up to 12"
  let a ← parseCentre centre
  let (reified, expr) ← parseUnivariate coordinate input
  let mut coefficients : Array ℚ := #[]
  for k in [0:n + 1] do
    match derivativeAt expr k a with
    | some value => coefficients := coefficients.push (value / k.factorial)
    | none =>
        throwErrorAt input "series: the derivative of order {k} at {surfaceText centre} is not an \
          exact rational number (exact values are known for sin, cos, exp, atan, asin at 0, \
          log, acos at 1, and square roots of rational squares)"
  let proof ← liftTermElabM do
    let quoted ← quoteVerifiedExpr expr
    let validity ← requireValidityAt "series" "expression" quoted (n + 1) a
    let csTerm ← mkListLit (mkConst ``Rat) (← coefficients.toList.mapM fun c ↦ quoteRat c)
    let partialProof ← mkAppM ``series_of_check
      #[quoted, toExpr n, ← quoteRat a, validity, csTerm]
    let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
      | throwError "series: unexpected certificate theorem shape"
    let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
    Digits.cleanProof (mkApp partialProof check) seriesCleanLemmas
      [``Verified.Expr.univariateEval]
  let report ← liftTermElabM do
    evidenceReportMessage #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
      "Taylor expansion with a little-o remainder" proof]
  -- `x + 1/2` rather than `x - -1/2` at a negative centre.
  let shifted :=
    if a < 0 then s!"{coordinate.getId} + {-a}" else s!"{coordinate.getId} - {a}"
  let base : FullSimplify.Form :=
    if a = 0 then .var coordinate.getId
    else if a < 0 then .add (.var coordinate.getId) (.num (-a))
    else .sub (.var coordinate.getId) (.num a)
  let polynomial := ascendingForm base coefficients.toList
  let remainder := if a = 0 then s!"o({coordinate.getId}^{n})" else s!"o(({shifted})^{n})"
  logReport ref {
    domain := s!"{coordinate.getId} → {a}"
    input := reified.render
    inputType := "scalar ℝ"
    output := s!"{polynomial.render} + {remainder}"
    outputType := "Taylor polynomial with exact coefficients"
  } #[
    computationNode "Checked coefficients" #[
      m!"Coefficients of ({shifted})^0, …, ^{n}: {coefficients.toList}"],
    report]

/-- The first order at which the derivative at `a` is nonzero, up to `bound`. -/
def order? (expr : Verified.Expr (Fin 1)) (a : ℚ) (bound : Nat) : Option (Nat × ℚ) := Id.run do
  for k in [0:bound + 1] do
    match derivativeAt expr k a with
    | some 0 => continue
    | some value => return some (k, value)
    | none => return none
  return none

/-- Run `#cas [limit x → a] f`. -/
def logLimit (ref : Syntax) (coordinate : TSyntax `ident) (aStx : Syntax) (input : Syntax) :
    CommandElabM Unit := do
  let a ← parseRational "limit" aStx
  let (reified, expr) ← parseUnivariate coordinate input
  let quotient? : Option (Verified.Expr (Fin 1) × Verified.Expr (Fin 1)) :=
    match expr with
    | .div num den => if derivativeAt den 0 a == some 0 then some (num, den) else none
    | _ => none
  match quotient? with
  | some (num, den) =>
      let some (m, denValue) := order? den a 12
        | throwErrorAt input "limit: the denominator has no nonzero derivative of order at \
            most 12 at {a} that is an exact rational number"
      for k in [0:m] do
        unless derivativeAt num k a == some 0 do
          throwErrorAt input "limit: the numerator does not vanish to order {m} at {a}; \
            the quotient has no finite limit or the value is not an exact rational"
      let some numValue := derivativeAt num m a
        | throwErrorAt input "limit: the derivative of order {m} of the numerator at {a} is \
            not an exact rational number"
      let c := numValue / m.factorial
      let d := denValue / m.factorial
      let proof ← liftTermElabM do
        let quotedNum ← quoteVerifiedExpr num
        let quotedDen ← quoteVerifiedExpr den
        let validNum ← requireValidityAt "limit" "numerator" quotedNum (m + 1) a
        let validDen ← requireValidityAt "limit" "denominator" quotedDen (m + 1) a
        let partialProof ← mkAppM ``tendsto_div_of_check
          #[quotedNum, quotedDen, toExpr m, ← quoteRat a, validNum, validDen, ← quoteRat c,
            ← quoteRat d, ← quoteRat (c / d)]
        let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
          | throwError "limit: unexpected certificate theorem shape"
        let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
        Digits.cleanProof (mkApp partialProof check) seriesCleanLemmas
          [``Verified.Expr.univariateEval]
      let report ← liftTermElabM do
        evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            s!"Limit from the leading terms of order {m}" proof]
      logReport ref {
        domain := s!"{coordinate.getId} → {a}, {coordinate.getId} ≠ {a}"
        input := reified.render
        inputType := "scalar ℝ"
        output := toString (c / d)
        outputType := "exact limit"
      } #[computationNode "Leading terms" #[
          m!"Numerator {c} (x - a)^{m}, denominator {d} (x - a)^{m} (not proof)"], report]
  | none =>
      let proof ← liftTermElabM do
        let quoted ← quoteVerifiedExpr expr
        let some validity ← validityAt quoted 1 a
          | throwError "limit: the domain checker did not certify that the expression is \
              defined at {a}; for a quotient whose denominator vanishes at {a}, write it as a \
              single quotient"
        let theoremProof ← mkAppM ``tendsto_of_validIteratesOn #[quoted, ← quoteRat a, validity]
        Digits.cleanProof theoremProof seriesCleanLemmas [``Verified.Expr.univariateEval]
      let report ← liftTermElabM do
        evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            "Continuity at a point of validity" proof]
      let value := match derivativeAt expr 0 a with
        | some q => toString q
        | none =>
            let closed := expr.mapVars fun _ ↦ (.rat a.num a.den : Verified.Expr (Fin 1))
            (FullSimplify.Form.ofExpr reified.names closed).render
      logReport ref {
        domain := s!"{coordinate.getId} → {a}"
        input := reified.render
        inputType := "scalar ℝ"
        output := value
        outputType := "limit, the value at the point"
      } #[report]

end CAS.Command.Series

namespace CAS.Command

open Lean Elab Command

/-- The centre of `#cas [series x a n]`: a rational literal such as `1/2`, `-3` or `1/10000`, or a
closed calculator expression with a rational value in parentheses. -/
syntax casSeriesCentre := ("-"? num (" / " num)?) <|> term:max

/-- `#cas [series x a n] e` computes the Taylor polynomial of `e` of degree `n` at the rational
point `a`, with exact coefficients and a little-o remainder, or the Laurent series when `e` is a
quotient whose denominator vanishes at `a`.

## Theorem
For the printed coefficients `c k`, the report proves
`(fun x ↦ e - ∑ k ∈ Finset.range (n + 1), c k * (x - a) ^ k) =o[𝓝 a] fun x ↦ (x - a) ^ n`
(`CAS.Verified.Expr.series_of_check`). For a quotient `g / h` whose denominator vanishes at `a`
to order `m`, the sum runs over the integer powers from `-m` to `n` and the remainder holds on
`𝓝[≠] a` (`CAS.Verified.Expr.laurent_of_check`).

## Conditions and limits
The order `n` is at most 12. `e` uses the functions of `#cas [derive x]` and no other variable.
The centre `a` is a rational literal such as `1/2`, `-1/2` or `1/10000`, or a closed calculator
expression in parentheses with a rational value, built from integers, fractions and decimals by
`+`, `-`, `*`, `/` and powers with integer literal exponents, such as `(1/2 - 1/3)`. A named
definition or a function value such as `(sqrt 4)` is refused, even when its value is rational. The
coefficients are the derivatives at `a` evaluated exactly, so every function must sit at a point
where its value is rational: `sin`, `cos`, `exp`, `atan` and `asin` at `0`, `log` and `acos` at `1`,
and square roots of rational squares. The derivatives must be defined at `a`; the theorem extends
their validity to a neighbourhood of `a`, so a centre as close to a singularity as `1/10000` for
`sqrt x` is accepted.

## Options
None.

## Examples
```lean
#cas [series x 0 7] (sin x)
```
```output
Output (Taylor polynomial with exact coefficients): x - 1/6*x^3 + 1/120*x^5 - 1/5040*x^7 + o(x^7)
```
```lean
#cas [series x 0 3] (1 / sin x)
```
```output
Output (Laurent series with a pole of order 1): 1/x + 1/6*x + 7/360*x^3 + o(x^3)
```
```lean
#cas [series x 1 4] (log x)
```
```output
Output (Taylor polynomial with exact coefficients): x - 1 - 1/2*(x - 1)^2 + 1/3*(x - 1)^3
- 1/4*(x - 1)^4 + o((x - 1)^4)
```
```lean
#cas [series x 1/10000 2] (sqrt x)
```
```output
Output (Taylor polynomial with exact coefficients): 1/100 + 50*(x - 1/10000)
- 125000*(x - 1/10000)^2 + o((x - 1/10000)^2)
```

## In a proof
```lean
open Filter Topology in
theorem series_sin_remainder
    (h : (fun x : ℝ ↦ Real.sin x - (x - 1 / 6 * x ^ 3)) =o[𝓝 0] fun x ↦ x ^ 3) :
    Tendsto (fun x : ℝ ↦ (Real.sin x - (x - 1 / 6 * x ^ 3)) / x ^ 3) (𝓝 0) (𝓝 0) :=
  h.tendsto_div_nhds_zero
```
The tactic `cas` does not prove the little-o statement, so a proof takes the printed theorem as a
hypothesis.

## See also
Mathematica `Series`, SymPy `series`. The modes `limit` and `derive`.

## Possible issues
```lean
#cas [series x 0 3] (abs x)
```
```output
series: the domain checker did not certify that the expression and its derivatives through order
3 are defined at 0
```
`abs` has no derivative at `0`; expand at a point where `e` is smooth.
```lean
#cas [series x 0 3] (log x)
```
```output
series: the derivative of order 0 at 0 is not an exact rational number (exact values are known for
sin, cos, exp, atan, asin at 0, log, acos at 1, and square roots of rational squares)
```
`log` is expanded at `1`: `#cas [series x 1 3] (log x)`.
```lean
#cas [series x 0 13] (sin x)
```
```output
series accepts orders up to 12
```
Ask for an order of at most 12.
-/
syntax (name := casSeriesCommand)
  "#cas" "[" &"series" ident casSeriesCentre num "]" term : command

/-- `#cas [limit x → a] e` computes the limit of `e` as `x` tends to the rational number `a` and
proves it.

## Theorem
When `e` is valid at `a`, the report proves `Tendsto (fun x ↦ e) (𝓝 a) (𝓝 L)`, where `L` is the
value at `a`. For a quotient `g / h` whose denominator vanishes at `a`, it proves
`Tendsto (fun x ↦ g / h) (𝓝[≠] a) (𝓝 L)` from the first derivatives of `g` and `h` that do not
vanish at `a` (`CAS.Verified.Expr.tendsto_div_of_check`). At a pole it proves
`Tendsto (fun x ↦ g / h) (𝓝[≠] a) atTop` (or `atBot`), and for a pole of odd order the two
one-sided infinite limits. The forms `x → ∞`, `x → -∞`, `x → a from above` and
`x → a from below` prove the same with the filters `atTop`, `atBot`, `𝓝[>] a` and `𝓝[<] a`.

## Conditions and limits
`a` is a closed calculator expression with a rational value, built from integers, fractions and
decimals by `+`, `-`, `*`, `/` and powers with integer literal exponents, such as `1/10000`, `-1/2`
or `0.25`. A named definition or a function value such as `sqrt 4` is refused, even when its value
is rational. `e` uses the functions of `#cas [derive x]`. The domain checker certifies that `e`, or
the numerator and the denominator of a quotient, are defined at `a`, and the theorem extends this to
a neighbourhood of `a`. For a quotient whose denominator vanishes at `a`, the derivatives of the
numerator and the denominator at `a` must have exact rational values, as those of `sin`, `cos`,
`exp`, `atan` and `asin` at `0` and of `log` and `acos` at `1` do.

## Options
None.

## Examples
```lean
#cas [limit x → 0] (sin x / x)
```
```output
Output (exact limit): 1
```
```lean
#cas [limit x → ∞] ((x^2 + 1) / (2*x^2 - 3))
```
```output
Output (exact limit from the terms of order 0): 1/2
```
```lean
#cas [limit x → 0 from above] (1 / x)
```
```output
Output (infinite limit at a pole of order 1): ∞
```
```lean
#cas [limit x → 1/10000] (sqrt x)
```
```output
Output (limit, the value at the point): 1/100
```

## In a proof
```lean
open Filter Topology in
theorem limit_sinc : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas
```

## See also
Mathematica `Limit`, SymPy `limit`. The modes `series`, `derive` and `sum k a ∞`, and the tactic
`cas`, which proves limits with the filters `𝓝 a`, `𝓝[≠] a`, `𝓝[>] a`, `𝓝[<] a`, `atTop` and
`atBot`.

## Possible issues
```lean
#cas [limit x → π] (sin x)
```
```output
limit: expected a rational number
```
The point must be a rational number or `∞`, `-∞`.
```lean
#cas [limit x → 0] (sin (1 / x))
```
```output
limit: the domain checker did not certify that the expression is defined at 0; for a quotient
whose denominator vanishes at 0, write it as a single quotient
```
Write a quotient as a single fraction `g / h`. Here `sin (1 / x)` has no limit at `0`.
-/
syntax (name := casLimitCommand) "#cas" "[" &"limit" ident " → " term "]" term : command

elab_rules : command
  | `(#cas [series $x:ident $a:casSeriesCentre $n:num] $expr:term) =>
      Series.logSeries expr x a n.getNat expr
  | `(#cas [limit $x:ident → $a:term] $expr:term) =>
      Series.logLimit expr x a expr

end CAS.Command
