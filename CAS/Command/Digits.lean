/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Elaboration
public import CAS.Command.Common
public meta import CAS.CEGA.Elaboration

/-!
# Certified decimal digits: `#cas [N d]`

`#cas [N d] e` prints the first `d` significant decimal digits of a closed real expression `e`
and proves them. The digits are the truncation of the true value toward zero: for a positive
value the theorem is `m / 10 ^ k ≤ e < (m + 1) / 10 ^ k`, where `m` has `d` digits, and for a
negative value `-(m + 1) / 10 ^ k < e ≤ -m / 10 ^ k`. Large values use `m 10 ^ k` instead.

The expression uses the calculator grammar of `#cas`: rational arithmetic, natural and integer
powers, `sqrt`, `exp`, `log`, `sin`, `cos`, `tan`, `atan`, `asin`, `acos`, the hyperbolic
functions, real powers with positive base, and the constants `pi` (also written `π` or `Pi`)
and `E`.

## Implementation notes

The search runs outside the kernel. We evaluate the expression with the interval evaluator
`DigitsEval.eval` of `CAS/Continuum/IntervalEval/Digits.lean` at the precision
`precisionFor d r` of round `r = 0, …, 4`, which doubles the bits, the series terms and the
logarithm terms from one round to the next, and stop at the first enclosure from which
`resolve?` reads all `d` digits. `certify` applies `DigitsEval.of_lowerCheck_decimal` (or
`of_upperCheck_decimal`, `of_lowerCheck_scaled`, `of_upperCheck_scaled`) at that precision, and
`CAS.CEGA.Elaboration.decideClosedCertificate` has the kernel decide its check without native
code. The comparison of the enclosure with the two decimal bounds is sound at every precision,
so the precision only decides whether the check succeeds. When four doublings do not resolve
the digits (for instance when the value is a decimal with fewer than `d` digits, such as
`cos (pi / 3)`), we certify the decimal enclosure with `d` places of the first round instead
(`enclosureOutcome`, `DigitsEval.of_enclosureCheck_decimal`).
-/

public meta section

namespace CAS.Command.Digits

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Elaboration.RealExpression
open CAS.Continuum

/-- Replace the coordinates `π`, `Pi` and `E` by the constants they denote. -/
def closeNamedConstants : ReflectedExpr Name Nat → ReflectedExpr Name Nat
  | .coordinate name =>
      if name == `π || name == `Pi then .constant .pi
      else if name == `E then .constant .e
      else .coordinate name
  | .add lhs rhs => .add (closeNamedConstants lhs) (closeNamedConstants rhs)
  | .mul lhs rhs => .mul (closeNamedConstants lhs) (closeNamedConstants rhs)
  | .sub lhs rhs => .sub (closeNamedConstants lhs) (closeNamedConstants rhs)
  | .div lhs rhs => .div (closeNamedConstants lhs) (closeNamedConstants rhs)
  | .neg arg => .neg (closeNamedConstants arg)
  | .pow base exponent => .pow (closeNamedConstants base) exponent
  | .unary operation arg => .unary operation (closeNamedConstants arg)
  | .apply function arg => .apply function (closeNamedConstants arg)
  | .rpow base exponent => .rpow (closeNamedConstants base) (closeNamedConstants exponent)
  | expression => expression

private def coordinateNames : ReflectedExpr Name Nat → List Name
  | .coordinate name => [name]
  | .add lhs rhs | .mul lhs rhs | .sub lhs rhs | .div lhs rhs | .rpow lhs rhs =>
      coordinateNames lhs ++ coordinateNames rhs
  | .neg arg | .pow arg _ | .unary _ arg | .apply _ arg => coordinateNames arg
  | _ => []

/-- Parse a closed calculator expression, an argument of the mode or call `command` (which the
refusals name), into the checked expression language. A refusal of the parser keeps its reason
after that name (`gamma: unsupported symbolic function 'foo'; …`). -/
def parseClosed (command : String) (stx : Syntax) : CommandElabM (Verified.Expr (Fin 0)) := do
  let parsed ← try parseExpr stx catch error =>
    match error with
    | .error ref message => throw (.error ref m!"{command}: {message}")
    | _ => throw error
  let named := closeNamedConstants parsed
  let free := (coordinateNames named).eraseDups
  unless free.isEmpty do
    throwErrorAt stx "{command} needs a closed expression; free symbols: {renderNames free}"
  match ReflectedExpr.toVerifiedExprM? (m := Id) (ι' := Fin 0)
      (fun _ ↦ none) (fun exponent ↦ some exponent) named with
  | some expression => return expression
  | none => throwErrorAt stx "{command} could not lower this expression to the checked language"

/-- The working precision of round `round` for `digits` digits. -/
def precisionFor (digits round : Nat) : DigitsEval.Precision :=
  { bits := (digits * 3322 / 1000 + 40) * 2 ^ round, terms := (digits + 24) * 2 ^ round,
    logTerms := (digits * 22 / 10 + 40) * 2 ^ round }

/-- The decimal exponent `E` with `10 ^ E ≤ q < 10 ^ (E + 1)`, for positive `q`. -/
def decimalExponent (q : ℚ) : Int := Id.run do
  let mut exponent : Int :=
    ((toString q.num.natAbs).length : Int) - ((toString q.den).length : Int)
  -- The digit counts give the exponent up to one; the loops correct it.
  while (10 : ℚ) ^ (exponent + 1) ≤ q do
    exponent := exponent + 1
  while q < (10 : ℚ) ^ exponent do
    exponent := exponent - 1
  return exponent

/-- How the certified digits were obtained. -/
inductive Outcome where
  /-- A positive value with `m / 10 ^ k ≤ x < (m + 1) / 10 ^ k`. -/
  | positiveDecimal (m k : Nat)
  /-- A negative value with `-(m + 1) / 10 ^ k < x ≤ -m / 10 ^ k`. -/
  | negativeDecimal (m k : Nat)
  /-- A large positive value with `m 10 ^ k ≤ x < (m + 1) 10 ^ k`. -/
  | positiveScaled (m k : Nat)
  /-- A large negative value with `-(m + 1) 10 ^ k < x ≤ -m 10 ^ k`. -/
  | negativeScaled (m k : Nat)
  /-- A closed enclosure `lo ≤ x ≤ hi` with decimal endpoints over `10 ^ k`. -/
  | enclosure (lo hi : Int) (k : Nat)

/-- Truncated digits of a positive interval, when both endpoints agree on them. -/
def positiveDigits? (digits : Nat) (lo hi : ℚ) : Option Outcome :=
  let exponent := decimalExponent lo
  let shift : Int := (digits : Int) - 1 - exponent
  if 0 ≤ shift then
    let k := shift.toNat
    let m := ⌊lo * 10 ^ k⌋.toNat
    if hi < ((m : ℚ) + 1) / 10 ^ k then some (.positiveDecimal m k) else none
  else
    let k := (-shift).toNat
    let m := ⌊lo / 10 ^ k⌋.toNat
    if hi < ((m : ℚ) + 1) * 10 ^ k then some (.positiveScaled m k) else none

/-- Truncated digits of the enclosure `I`, if it determines them. -/
def resolve? (digits : Nat) (I : RationalInterval) : Option Outcome :=
  if 0 < I.lo then
    positiveDigits? digits I.lo I.hi
  else if I.hi < 0 then
    match positiveDigits? digits (-I.hi) (-I.lo) with
    | some (.positiveDecimal m k) =>
        if (-((m : ℚ) + 1)) / 10 ^ k < I.lo then some (.negativeDecimal m k) else none
    | some (.positiveScaled m k) =>
        if -((m : ℚ) + 1) * 10 ^ k < I.lo then some (.negativeScaled m k) else none
    | _ => none
  else
    none

/-- A decimal enclosure of `I` with `digits` places after the point. -/
def enclosureOutcome (digits : Nat) (I : RationalInterval) : Outcome :=
  .enclosure ⌊I.lo * 10 ^ digits⌋ ⌈I.hi * 10 ^ digits⌉ digits

/-- Render `m / 10 ^ k` as a decimal string. -/
def renderDecimal (m : Nat) (k : Nat) : String :=
  let s := toString m
  if k = 0 then s
  else if s.length > k then
    let point := s.length - k
    String.ofList (s.toList.take point) ++ "." ++ String.ofList (s.toList.drop point)
  else
    "0." ++ String.ofList (List.replicate (k - s.length) '0') ++ s

/-- Render `m 10 ^ k` in scientific notation. -/
def renderScaled (m : Nat) (k : Nat) : String :=
  let s := toString m
  let exponent := s.length - 1 + k
  let mantissa :=
    if s.length = 1 then s
    else String.ofList (s.toList.take 1) ++ "." ++ String.ofList (s.toList.drop 1)
  s!"{mantissa} × 10^{exponent}"

/-- Render a signed decimal `z / 10 ^ k`. -/
def renderSigned (z : Int) (k : Nat) : String :=
  if z < 0 then "-" ++ renderDecimal z.natAbs k else renderDecimal z.natAbs k

/-- Render `m / 10 ^ k`, in scientific notation when the value is below `10 ^ (-6)`. -/
def renderSmall (m k : Nat) : String :=
  let s := toString m
  if k ≥ s.length + 6 then
    let mantissa :=
      if s.length = 1 then s
      else String.ofList (s.toList.take 1) ++ "." ++ String.ofList (s.toList.drop 1)
    s!"{mantissa} × 10^-{k + 1 - s.length}"
  else renderDecimal m k

/-- The displayed result. -/
def renderOutcome : Outcome → String
  | .positiveDecimal m k => renderSmall m k
  | .negativeDecimal m k => "-" ++ renderSmall m k
  | .positiveScaled m k => renderScaled m k
  | .negativeScaled m k => "-" ++ renderScaled m k
  | .enclosure lo hi k => s!"[{renderSigned lo k}, {renderSigned hi k}]"

/-- Simplification set that turns `Verified.Expr.eval` and numeral casts into ordinary real
notation, extended by the lemmas `extra`. -/
def cleanSimpTheorems (extra : List Name := []) (unfold : List Name := [])
    (reversed : List Name := []) : MetaM SimpTheorems := do
  let mut theorems : SimpTheorems := {}
  theorems ← theorems.addDeclToUnfold ``Verified.Expr.eval
  for name in unfold do
    theorems ← theorems.addDeclToUnfold name
  for name in reversed do
    theorems ← theorems.addConst name (inv := true)
  for name in [``Nat.cast_ofNat, ``Nat.cast_one, ``Nat.cast_zero, ``Int.cast_ofNat,
      ``Int.cast_one, ``Int.cast_zero, ``Int.cast_neg, ``Nat.cast_add] ++ extra do
    theorems ← theorems.addConst name
  return theorems

/-- Restate a proof about `Verified.Expr.eval` in ordinary real notation. -/
def cleanProof (proof : Lean.Expr) (extra : List Name := []) (unfold : List Name := [])
    (simprocs : Bool := false) (reversed : List Name := []) : MetaM Lean.Expr := do
  let type ← inferType proof
  let context ← Simp.mkContext {}
    (simpTheorems := #[← cleanSimpTheorems extra unfold reversed])
    (congrTheorems := ← getSimpCongrTheorems)
  let defaults ← Simp.getSimprocs
  let procs : Simp.SimprocsArray := if simprocs then #[defaults] else #[]
  let (result, _) ← simp type context procs
  match result.proof? with
  | none => mkExpectedTypeHint proof result.expr
  | some equality => mkEqMP equality proof

/-- The binder names of `original` on the same binders of `changed`. -/
partial def restoreNames : Lean.Expr → Lean.Expr → Lean.Expr
  | .forallE n t₁ b₁ _, .forallE _ t₂ b₂ bi =>
      .forallE n (restoreNames t₁ t₂) (restoreNames b₁ b₂) bi
  | .lam n t₁ b₁ _, .lam _ t₂ b₂ bi => .lam n (restoreNames t₁ t₂) (restoreNames b₁ b₂) bi
  | .app f₁ a₁, .app f₂ a₂ => .app (restoreNames f₁ f₂) (restoreNames a₁ a₂)
  | _, changed => changed

/-- Evaluate the closed numeral arithmetic in a statement by `norm_num`, keeping the decimal
bounds `m / 10 ^ k` as they are. -/
def evaluateNumerals (proof : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType proof
  let isBound (e : Lean.Expr) : Bool :=
    e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 5).isAppOfArity ``HPow.hPow 6
  let methods : Simp.Methods := {
    pre := fun e ↦ if isBound e then return .done { expr := e }
      else Mathlib.Meta.NormNum.tryNormNum (post := false) e
    post := fun e ↦ if isBound e then return .done { expr := e }
      else Mathlib.Meta.NormNum.tryNormNum (post := true) e
    discharge? := Simp.dischargeGround }
  let context ← Simp.mkContext {} (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Simp.main type context (methods := methods)
  let restored := restoreNames type result.expr
  match result.proof? with
  | none => mkExpectedTypeHint proof restored
  | some equality => mkExpectedTypeHint (← mkEqMP equality proof) restored

/-- The proof of the reported statement, checked by the kernel. -/
def certify (precision : DigitsEval.Precision) (expression : Verified.Expr (Fin 0))
    (outcome : Outcome) : MetaM Lean.Expr := do
  let precisionTerm := mkApp3 (mkConst ``DigitsEval.Precision.mk)
    (toExpr precision.bits) (toExpr precision.terms) (toExpr precision.logTerms)
  let expressionTerm ← quoteVerifiedExpr expression
  let rho ← Term.TermElabM.run' do
    Term.elabTerm (← `((Fin.elim0 : Fin 0 → ℝ))) none
  let (theoremName, args) := match outcome with
    | .positiveDecimal m k => (``DigitsEval.of_lowerCheck_decimal, #[toExpr m, toExpr k])
    | .negativeDecimal m k => (``DigitsEval.of_upperCheck_decimal, #[toExpr m, toExpr k])
    | .positiveScaled m k => (``DigitsEval.of_lowerCheck_scaled, #[toExpr m, toExpr k])
    | .negativeScaled m k => (``DigitsEval.of_upperCheck_scaled, #[toExpr m, toExpr k])
    | .enclosure lo hi k =>
        (``DigitsEval.of_enclosureCheck_decimal, #[toExpr lo, toExpr hi, toExpr k])
  let partialProof ←
    mkAppOptM theoremName (#[some precisionTerm, some expressionTerm] ++ args.map some)
  let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
    | throwError "N: unexpected certificate theorem shape"
  let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
  cleanProof (mkApp2 partialProof check rho)

/-- Run `#cas [N d] e`. -/
def logDigits (ref : Syntax) (digits : Nat) (input : Syntax) : CommandElabM Unit := do
  checkDigitCount ref "N" digits
  let expression ← parseClosed "N" input
  let mut found : Option (DigitsEval.Precision × Outcome) := none
  let mut first : Option (DigitsEval.Precision × RationalInterval) := none
  for round in [0:5] do
    if found.isSome then break
    let precision := precisionFor digits round
    match DigitsEval.eval precision DigitsEval.closedEnv expression with
    | none =>
        throwErrorAt input "N could not enclose this expression: a logarithm or square root \
          of a value not certified positive, a quotient by an interval containing zero, or a \
          real power with a base not certified positive"
    | some I =>
        if first.isNone then first := some (precision, I)
        if let some outcome := resolve? digits I then
          found := some (precision, outcome)
  let (precision, outcome) ← match found, first with
    | some result, _ => pure result
    | none, some (precision, I) => pure (precision, enclosureOutcome digits I)
    | none, none => throwErrorAt input "N could not enclose this expression"
  let report ← liftTermElabM do
    let proof ← certify precision expression outcome
    let step := match outcome with
      | .enclosure _ _ _ => "Certified decimal enclosure"
      | _ => "Certified decimal digits"
    evidenceReportMessage #[← proofStep step ``DigitsEval.eval_sound proof]
  let outputType := match outcome with
    | .enclosure _ _ _ => "certified decimal enclosure"
    | _ => s!"first {digits} significant digits, truncated"
  logReport ref {
    domain := "closed real expression"
    input := surfaceText input
    inputType := "scalar ℝ"
    output := renderOutcome outcome
    outputType
  } #[
    computationNode "Certified numerical evaluation" #[
      m!"Working precision: {precision.bits} bits, {precision.terms} series terms, \
        {precision.logTerms} logarithm terms",
      (match outcome with
        | .enclosure _ _ _ => m!"Guarantee: the real value lies in the printed decimal enclosure"
        | _ => m!"Guarantee: every printed digit is a digit of the real value, \
            truncated toward zero")
    ],
    report
  ]

end CAS.Command.Digits

namespace CAS.Command

open Lean Elab Command

/-- `#cas [N d] e` prints the first `d` significant decimal digits of the closed real expression
`e`, truncated toward zero, and proves them.

## Theorem
For a positive value whose printed digits form the integer `m`, the report proves
`m / 10 ^ k ≤ e ∧ e < (m + 1) / 10 ^ k`, and for a negative value
`-(m + 1) / 10 ^ k < e ∧ e ≤ -m / 10 ^ k` (`CAS.Continuum.DigitsEval.eval_sound`). A value with
more than `d` digits before the point has `m * 10 ^ k` in place of `m / 10 ^ k`. When four
doublings of the working precision do not resolve the digits, as for `cos (pi / 3)`, whose value
`1 / 2` has a short decimal expansion, the report proves a decimal enclosure
`lo / 10 ^ k ≤ e ∧ e ≤ hi / 10 ^ k` instead.

## Conditions and limits
`e` is closed and uses the calculator grammar of `#cas`: rational arithmetic, natural and integer
powers, `sqrt`, `exp`, `log`, `sin`, `cos`, `tan`, `atan`, `asin`, `acos`, the hyperbolic
functions, real powers with a positive base, and the constants `pi` (also `π` or `Pi`) and `E`.
`BesselJ n q` with an integer order `n`, `erf q` and the orthogonal polynomials at a rational
point `q` have their own routes; `BesselJ` and `erf` accept at most 30 digits. `d` is between 1
and the option `cas.maxDigits`.

## Options
`set_option cas.maxDigits n` sets the largest `d`, default 2000.

## Examples
```lean
#cas [N 20] (sqrt 2)
```
```output
Output (first 20 significant digits, truncated): 1.4142135623730950488
```
```lean
#cas [N 10] (exp 1 + pi)
```
```output
Output (first 10 significant digits, truncated): 5.859874482
```
```lean
#cas [N 20] (cos (pi / 3))
```
```output
Output (certified decimal enclosure): [0.49999999999999999999, 0.50000000000000000001]
```

## In a proof
```lean
theorem digits_sqrt_two : Real.sqrt 2 ≤ 1.415 := by
  cega
```
The tactic `cega` proves a bound that the printed digits imply.

## See also
Mathematica `N`, SymPy `N` and `evalf`. The modes `enclose`, `nintegrate` and `findRoot`, and the
tactic `cega`.

## Possible issues
```lean
#cas [N 15] (x + 1)
```
```output
N needs a closed expression; free symbols: x
```
Substitute a rational value for each variable, or enclose the expression on a box with
`#cas [enclose x in [a, b]]`.
```lean
#cas [N 0] (pi)
```
```output
N accepts between 1 and 2000 digits
```
Ask for at least one digit; `set_option cas.maxDigits` raises the upper limit.
-/
syntax (name := casDigitsCommand) "#cas" "[" &"N" num "]" term : command

elab_rules : command
  | `(#cas [N $digits:num] $expr:term) =>
      Digits.logDigits digits digits.getNat expr

end CAS.Command
