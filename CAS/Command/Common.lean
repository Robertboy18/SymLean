/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import CAS.ClosedForm.Pipeline.Configured
public import CAS.Command.Explanation
public import CAS.Command.Report
public import CAS.Command.Syntax
public meta import CAS.Command.Syntax
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import CAS.Expr.AutomaticSign

/-!
# Shared implementation for exact `#cas` commands

The exact `#cas` modes share the rendering of reified expressions and of their side conditions
(`renderExpr`, `renderConditions`), the evidence part of a report (`evidenceReportMessage`,
`proofStep`), the lookup of coordinates (`coordinateAt`, `uniqueCoordinate`,
`scalarCoordinateInput`), the elaboration of a proof against its statement (`elabCheckedProof`),
and the translation between calculator expressions and Mathlib terms in both directions
(`exprTerm`, `ReifiedExpr.inputTerm`, `realForallStatement`; `renderTerm`, `renderProp`). The
expression parser is `CAS.Command.Syntax`; each mode declares its `#cas [...]` syntax and
elaborator in its own module under `CAS.Command`. The definitions are namespaced as command
internals and do not extend the mathematical expression or certificate APIs.

## Main definitions

* `CAS.Command.renderConditions`: the `Conditions` line of a report, from checked requirements.
* `CAS.Command.evidenceReportMessage`: validate every proof step, then render the evidence tree.
* `CAS.Command.proofStep`: a generated proof term as an evidence step with its theorem name.
* `CAS.Command.elabCheckedProof`: a proof elaborated against its statement, refusing `sorry`.
* `CAS.Command.exprTerm`, `CAS.Command.ReifiedExpr.inputTerm`: a calculator expression, and the
  input as the user wrote it, as Mathlib terms.
* `CAS.Command.conditionTerms`, `CAS.Command.realForallStatement`: checked conditions as
  hypotheses, and the statement `∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → P` over them.
* `CAS.Command.renderTerm`, `CAS.Command.renderProp`: a Mathlib term or proposition in the
  notation of the calculator's printer.

## Implementation notes

A report lists a proof step as checked only after validation. `evidenceReportMessage`
validates all steps before it renders any (`CAS.Tactic.Explanation.validateAll`): a step with a
metavariable, a `sorry` or a placeholder axiom in its statement, its proof or the type of its
proof is refused, and the proof of every other step is added to the environment as an auxiliary
theorem under a fresh name and checked by the kernel at once
(`CAS.Tactic.Explanation.kernelCheckedProof`, through `ProofCarrier.addUncachedTheorem`). Steps
that the caller has validated already, such as the headline theorems of `withHeadlines`, come in
as `validated` and are listed first. `CAS.Command.Explanation.render` then prints the
propositions and the theorem names, not the proof terms.

The statements are Lean syntax, elaborated where the command runs, so they speak about the user's
own terms: `exprTerm` writes a calculator expression with Mathlib's functions, `conditionTerms`
states each displayed condition literally as the checked requirement it comes from, and
`realForallStatement` closes over the variables. `elabCheckedProof` elaborates a proof against
such a statement without error recovery, and the kernel checks it when the caller adds it. The
`Conditions` line prints the same conditions in display form (`renderConditions`): duplicates,
conditions that `Verified.Expr.AutomaticSign` recognizes and nonzero conditions implied by a
listed positivity condition are dropped, and a sum is written in descending powers when it
equals that polynomial with no further condition. The line adds no assumption.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation
open CAS.Elaboration.RealExpression (DesugaredFunction ReflectedExpr)

/-- Render an ordered coordinate-name table. -/
def renderNames (names : List Name) : String :=
  if names.isEmpty then
    "(none)"
  else
    ", ".intercalate (names.map renderName)

/-- Render the real coordinate space represented by a command's name table. -/
def renderRealDomain (names : List Name) : String :=
  match names with
  | [] => "ℝ^0 (constant)"
  | [name] => s!"{renderName name} ∈ ℝ"
  | _ => s!"({renderNames names}) ∈ ℝ^{names.length}"

/-- Replace every subterm that `function?` reads as a function of `DesugaredFunction` by an atom
carrying the function and its argument. -/
private def foldFunctions {ι : Type*}
    (function? : Verified.Expr ι → Option (DesugaredFunction × Verified.Expr ι))
    (expr : Verified.Expr ι) : Verified.Expr (ι ⊕ (DesugaredFunction × Verified.Expr ι)) :=
  match function? expr, expr with
  | some application, _ => .var (.inr application)
  | none, .nat k => .nat k
  | none, .int k => .int k
  | none, .rat num den => .rat num den
  | none, .pi => .pi
  | none, .e => .e
  | none, .var i => .var (.inl i)
  | none, .add a b => .add (foldFunctions function? a) (foldFunctions function? b)
  | none, .mul a b => .mul (foldFunctions function? a) (foldFunctions function? b)
  | none, .sub a b => .sub (foldFunctions function? a) (foldFunctions function? b)
  | none, .div a b => .div (foldFunctions function? a) (foldFunctions function? b)
  | none, .neg a => .neg (foldFunctions function? a)
  | none, .pow a k => .pow (foldFunctions function? a) k
  | none, .sin a => .sin (foldFunctions function? a)
  | none, .cos a => .cos (foldFunctions function? a)
  | none, .atan a => .atan (foldFunctions function? a)
  | none, .asin a => .asin (foldFunctions function? a)
  | none, .acos a => .acos (foldFunctions function? a)
  | none, .exp a => .exp (foldFunctions function? a)
  | none, .log a => .log (foldFunctions function? a)
  | none, .sqrt a => .sqrt (foldFunctions function? a)
  | none, .rpow a b => .rpow (foldFunctions function? a) (foldFunctions function? b)

/-- The display normal form of `expr` as text, with every form of a function of `functions`
written by the function's name: `tan(a)`, `|a|`, `sinh(a)`. -/
private partial def renderOutput {ι : Type*} [DecidableEq ι] (functions : List DesugaredFunction)
    (name : ι → String) (expr : Verified.Expr ι) : String :=
  (foldFunctions (DesugaredFunction.matchAmong? functions) expr.displayNormalForm).renderWith <|
    Sum.elim name fun (function, argument) ↦
      let shown := renderOutput functions name argument
      match function with
      | .abs => "|" ++ shown ++ "|"
      | function => function.displayName ++ "(" ++ shown ++ ")"

/-- An expression as text in the coordinate names written by the user: its `displayNormalForm`,
with every form of a function of `DesugaredFunction` that the input applies written by the
function's name (`tan(a)`, `|a|`, `sinh(a)`, `cosh(a)`, `tanh(a)`). The text is a display form:
neither `displayNormalForm` nor the names are proved equal to `expr`. What a report checks is
stated on its `Proposition` and `Theorem` lines. -/
def renderExpr (reified : ReifiedExpr)
    (expr : Verified.Expr (Fin reified.names.length)) : String :=
  renderOutput reified.inputFunctions reified.coordinateName expr

/-- `DesugaredFunction.match?` for the functions that the input applies, so that a statement about
a result names a function only when the input applies it somewhere. -/
def ReifiedExpr.resultFunction? (reified : ReifiedExpr)
    (expr : Verified.Expr (Fin reified.names.length)) :
    Option (DesugaredFunction × Verified.Expr (Fin reified.names.length)) :=
  DesugaredFunction.matchAmong? reified.inputFunctions expr

/-- Render a comma-separated list of expressions in user coordinates. -/
def renderExprList (reified : ReifiedExpr)
    (expressions : List (Verified.Expr (Fin reified.names.length))) : String :=
  if expressions.isEmpty then
    "(none)"
  else
    ", ".intercalate (expressions.map (renderExpr reified))

/-- Clean an expression for display with a checked route that needs no side conditions. -/
private def unconditionalDisplayNormalForm {ι : Type*} [DecidableEq ι]
    (expression : Verified.Expr ι) : Verified.Expr ι :=
  let route := Verified.Expr.simplifySideClaimRoute expression
  if route.nonzero.isEmpty then route.rhs else expression

/-- Remove factors that are automatically nonzero from a displayed nonzero condition. -/
private def nonzeroDisplayCore {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Verified.Expr ι
  | .neg argument => nonzeroDisplayCore argument
  | .pow argument (_ + 1) => nonzeroDisplayCore argument
  | .mul left right =>
      if Verified.Expr.AutomaticSign.nonzero left then
        nonzeroDisplayCore right
      else if Verified.Expr.AutomaticSign.nonzero right then
        nonzeroDisplayCore left
      else
        .mul left right
  | expression => expression

/-- Remove factors that are automatically positive from a displayed positivity condition. -/
private def positiveDisplayCore {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Verified.Expr ι
  | .mul left right =>
      if Verified.Expr.AutomaticSign.positive left then
        positiveDisplayCore right
      else if Verified.Expr.AutomaticSign.positive right then
        positiveDisplayCore left
      else
        .mul left right
  | expression => expression

private def nonzeroDisplayNormalForm {ι : Type*} [DecidableEq ι]
    (expression : Verified.Expr ι) : Verified.Expr ι :=
  let compacted := nonzeroDisplayCore expression
  nonzeroDisplayCore (unconditionalDisplayNormalForm compacted)

private def positiveDisplayNormalForm {ι : Type*} [DecidableEq ι]
    (expression : Verified.Expr ι) : Verified.Expr ι :=
  let normalized := unconditionalDisplayNormalForm expression
  let core := positiveDisplayCore normalized
  if core = normalized then expression else core

private def followsFromPositive {ι : Type*} [DecidableEq ι]
    (positive : List (Verified.Expr ι)) : Verified.Expr ι → Bool
  | .sqrt argument => positive.contains argument
  | expression => positive.contains expression

/-- A sum in a displayed condition as its polynomial over its atoms (`Alg.Canonical.compile`),
terms in the descending graded order of `mvNormalize`. A nonzero condition is scaled to integer
coefficients with a positive leading coefficient; a positivity condition is scaled by a positive
constant only and starts with a positive term. An expression whose rational skeleton has a
nonconstant denominator, or whose compilation holds only under the nonzero conditions it records
(a sum with a quotient by a nonconstant term, as in `1/(1/x + 1/(1 - x)) - 1`), is unchanged, so
that the displayed condition is never weaker than the one the theorem has. -/
private def orderedSum {ι : Type*} [DecidableEq ι] [Ord ι] (positive : Bool)
    (expression : Verified.Expr ι) : Verified.Expr ι :=
  let table := Verified.Expr.Alg.Canonical.atoms expression
  let fraction := Verified.Expr.Alg.Canonical.compile table expression
  match Verified.Expr.Alg.Canonical.constantValue? fraction.den, fraction.nonzero with
  | some denominator, [] =>
      let terms :=
        (Verified.Expr.Alg.mvNormalize fraction.num).map fun (c, m) ↦ (c / denominator, m)
      let lcmDen : ℕ := terms.foldl (fun acc (c, _) ↦ Nat.lcm acc c.den) 1
      let gcdNum : ℕ := terms.foldl (fun acc (c, _) ↦ Nat.gcd acc c.num.natAbs) 0
      let scale : ℚ := if gcdNum = 0 then 1 else (lcmDen : ℚ) / gcdNum
      let scale := match terms with
        | (lead, _) :: _ => if !positive && lead < 0 then -scale else scale
        | [] => scale
      let terms := terms.map fun (c, m) ↦ (c * scale, m)
      let terms := match terms, positive with
        | (lead, _) :: _, true =>
            if lead < 0 then
              match terms.findIdx? (0 < ·.1) with
              | some k => terms[k]! :: terms.eraseIdx k
              | none => terms
            else terms
        | _, _ => terms
      match terms with
      | [] => .nat 0
      | (c, m) :: rest =>
          Verified.Expr.Alg.Canonical.renderSum table
            (Verified.Expr.Alg.Canonical.renderTerm table c m) rest
  | _, _ => expression

/-- The factors of a displayed condition with every sum written by `orderedSum`. -/
private def orderedFactors {ι : Type*} [DecidableEq ι] [Ord ι] (positive : Bool) :
    Verified.Expr ι → Verified.Expr ι
  | .mul a b => .mul (orderedFactors positive a) (orderedFactors positive b)
  | .pow a k => .pow (orderedFactors positive a) k
  | expression@(.add _ _) | expression@(.sub _ _) | expression@(.neg _) =>
      orderedSum positive expression
  | expression => expression

/-- The parts of a displayed nonzero condition: `a / b ≠ 0` is `a ≠ 0` and `b ≠ 0`, and parts
that are automatically nonzero are dropped. -/
private partial def nonzeroParts {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → List (Verified.Expr ι)
  | .div a b =>
      (nonzeroParts (nonzeroDisplayCore a) ++ nonzeroParts (nonzeroDisplayCore b)).filter
        fun part ↦ !Verified.Expr.AutomaticSign.nonzero part
  | expression => [expression]

/--
Render the hypotheses under which an analytic certificate applies, in user coordinates.

The displayed list is a presentation of `requirements`, not a new set of assumptions: the
checked requirement bundle is retained unchanged in the detailed report and in the evidence
proposition. Presentation does the following. Duplicates are removed. A requirement is dropped
when `Verified.Expr.AutomaticSign` recognizes it syntactically as automatically nonzero or
positive, or when it is a nonzero requirement already implied by a listed positivity
requirement. Within a displayed product, factors recognized as automatically signed are
omitted. An entry `sqrt a` in the nonzero list is printed as `a > 0`, following the encoding
of positivity obligations in `NormResult.nonzero`. A nonzero condition `a / b ≠ 0` is printed as
`a ≠ 0` and `b ≠ 0`, and every sum as its polynomial over its atoms in descending powers
(`orderedSum`) when the sum equals that polynomial with no further condition: scaled
to integer coefficients with a positive leading coefficient in a nonzero condition, and by a
positive constant only, starting with a positive term, in a positivity condition.

`AutomaticSign` is a syntactic check, so a condition that is mathematically automatic but not
of a recognized shape (for instance an expanded sum of even powers with positive coefficients)
is still displayed.
-/
def renderConditions (reified : ReifiedExpr)
    (requirements :
      Verified.Expr.ValidityRequirements (Fin reified.names.length)) :
    Option String :=
  let allPositiveExpressions := requirements.positive.eraseDups
  let positiveExpressions :=
    allPositiveExpressions.filter
      (fun expression ↦ !Verified.Expr.AutomaticSign.positive expression)
  let nonzero :=
    requirements.nonzero.eraseDups
      |>.filter (fun expression ↦
        !Verified.Expr.AutomaticSign.nonzero expression &&
          !followsFromPositive allPositiveExpressions expression &&
          !(match expression with
            | .sqrt argument => Verified.Expr.AutomaticSign.positive argument
            | _ => false))
      |>.flatMap fun expression ↦
        match expression with
        | .sqrt argument =>
            let shown := orderedFactors true (positiveDisplayNormalForm argument)
            [s!"{renderExpr reified shown} > 0"]
        | _ => (nonzeroParts (nonzeroDisplayNormalForm expression)).map fun part ↦
            s!"{renderExpr reified (orderedFactors false part)} ≠ 0"
  let positive :=
    positiveExpressions
      |>.map fun expression ↦
      s!"{renderExpr reified (orderedFactors true (positiveDisplayNormalForm expression))} > 0"
  let conditions := (nonzero ++ positive).eraseDups
  if conditions.isEmpty then none else some ("; ".intercalate conditions)

private def combineRequirements {ι : Type*}
    (left right : Verified.Expr.ValidityRequirements ι) :
    Verified.Expr.ValidityRequirements ι where
  nonzero := left.nonzero ++ right.nonzero
  positive := left.positive ++ right.positive

/--
Requirements for the analytic Laplacian theorem.

Second partials require both validity of the original scalar expression and
validity of every first symbolic partial.
-/
def laplacianRequirements {n : Nat}
    (input : Verified.Expr (Fin n)) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  (List.finRange n).foldl
    (fun requirements coordinate ↦
      combineRequirements requirements
        (input.diff coordinate).validityRequirements)
    input.validityRequirements

/-- Render a checked validity-requirement bundle as a collapsed node. -/
def requirementsComputation (reified : ReifiedExpr) (label : String)
    (requirements :
      Verified.Expr.ValidityRequirements (Fin reified.names.length)) :
    MessageData :=
  computationNode label #[
    m!"Raw checked nonzero requirements: {renderExprList reified requirements.nonzero}",
    m!"Raw checked positivity requirements: {renderExprList reified requirements.positive}"
  ]

private def passKindLabel : Verified.Expr.PassKind → String
  | .checked => "checked"
  | .sideConditioned => "side-conditioned"

/-- Convert typed pipeline metadata into the planner-only report branch. -/
def passMetadata
    (pass : Verified.Expr.PassInfo) : PlannerExplanationStep where
  label := s!"{pass.phase.label}: {pass.name}"
  status := .attempted
  detail := passKindLabel pass.kind

/-- Validate all proof steps before constructing an InfoView evidence report. The steps
`validated`, checked already, come first. -/
def evidenceReportMessage
    (steps : Array UncheckedExplanationStep)
    (plannerMetadata : Array PlannerExplanationStep := #[])
    (validated : Array CheckedExplanationStep := #[]) :
    MetaM MessageData := do
  let checkedEvidence := validated ++ (← validateAll steps)
  let report : ExplanationReport := { checkedEvidence, plannerMetadata }
  Explanation.render report

/-- Pass a generated proof term to the shared kernel-checked evidence validator. -/
def proofStep
    (label : String) (theoremName : Name) (proof : Lean.Expr) :
    MetaM UncheckedExplanationStep :=
  UncheckedExplanationStep.ofProof label proof (some theoremName)

/-- Resolve a displayed coordinate name to its bounded expression index. -/
def coordinateAt (ref : Syntax) (reified : ReifiedExpr) (name : Name) :
    CommandElabM (Fin reified.names.length) := do
  let some coordinate := coordinateIndex? reified.names name
    | throwErrorAt ref
        "coordinate '{renderName name}' is absent from the reified expression"
  return coordinate

/--
Return the sole inferred coordinate of an expression.

Bare scalar operations use this check rather than assigning a meaning to an
ambiguous variable order. Named operations remain available for constants and
multivariate expressions.
-/
def uniqueCoordinate (ref : Syntax) (reified : ReifiedExpr) (help : String) :
    CommandElabM (Name × Fin reified.names.length) := do
  if reified.names.length != 1 then
    let detail :=
      if reified.names.isEmpty then
        "the expression has no variables"
      else
        s!"the expression has multiple variables: {renderNames reified.names}"
    throwErrorAt ref "{detail}; {help}"
  let some name := reified.names.head?
    | throwErrorAt ref "internal #cas error: missing univariate coordinate"
  return (name, ← coordinateAt ref reified name)

/-- Select the coordinate from its explicit name, lambda binder, or sole variable. -/
def scalarCoordinateInput (ref : Syntax) (name? : Option Name) (help : String) :
    CommandElabM (Σ reified : ReifiedExpr, Fin reified.names.length) := do
  let (reified, selected?) ← parseScalarInput ref name?
  let coordinate ←
    match selected? with
    | some name => coordinateAt ref reified name
    | none => Prod.snd <$> uniqueCoordinate ref reified help
  return ⟨reified, coordinate⟩

/-- A rational as term syntax `n`, `-n`, `n / d` or `-n / d`. -/
def ratSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) : m (TSyntax `term) := do
  let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let magnitude ← if q.den = 1 then pure numerator else
    let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
    `($numerator / $denominator)
  if q.num < 0 then `(-$magnitude) else pure magnitude

/-- A rational as an expression in one variable: a numeral, a fraction, or the negation of one. -/
def ratExpr (q : ℚ) : Verified.Expr (Fin 1) :=
  if q.den = 1 then (if 0 ≤ q.num then .nat q.num.toNat else .neg (.nat q.num.natAbs))
  else if 0 ≤ q.num then .rat q.num q.den else .neg (.rat (-q.num) q.den)

/-- Elaborate a statement and prove it with a tactic, returning the proof. -/
def proveWith (statement : TSyntax `term) (tactic : TSyntax `tactic) :
    CommandElabM Lean.Expr := liftTermElabM do
  let proposition ← Term.elabTerm statement none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let proof ← Term.withoutErrToSorry <| Term.elabTerm (← `(by $tactic:tactic)) (some proposition)
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

/-- Elaborate `statement`, then the term `proof` against it without error recovery, and return
the proof with `statement` as its type hint, so that a report keeps the statement as written. A
proof that still contains `sorry` fails with "`command`: a proof step failed". The kernel checks
the proof when the caller adds it to the environment. -/
def elabCheckedProof (command : String) (statement proof : TSyntax `term) :
    Term.TermElabM Lean.Expr := do
  let type ← Term.elabType statement
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← Term.withoutErrToSorry <| Term.elabTermEnsuringType proof type
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasSorry then throwError "{command}: a proof step failed"
  mkExpectedTypeHint value type

/-! ## Calculator expressions as Mathlib terms -/

private def numeralTerm (k : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩

/-- `exprTerm` with each variable `i` printed as `atom i`. -/
private partial def exprTermWith {ι : Type} (atom : ι → TermElabM (TSyntax `term))
    (expr : Verified.Expr ι) : TermElabM (TSyntax `term) := do
  let term (a : Verified.Expr ι) := exprTermWith atom a
  match expr with
  | .nat k => pure (numeralTerm k)
  | .int k => if k < 0 then `(-$(numeralTerm k.natAbs)) else pure (numeralTerm k.toNat)
  | .rat p q => ratSyntax ((p : ℚ) / q)
  | .pi => `(Real.pi)
  | .e => `(Real.exp 1)
  | .var i => atom i
  | .add a b => `($(← term a) + $(← term b))
  | .sub a b => `($(← term a) - ($(← term b)))
  | .neg a => `(-($(← term a)))
  | .mul a b => `(($(← term a)) * ($(← term b)))
  | .div a b => `(($(← term a)) / ($(← term b)))
  | .pow a k => `(($(← term a)) ^ $(numeralTerm k))
  | .sin a => `(Real.sin ($(← term a)))
  | .cos a => `(Real.cos ($(← term a)))
  | .atan a => `(Real.arctan ($(← term a)))
  | .asin a => `(Real.arcsin ($(← term a)))
  | .acos a => `(Real.arccos ($(← term a)))
  | .exp a => `(Real.exp ($(← term a)))
  | .log a => `(Real.log ($(← term a)))
  | .sqrt a => `(Real.sqrt ($(← term a)))
  | .rpow a b => `((($(← term a)) : ℝ) ^ (($(← term b)) : ℝ))

/-- A calculator expression as real term syntax over the given variables: `π` is `Real.pi`, `e`
is `Real.exp 1`, the functions are `Real.sin`, `Real.cos`, `Real.arctan`, `Real.arcsin`,
`Real.arccos`, `Real.exp`, `Real.log` and `Real.sqrt`, and `rpow a b` is `a ^ (b : ℝ)`. A subterm
that `function?` reads as a function of `DesugaredFunction` is the function's Mathlib constant
applied to the argument (`Real.tan a`, `|a|`, `Real.sinh a`). The term elaborates to a real number
whose value is `eval` of the expression at the variables, since each such function equals its form
(`DesugaredFunction.rewriteLemmas`). -/
partial def exprTerm {n : Nat} (vars : Fin n → TSyntax `term) (expr : Verified.Expr (Fin n))
    (function? : Verified.Expr (Fin n) → Option (DesugaredFunction × Verified.Expr (Fin n)) :=
      fun _ ↦ none) :
    TermElabM (TSyntax `term) :=
  let atom : Fin n ⊕ (DesugaredFunction × Verified.Expr (Fin n)) → TermElabM (TSyntax `term) :=
    fun
      | .inl i => pure (vars i)
      | .inr (function, argument) => do
          `($(mkCIdent function.constantName) ($(← exprTerm vars argument function?)))
  exprTermWith atom (foldFunctions function? expr)

/-- Every application of a function of `DesugaredFunction` in `tree` replaced by an atom carrying
the function and its argument. -/
private def atomizeApplications {ι κ : Type} :
    ReflectedExpr ι κ → ReflectedExpr (ι ⊕ (DesugaredFunction × ReflectedExpr ι κ)) κ
  | .nat value => .nat value
  | .rat num den => .rat num den
  | .constant value => .constant value
  | .coordinate index => .coordinate (.inl index)
  | .add lhs rhs => .add (atomizeApplications lhs) (atomizeApplications rhs)
  | .mul lhs rhs => .mul (atomizeApplications lhs) (atomizeApplications rhs)
  | .sub lhs rhs => .sub (atomizeApplications lhs) (atomizeApplications rhs)
  | .div lhs rhs => .div (atomizeApplications lhs) (atomizeApplications rhs)
  | .neg arg => .neg (atomizeApplications arg)
  | .pow base exponent => .pow (atomizeApplications base) exponent
  | .unary operation arg => .unary operation (atomizeApplications arg)
  | .apply function arg => .coordinate (.inr (function, arg))
  | .rpow base exponent => .rpow (atomizeApplications base) (atomizeApplications exponent)

/-- `tree` lowered to `Verified.Expr` as the reifier lowers the input. -/
private def lowerTree {ι : Type} (tree : ReflectedExpr ι Nat) : Option (Verified.Expr ι) :=
  Id.run <| tree.toVerifiedExprM? (fun index ↦ pure (some index))
    (fun exponent ↦ pure (some exponent))

/-- `tree` as real term syntax: each application of a function of `DesugaredFunction` is the
function's Mathlib constant applied to its argument, and the rest is printed as `exprTerm` prints
its lowering. -/
private partial def treeTerm {n : Nat} (vars : Fin n → TSyntax `term)
    (tree : ReflectedExpr (Fin n) Nat) : TermElabM (TSyntax `term) := do
  let some expr := lowerTree (atomizeApplications tree)
    | throwError "internal #cas error: the input does not lower to a calculator expression"
  let atom :
      Fin n ⊕ (DesugaredFunction × ReflectedExpr (Fin n) Nat) → TermElabM (TSyntax `term) :=
    fun
      | .inl i => pure (vars i)
      | .inr (function, argument) => do
          `($(mkCIdent function.constantName) ($(← treeTerm vars argument)))
  exprTermWith atom expr

/-- The input as real term syntax over the given variables, read occurrence by occurrence from the
input as written: each application of a function of `DesugaredFunction` is the function's Mathlib
constant applied to its argument (`Real.tan a`, `|a|`, `Real.sinh a`), and every other part is
printed as `exprTerm` prints it, so that a form of such a function that the user wrote out stays
written out. An input whose syntax is not recorded, or does not lower to `reified.expr`, is
printed by `exprTerm` with no function names. -/
def ReifiedExpr.inputTerm (reified : ReifiedExpr)
    (vars : Fin reified.names.length → TSyntax `term) : TermElabM (TSyntax `term) :=
  match reified.surface.tree? with
  | some tree =>
      if lowerTree tree == some reified.expr then treeTerm vars tree
      else exprTerm vars reified.expr
  | none => exprTerm vars reified.expr

/-- The hypotheses `0 < a` and `d ≠ 0` of a statement under `requirements`, as term syntax:
the conditions `renderConditions` displays, before its display normalization, so that each
hypothesis is literally a checked requirement (an entry `sqrt a` of the nonzero list becomes
`0 < a`). -/
def conditionTerms {n : Nat} (vars : Fin n → TSyntax `term)
    (requirements : Verified.Expr.ValidityRequirements (Fin n)) :
    TermElabM (Array (TSyntax `term)) := do
  let allPositive := requirements.positive.eraseDups
  let nonzero := requirements.nonzero.eraseDups.filter fun expression ↦
    !Verified.Expr.AutomaticSign.nonzero expression &&
      !followsFromPositive allPositive expression &&
      !(match expression with
        | .sqrt argument => Verified.Expr.AutomaticSign.positive argument
        | _ => false)
  let positive := allPositive.filter fun expression ↦
    !Verified.Expr.AutomaticSign.positive expression
  let conditions : List (Bool × Verified.Expr (Fin n)) :=
    (nonzero.map fun expression ↦
      match expression with
      | .sqrt argument => (true, argument)
      | expression => (false, expression)) ++ positive.map ((true, ·))
  conditions.eraseDups.toArray.mapM fun (isPositive, expression) ↦ do
    let term ← exprTerm vars expression
    if isPositive then `((0 : ℝ) < $term) else `(($term : ℝ) ≠ 0)

/-- The statement `∀ vars : ℝ, c₀ → c₁ → … → body`. -/
def realForallStatement (vars : Array (TSyntax `ident)) (conditions : Array (TSyntax `term))
    (body : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut statement := body
  for condition in conditions.reverse do
    statement ← `($condition → $statement)
  if vars.isEmpty then return statement
  `(∀ $vars* : ℝ, $statement)

/-- The coordinate names of a reified expression as binder identifiers and as terms. -/
def coordinateIdents (reified : ReifiedExpr) :
    Array (TSyntax `ident) × (Fin reified.names.length → TSyntax `term) :=
  let idents := reified.names.toArray.map mkIdent
  (idents, fun i ↦ mkIdent (reified.names.get i))

/-! ## Mathlib terms in the calculator printer -/

/-- A natural numeral: `OfNat.ofNat _ k _` or a raw literal. -/
private def natNumeral? (e : Lean.Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal k) => some k
  | e =>
      if e.isAppOfArity ``OfNat.ofNat 3 then
        match (e.getArg! 1).consumeMData with
        | .lit (.natVal k) => some k
        | _ => none
      else none

/-- A connective whose operand needs parentheses inside another connective. -/
private def isConnective (p : Lean.Expr) : Bool :=
  p.isAppOfArity ``Or 2 || p.isAppOfArity ``And 2 || p.isAppOfArity ``Iff 2

/-- The type of a subtraction, a division or a remainder whose value is not the real one, as a
typed group prints it: `ℕ` for a subtraction, a division or a remainder in `ℕ`, `ℤ` for a division
or a remainder in `ℤ`. `division` is `true` for `/` and `%`. -/
private def truncatingType? (type : Lean.Expr) (division : Bool) : Option String :=
  match type.consumeMData with
  | .const ``Nat [] => some "ℕ"
  | .const ``Int [] => if division then some "ℤ" else none
  | _ => none

/-- The atom `termDisplay` reads `Complex.I` as. -/
private def imaginaryUnit : Verified.Expr String := .var "i"

/-- Whether the calculator printer prints one of its own constants as `name` (`pi`, `e`, `i`) or
one of its own functions as `name(…)` (`sin`, `cos`, `atan`, `asin`, `acos`, `exp`, `log`,
`sqrt`), as `renderWith` prints them. -/
private def printerName (name : String) : Bool :=
  let x : Verified.Expr String := .var "x"
  ([.pi, .e, imaginaryUnit, .sin x, .cos x, .atan x, .asin x, .acos x, .exp x, .log x, .sqrt x] :
      List (Verified.Expr String)).any fun own ↦
    own.renderWith id == name || own.renderWith id == s!"{name}(x)"

/-- Whether the real term `a` is positive by its form: a positive numeral, `π`, an `exp`, or a sum,
product, quotient, power, `⁻¹` or `sqrt` of terms positive by their form. -/
private partial def positiveByForm (a : Lean.Expr) : Bool :=
  if let some k := natNumeral? a then k != 0 else
  match a.consumeMData.getAppFnArgs with
  | (``Real.pi, #[]) | (``Real.exp, #[_]) => true
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) | (``HMul.hMul, #[_, _, _, _, x, y])
  | (``HDiv.hDiv, #[_, _, _, _, x, y]) => positiveByForm x && positiveByForm y
  | (``HPow.hPow, #[_, _, _, _, x, _]) | (``Inv.inv, #[_, _, x]) | (``Real.sqrt, #[x]) =>
      positiveByForm x
  | _ => false

/-- Whether the real term `a` contains, outside binders, a function whose complex reading under
`Complex.ofReal` may have another value: `log`, `sqrt` or a power with a real exponent
(`Complex.cpow`) of a term that is not positive by its form (`positiveByForm`), since they differ
at negative numbers, and `arcsin` and `arccos`, which differ outside `[-1, 1]`. -/
private partial def complexReadingDiffers (a : Lean.Expr) : Bool :=
  match a.consumeMData.getAppFnArgs with
  | (``Real.log, #[x]) | (``Real.sqrt, #[x]) => !positiveByForm x || complexReadingDiffers x
  | (``Real.arcsin, _) | (``Real.arccos, _) => true
  | (``HPow.hPow, #[_, exponentType, _, _, base, exponent]) =>
      (exponentType.consumeMData.isConstOf ``Real && (natNumeral? exponent).isNone &&
          !positiveByForm base) ||
        complexReadingDiffers base || complexReadingDiffers exponent
  | (_, args) => args.any complexReadingDiffers

mutual

/--
Read a Mathlib real or complex term as a calculator expression over display names.

Numerals, the casts `Nat.cast`, `Int.cast`, `Rat.cast` and `Complex.ofReal`, `+`, `-`, `*`, `/`,
negation, `⁻¹` (as `1/a`), powers (a numeral exponent is `pow`, any other `rpow`), `Real.pi`,
`Real.exp 1` (as `e`), the real and complex `exp`, `sin`, `cos`, `log`, and `arctan`, `arcsin`,
`arccos`, `sqrt` are read; `Complex.I` is the atom `i` and a free variable the atom of its name,
with Lean's escapes when the name is not an identifier (`«n-m»`). `|a|` and `if c then a else b`
are atoms printed by the same printer, any other application of a constant prints as
`name(arguments)` with the explicit arguments and the last component of the name, escaped as Lean
escapes it (`sinh(x)`, `Gamma(x)`, `«a-b»`), or with the full name when the calculator printer
prints one of its own functions or constants under that component (`Nat.sqrt(8)`, see
`printerName`), and any other subterm by `ppExpr`.

A cast is dropped, since every operation read under it means the same in the target type: a
subtraction in `ℕ` and a division or a remainder in `ℕ` or `ℤ` are read as one atom, a typed group
such as `(n - (m - k) : ℕ)`, `(a/b : ℤ)` or `(a%b : ℕ)`, and a real term under `Complex.ofReal`
as `(… : ℝ)` when it contains a function whose complex reading may take another value (`log(x)`,
`sqrt(x)` or `x^y` with a real exponent `y`, where `x` is not positive by its form, and `arcsin`,
`arccos`). `groupText` prints the inside of every group.
-/
partial def termDisplay (e : Lean.Expr) : MetaM (Verified.Expr String) := do
  let e := (← instantiateMVars e).consumeMData
  if let some k := natNumeral? e then return .nat k
  if let .fvar id := e then
    return .var (toString (← id.getUserName).eraseMacroScopes)
  let group (type? : Option String) (shown : MetaM (Verified.Expr String)) :
      MetaM (Verified.Expr String) := do
    match type? with
    | some type => return .var s!"({← groupText type e} : {type})"
    | none => shown
  let application : MetaM (Verified.Expr String) := do
    let (name, args) := e.getAppFnArgs
    if e.getAppFn.isConst then
      let info ← getFunInfoNArgs e.getAppFn args.size
      let mut shown : Array String := #[]
      for k in [:args.size] do
        if info.paramInfo[k]?.all (·.binderInfo.isExplicit) then
          shown := shown.push (← renderTerm args[k]!)
      let name := Lean.privateToUserName name
      let function := match name with
        | .str pre last =>
            if !printerName last then (Name.mkSimple last).toString
            else if pre.isAnonymous then s!"_root_.{name}"
            else name.toString
        | _ => name.toString
      return .var (if shown.isEmpty then function
        else function ++ "(" ++ ", ".intercalate shown.toList ++ ")")
    let printed := toString (← ppExpr e)
    return .var (if printed.contains ' ' then s!"({printed})" else printed)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← termDisplay a) (← termDisplay b)
  | (``HSub.hSub, #[type, _, _, _, a, b]) =>
      group (truncatingType? type false) do return .sub (← termDisplay a) (← termDisplay b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← termDisplay a) (← termDisplay b)
  | (``HDiv.hDiv, #[type, _, _, _, a, b]) =>
      group (truncatingType? type true) do return .div (← termDisplay a) (← termDisplay b)
  | (``HMod.hMod, #[type, _, _, _, _, _]) => group (truncatingType? type true) application
  | (``Neg.neg, #[_, _, a]) => return .neg (← termDisplay a)
  | (``Inv.inv, #[_, _, a]) => return .div (.nat 1) (← termDisplay a)
  | (``HPow.hPow, #[_, _, _, _, a, b]) =>
      match natNumeral? b with
      | some k => return .pow (← termDisplay a) k
      | none => return .rpow (← termDisplay a) (← termDisplay b)
  | (``Nat.cast, #[_, _, a]) | (``Int.cast, #[_, _, a]) | (``Rat.cast, #[_, _, a]) =>
      termDisplay a
  | (``Complex.ofReal, #[a]) =>
      if complexReadingDiffers a then return .var s!"({← groupText "ℝ" a} : ℝ)"
      else termDisplay a
  | (``Zero.zero, #[_, _]) => return .nat 0
  | (``One.one, #[_, _]) => return .nat 1
  | (``Real.pi, #[]) => return .pi
  | (``Real.exp, #[a]) =>
      if natNumeral? a == some 1 then return .e else return .exp (← termDisplay a)
  | (``Complex.exp, #[a]) => return .exp (← termDisplay a)
  | (``Real.sin, #[a]) | (``Complex.sin, #[a]) => return .sin (← termDisplay a)
  | (``Real.cos, #[a]) | (``Complex.cos, #[a]) => return .cos (← termDisplay a)
  | (``Real.log, #[a]) | (``Complex.log, #[a]) => return .log (← termDisplay a)
  | (``Real.arctan, #[a]) => return .atan (← termDisplay a)
  | (``Real.arcsin, #[a]) => return .asin (← termDisplay a)
  | (``Real.arccos, #[a]) => return .acos (← termDisplay a)
  | (``Real.sqrt, #[a]) => return .sqrt (← termDisplay a)
  | (``Complex.I, #[]) => return imaginaryUnit
  | (``abs, #[_, _, _, a]) => return .var s!"|{← renderTerm a}|"
  | (``ite, #[_, _, _, _, _]) => return .var s!"({← renderTerm e})"
  | _ => application

/--
The text of the typed group `(… : type)` around the term `e`, read at the level `context`: the
operator tree of `e` written as Lean reads it, so that the text elaborates to the same tree. `+`
and `-` are at level 65 and print with spaces, `*`, `/` and `%` at level 70 and print without,
each with its left operand at its own level and its right operand one level above, so that a right
operand of the same level keeps its parentheses (`(1 + (2 - 3) - 0 : ℕ)`, `(2*(3/2)/1 : ℕ)`); `^`
is at level 80 with its base one level above. A negation is read at level 70 with its operand at
71, which parenthesizes it as the right operand of `*`, `/`, `%` and `^` and under another
negation, since a minus sign right after `/` or `-` would start a comment. `⁻¹` prints as `1/a`,
as `termDisplay` reads it.

A cast is dropped inside the group, and an operation of another type prints in the group unless it
is a subtraction, a division or a remainder with a typed group of another type, which is a group of
its own (`((n - m : ℕ)/k : ℤ)`). Every other subterm is one atom, printed by `termDisplay` and the
display normal form as `renderTerm` prints it, so no rule of real arithmetic reaches the
operations of the group.
-/
partial def groupText (type : String) (e : Lean.Expr) (context : Nat := 0) : MetaM String := do
  let e := (← instantiateMVars e).consumeMData
  let operation (level : Nat) (leftAssociative : Bool) (symbol : String) (a b : Lean.Expr) :
      MetaM String := do
    let (left, right) := if leftAssociative then (level, level + 1) else (level + 1, level)
    return Verified.Expr.parenIf (decide (level < context))
      s!"{← groupText type a left}{symbol}{← groupText type b right}"
  let inGroup (carrier : Lean.Expr) (division : Bool) : Bool :=
    (truncatingType? carrier division).all (· == type)
  let atom : MetaM String := do
    return (Verified.Expr.displayNormalForm (← termDisplay e)).renderWith id
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => operation 65 true " + " a b
  | (``HSub.hSub, #[carrier, _, _, _, a, b]) =>
      if inGroup carrier false then operation 65 true " - " a b else atom
  | (``HMul.hMul, #[_, _, _, _, a, b]) => operation 70 true "*" a b
  | (``HDiv.hDiv, #[carrier, _, _, _, a, b]) =>
      if inGroup carrier true then operation 70 true "/" a b else atom
  | (``HMod.hMod, #[carrier, _, _, _, a, b]) =>
      if inGroup carrier true then operation 70 true "%" a b else atom
  | (``HPow.hPow, #[_, _, _, _, a, b]) => operation 80 false "^" a b
  | (``Neg.neg, #[_, _, a]) =>
      return Verified.Expr.parenIf (decide (70 < context)) s!"-{← groupText type a 71}"
  | (``Inv.inv, #[_, _, a]) =>
      return Verified.Expr.parenIf (decide (70 < context)) s!"1/{← groupText type a 71}"
  | (``Nat.cast, #[_, _, a]) | (``Int.cast, #[_, _, a]) | (``Rat.cast, #[_, _, a]) =>
      groupText type a context
  | _ => atom

/-- Print a Mathlib real or complex term with the calculator printer: `termDisplay`, then
`displayNormalForm` and `renderWith`, as `renderExpr` prints a calculator expression. -/
partial def renderTerm (e : Lean.Expr) : MetaM String := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFnArgs with
  | (``ite, #[_, c, _, a, b]) =>
      return s!"if {← renderProp c} then {← renderTerm a} else {← renderTerm b}"
  | _ => return (Verified.Expr.displayNormalForm (← termDisplay e)).renderWith id

/-- Print a proposition built from `=`, `≠`, `<`, `≤`, `>`, `≥`, `∧`, `∨`, `↔`, `¬`, `True` and
`False` over real or complex terms, the terms by `renderTerm`. -/
partial def renderProp (p : Lean.Expr) : MetaM String := do
  let p := (← instantiateMVars p).consumeMData
  let relation (symbol : String) (a b : Lean.Expr) : MetaM String :=
    return s!"{← renderTerm a} {symbol} {← renderTerm b}"
  let operand (q : Lean.Expr) : MetaM String := do
    let text ← renderProp q
    return if isConnective q then s!"({text})" else text
  match p.getAppFnArgs with
  | (``Eq, #[_, a, b]) => relation "=" a b
  | (``Ne, #[_, a, b]) => relation "≠" a b
  | (``LT.lt, #[_, _, a, b]) => relation "<" a b
  | (``LE.le, #[_, _, a, b]) => relation "≤" a b
  | (``GT.gt, #[_, _, a, b]) => relation ">" a b
  | (``GE.ge, #[_, _, a, b]) => relation "≥" a b
  | (``Or, #[a, b]) =>
      let right ← if b.isAppOfArity ``Iff 2 then operand b else renderProp b
      return s!"{← operand a} ∨ {right}"
  | (``And, #[a, b]) =>
      let right ← if b.isAppOfArity ``And 2 then renderProp b else operand b
      return s!"{← operand a} ∧ {right}"
  | (``Iff, #[a, b]) => return s!"{← operand a} ↔ {← operand b}"
  | (``Not, #[a]) => return s!"¬({← renderProp a})"
  | (``True, #[]) => return "True"
  | (``False, #[]) => return "False"
  | _ => return toString (← ppExpr p)

end

/-- `q * a` in the calculator printer, with the denominator of `q` last: `3*sqrt(pi)/4`,
`-sqrt(pi)`, `pi^2/6`. -/
def rationalMultipleText (q : ℚ) (a : Verified.Expr String) : String :=
  let numerator : Verified.Expr String :=
    if q.num = 1 then a
    else if q.num = -1 then .neg a
    else if q.num < 0 then .mul (.int q.num) a
    else .mul (.nat q.num.toNat) a
  (if q.den = 1 then numerator else .div numerator (.nat q.den)).renderWith id

end CAS.Command
