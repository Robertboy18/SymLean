/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.ProofCarrier
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.Meta.Tactic.Simp.SimpCongrTheorems
import Mathlib.Algebra.Ring.Basic

/-!
# Checked tactic explanations

Tactic explanations separate checked evidence from everything else. A
`CheckedExplanationStep` can only be constructed by validating a proposition
and proof in `MetaM`, or from the shared proof carrier after it has performed
its own checks. Planner metadata is represented separately. It may explain search and route
selection, but it is never accepted as mathematical evidence.

## Main definitions

* `UncheckedExplanationStep`, `CheckedExplanationStep`: proposed and checked evidence;
  `UncheckedExplanationStep.validate` and `CheckedExplanationStep.ofClosedMainGoal` build the
  checked steps.
* `PlannerExplanationStep`: planner metadata.
* `ExplanationReport`: the checked evidence and the planner metadata of a report.

## Implementation notes

Validation instantiates assigned metavariables, rejects
unresolved metavariables and direct or transitively referenced placeholder
evidence, and checks that the narrated expression is a proposition. For
explicit proposed evidence the kernel then checks the proof term against that
proposition by adding the pair to the environment as an
auxiliary theorem. The kernel checks the proposition itself at the same time.
Reflection and decision steps inside the proof or the proposition are thus
evaluated by the kernel, never by the elaborator's `whnf`, so large
certificates are validated the same way an ordinary theorem would be. Before
the check, validation writes `a + -b` as `a - b` and `a - -b` as `a + b` in the
proposition and adds the rewrite to the proof, so that a report prints in
conventional form exactly the proposition the kernel checks.

A completed tactic goal instead reuses the elaborator's validation. Its report
records this distinction: the kernel checks that proof when the enclosing
declaration is accepted. Such a step states the goal as written, signs
included: its proof is the one the declaration hands to the kernel, and a
tidied statement would need a proof of its own that no check covers.

A report prints a proposition as the pretty-printer does, with the base and the
exponent of each power whose exponent is not a natural number marked to print
with their type when they are closed numeric terms, the powers inside such a
term included (`showPowerTypes`).
-/

public meta section

namespace CAS.Tactic.Explanation

open Lean Meta

/--
Unvalidated evidence proposed by a tactic or command.

The optional theorem name is diagnostic attribution. The proof expression,
rather than this name, is the evidence checked by `validate`.
-/
structure UncheckedExplanationStep where
  /-- Human-readable description of the proposed evidence. -/
  label : String
  /-- The proposition that the step claims to prove. -/
  proposition : Expr
  /-- The unvalidated proof term proposed for `proposition`. -/
  proof : Expr
  /-- Optional declaration credited as the source of the proof. -/
  theoremName? : Option Name := none

/-- Which checker has already accepted the evidence at report construction time. -/
inductive EvidenceValidation where
  /-- An auxiliary theorem has been synchronously accepted by the kernel. -/
  | kernel
  /-- The elaborator checked the completed goal; declaration kernel checking is pending. -/
  | elaborator
deriving DecidableEq, Repr

/--
Evidence whose proof term has been checked against its narrated proposition.

The constructor is private so every value displayed as checked evidence must
pass through `UncheckedExplanationStep.validate` or originate from a
`ProofCarrier.ClosedMainGoal`.
-/
structure CheckedExplanationStep where
  private mk ::
  /-- Human-readable description of the validated evidence. -/
  label : String
  /-- The proposition against which the proof term was checked. -/
  proposition : Expr
  /-- The type-correct proof term for `proposition`. -/
  proof : Expr
  /-- Optional declaration credited as the source of the proof. -/
  theoremName? : Option Name
  /-- The check already performed, distinguished from eventual declaration checking. -/
  validation : EvidenceValidation

/-- Status attached to diagnostic planner metadata. -/
inductive PlannerExplanationStatus where
  | attempted
  | succeeded
  | selected
deriving DecidableEq, Repr

namespace PlannerExplanationStatus

/-- Stable user-facing label for a planner status. -/
def label : PlannerExplanationStatus → String
  | .attempted => "attempted"
  | .succeeded => "succeeded"
  | .selected => "selected"

end PlannerExplanationStatus

/--
One diagnostic fact about tactic planning or route selection.

These fields carry no proof and must only be rendered under a section marked
as metadata.
-/
structure PlannerExplanationStep where
  /-- Human-readable description of the planner event. -/
  label : String
  /-- The outcome of the planner event. -/
  status : PlannerExplanationStatus
  /-- Optional diagnostic detail carrying no mathematical evidence. -/
  detail : String := ""

/--
A checked explanation report and its separate, non-proving planner metadata.
-/
structure ExplanationReport where
  /-- Validated mathematical evidence displayed by the report. -/
  checkedEvidence : Array CheckedExplanationStep := #[]
  /-- Non-proving diagnostics about search and route selection. -/
  plannerMetadata : Array PlannerExplanationStep := #[]

/--
Turn an existing proof term into proposed explanation evidence.

The inferred proposition is not trusted by this constructor. Callers must
still invoke `UncheckedExplanationStep.validate` before displaying the step as
checked evidence.
-/
def UncheckedExplanationStep.ofProof
    (label : String) (proof : Expr) (theoremName? : Option Name := none) :
    MetaM UncheckedExplanationStep := do
  return {
    label
    proposition := ← inferType proof
    proof
    theoremName?
  }

private def rejectMVars (label kind : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar then
    throwError "cannot report {label} as checked evidence: \
      {kind} contains unresolved metavariables{indentExpr e}"

private def rejectPlaceholders (label kind : String) (e : Expr) : MetaM Unit := do
  if e.hasSorry then
    throwError "cannot report {label} as checked evidence: {kind} contains placeholder evidence"
  ProofCarrier.rejectIncompleteDependencies
    s!"cannot report {label} as checked evidence: {kind}" e

/--
Have the kernel check `proof` against `proposition` by adding an auxiliary
theorem to the environment, and return that theorem as a proof of
`proposition`.

Free variables of the current local context are abstracted first, so evidence
stated inside a tactic proof may mention hypotheses; let-bound variables are
substituted. Asynchronous checking is disabled for the addition so that a
kernel rejection surfaces here, prefixed by `description`, rather than as a
later diagnostic. Every call adds its own theorem: the proof term supplied by
the caller is what gets checked, not a cached proof of the same statement. The
theorem is not entered into the auxiliary-lemma cache either, since the evidence
may depend on a native certificate (`ProofCarrier.addUncachedTheorem`).

Reflection steps such as `decide` proofs inside `proof` are evaluated by the
kernel alone. Callers that embed one large reflection step in several
displayed steps should check it once with this function and reuse the returned
constant, so the kernel evaluates it once.
-/
def kernelCheckedProof (description : String) (proposition proof : Expr) : MetaM Expr := do
  try
    -- With `zetaDelta` the closure step substitutes let-bound variables instead
    -- of running the elaborator's type checker to decide which ones are needed;
    -- that checker would otherwise evaluate reflection steps by `whnf`.
    withOptions (Elab.async.set · false) do
      let closure ← Closure.mkValueTypeClosure proposition proof (zetaDelta := true)
      -- Qualify the auxiliary name by the current module: `#cas` runs outside any
      -- declaration, and two modules that both run it must not clash on import.
      let name ← ProofCarrier.runKernelCheck description
        (ProofCarrier.addUncachedTheorem closure.levelParams.toList closure.type closure.value
          ((← getMainModule) ++ `_evidence))
        fun error ↦ throw error
      return mkAppN (mkConst name closure.levelArgs.toList) closure.exprArgs
  catch error =>
    throwError "{description}: the kernel rejected the proof term for the stated \
      proposition{indentD error.toMessageData}"

/-- Whether `e` is a negation, or a product or quotient whose left operand is negation-led. -/
private partial def isNegationLed (e : Expr) : Bool :=
  e.isAppOfArity ``Neg.neg 3 ||
    ((e.isAppOfArity ``HMul.hMul 6 || e.isAppOfArity ``HDiv.hDiv 6) && isNegationLed (e.getArg! 4))

/-- Whether `e` is a sum `a + t` or a difference `a - t` whose right operand `t` is
negation-led. -/
private def isSignedSum (e : Expr) : Bool :=
  (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6) && isNegationLed (e.getArg! 5)

/-- For a negation-led `e`, the term `u` with a proof of `e = -u`: `-b` gives `b`, `-b * c` gives
`b * c` (`neg_mul`) and `-b / c` gives `b / c` (`neg_div`). -/
private partial def negatedTerm? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if e.isAppOfArity ``Neg.neg 3 then return some (e.appArg!, ← mkEqRefl e)
  let product := e.isAppOfArity ``HMul.hMul 6
  unless product || e.isAppOfArity ``HDiv.hDiv 6 do return none
  let some (first, hfirst) ← negatedTerm? (e.getArg! 4) | return none
  let second := e.getArg! 5
  let operation := e.appFn!.appFn!
  let unsigned := mkApp2 operation first second
  let distributed ← if product then mkAppM ``neg_mul #[first, second]
    else mkAppM ``neg_div #[second, first]
  let proof ← mkEqTrans (← mkCongrFun (← mkCongrArg operation hfirst) second) distributed
  return some (unsigned, ← mkExpectedTypeHint proof (← mkEq e (← mkAppM ``Neg.neg #[unsigned])))

/-- The simplification step writing `a + -b` as `a - b` (`sub_eq_add_neg`) and `a - -b` as
`a + b` (`sub_neg_eq_add`), also when the negation leads a product or a quotient. A type without
the instances these lemmas need is left as it is. -/
private def tidySign (e : Expr) : Simp.SimpM Simp.Step := do
  unless isSignedSum e do return .continue
  let sum := e.isAppOfArity ``HAdd.hAdd 6
  try
    let some (b, hb) ← negatedTerm? (e.getArg! 5) | return .continue
    let a := e.getArg! 4
    let target ← mkAppM (if sum then ``HSub.hSub else ``HAdd.hAdd) #[a, b]
    let rewrite ← if sum then mkEqSymm (← mkAppM ``sub_eq_add_neg #[a, b])
      else mkAppM ``sub_neg_eq_add #[a, b]
    let proof ← mkEqTrans (← mkCongrArg e.appFn! hb) rewrite
    return .visit { expr := target, proof? := some (← mkExpectedTypeHint proof (← mkEq e target)) }
  catch _ =>
    return .continue

/-- The proposition `p` with every `a + -b` written `a - b` and every `a - -b` written `a + b`,
where the negation may lead a product or a quotient, together with a proof of the equation of
`p` with it when the rewrite changed `p`. -/
def tidySigns (p : Expr) : MetaM (Expr × Option Expr) := do
  unless (p.find? isSignedSum).isSome do return (p, none)
  let context ← Simp.mkContext
    { zeta := false, beta := false, eta := false, etaStruct := .none, iota := false,
      proj := false, decide := false, arith := false, dsimp := false, ground := false,
      failIfUnchanged := false, autoUnfold := false }
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Simp.main p context (methods := { post := tidySign })
  return (result.expr, result.proof?)

/-- Whether `e` is a closed numeric term: a numeral `OfNat.ofNat`, a raw natural literal or a
scientific literal, or a negation, sum, difference, product, quotient or power of closed numeric
terms, or a cast `Nat.cast`, `Int.cast` or `Rat.cast` of one, each possibly under metadata (simp
leaves `no_index` marks on the numerals it rewrites). -/
private partial def isNumeralTerm (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isRawNatLit || e.isAppOfArity ``OfNat.ofNat 3 ||
    e.isAppOfArity ``OfScientific.ofScientific 5 ||
    (e.isAppOfArity ``Neg.neg 3 && isNumeralTerm e.appArg!) ||
    ((e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``Int.cast 3 ||
        e.isAppOfArity `Rat.cast 3) && isNumeralTerm e.appArg!) ||
    ((e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 ||
        e.isAppOfArity ``HMul.hMul 6 || e.isAppOfArity ``HDiv.hDiv 6 ||
        e.isAppOfArity ``HPow.hPow 6) &&
      isNumeralTerm (e.getArg! 4) && isNumeralTerm (e.getArg! 5))

/-- The term `e` marked so that the delaborator prints it with its type, as `(e : α)`. -/
private def withTypeShown (e : Expr) : Expr :=
  mkMData (KVMap.empty.insert `pp.analysis.needsType (.ofBool true)) e

/-- The proposition `p` with the base and the exponent of each power `a ^ b` whose exponent `b`
is not a natural number marked to print with their type when they are closed numeric terms
(`isNumeralTerm`), as in `x ^ (2 / 3 : ℝ)` and `x ^ (2 ^ 2 / 3 ^ 2 : ℝ)`: a pasted `x ^ (2 / 3)`
would be a natural power. The powers inside a marked term are marked too, as in
`x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ)`, since the type of the term does not fix the type of an exponent
inside it. Powers with a natural exponent and all other numerals are left as they are. The marks
are metadata, which the kernel and definitional equality ignore. -/
partial def showPowerTypes (p : Expr) : Expr :=
  p.replace fun e ↦
    if e.isAppOfArity ``HPow.hPow 6 && !(e.getArg! 1).consumeMData.isConstOf ``Nat then
      let shown (operand : Expr) : Expr :=
        let inner := showPowerTypes operand
        if isNumeralTerm operand then withTypeShown inner else inner
      some (mkAppN e.getAppFn
        #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3, shown (e.getArg! 4),
          shown (e.getArg! 5)])
    else none

/--
Validate a proposed explanation step before it can be displayed as checked
evidence.

The proof term is checked by the kernel against the narrated proposition, so
the validation is exactly as strong as the check a theorem receives when it is
added to the environment. The checked step states the proposition with
`tidySigns` applied, and its proof is the given proof transported along that
rewrite. It rejects placeholder axioms reached through
referenced declarations. Beyond that it is relative to the current environment
and local context: it does not record why the planner selected this proof, and
it does not inspect the other axioms of declarations referenced by the proof.
-/
def UncheckedExplanationStep.validate
    (step : UncheckedExplanationStep) : MetaM CheckedExplanationStep := do
  -- Maximal sharing of the proposition and the proof together, with the primitive that Lean uses
  -- to prepare definitions for the kernel (`Lean.Elab.shareCommonPreDefs`).
  let (proposition, proof) :=
    ShareCommon.shareCommon' (← instantiateMVars step.proposition, ← instantiateMVars step.proof)

  rejectMVars step.label "proposition" proposition
  rejectMVars step.label "proof" proof
  rejectPlaceholders step.label "proposition" proposition
  rejectPlaceholders step.label "proof" proof
  -- The type of the proof can reach placeholder evidence that neither the
  -- proposition nor the proof term mentions, for example through the type of a
  -- local hypothesis. Inferring the type does not type-check the proof, so it evaluates none of
  -- its reflection steps.
  let proofType ← instantiateMVars (← inferType proof)
  rejectMVars step.label "proof type" proofType
  rejectPlaceholders step.label "proof type" proofType

  unless ← isProp proposition do
    throwError "cannot report {step.label} as checked evidence: \
      narrated expression is not a proposition"

  -- The step states the proposition with its signs tidied, and its proof carries the rewrite,
  -- so that the kernel checks the statement as the report prints it.
  let (proposition, proof) ← do
    let (tidied, equation?) ← tidySigns proposition
    match equation? with
    | some equation => pure (tidied, ← mkExpectedTypeHint (← mkEqMP equation proof) tidied)
    | none => pure (tidied, proof)

  discard <| kernelCheckedProof
    s!"cannot report {step.label} as checked evidence" proposition proof

  if let some theoremName := step.theoremName? then
    unless (← getEnv).contains theoremName do
      throwError "cannot report {step.label} as checked evidence: \
        unknown theorem name {theoremName}"

  return .mk step.label proposition proof step.theoremName? .kernel

/--
Turn a proof already accepted by the shared tactic proof carrier into
reportable evidence without re-checking the same potentially large proof a
second time; the kernel checks that proof when the enclosing declaration is
added.

`ProofCarrier.ClosedMainGoal` has a private constructor and is produced only
after the assigned proof is complete, type-correct, and definitionally equal
to the original target. The step states that target as written, without
`tidySigns`: its proof is the one the declaration hands to the kernel, and a
tidied statement would need a transported proof that neither this step nor the
declaration checks. The optional theorem name remains diagnostic attribution
and is checked against the current environment.
-/
def CheckedExplanationStep.ofClosedMainGoal {α : Type}
    (label : String) (closed : ProofCarrier.ClosedMainGoal α)
    (theoremName? : Option Name := none) : MetaM CheckedExplanationStep := do
  if let some theoremName := theoremName? then
    unless (← getEnv).contains theoremName do
      throwError "cannot report {label} as checked evidence: unknown theorem name {theoremName}"
  return .mk label closed.target closed.proof theoremName? .elaborator

/-- Validate several evidence steps, stopping at the first rejected step. -/
def validateAll
    (steps : Array UncheckedExplanationStep) : MetaM (Array CheckedExplanationStep) :=
  steps.mapM (·.validate)

end CAS.Tactic.Explanation
