/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Rational
public meta import CAS.Expr.AutomaticSign
public meta import CAS.Tactic.ProofCarrier
public import CAS.Expr.Serialization
public meta import CAS.Expr.Serialization

/-!
# Kernel evaluation and read-back of checked expression data

The exact tactics compute checked data (normal forms, side-condition lists, antiderivative
candidates, requirement collections) by running the closed-form normalizers. The derivative,
identity, integration, and semantic routes evaluate such a value in the kernel, decode it in
compiled code, and certify the statement built from it by one kernel-checked decision.

## Main definitions

* `kernelWhnf` reduces a closed term with the kernel's evaluator;
* `readBackExpression`, `readBackList`, `readBackRun`, and `readBackRequirements` evaluate a
  checked value in one kernel reduction through `Verified.Expr.Serial` and decode the result in
  compiled code;
* `quoteNatExpression` and `quoteNatList` quote the decoded data back as terms over a `Fin`
  index type;
* `decideByKernel` certifies a decidable statement as `decide +kernel` does, so that the kernel,
  not the elaborator, evaluates the checked computation once more for the proof.

## Implementation notes

We evaluate each value in one kernel reduction because the two other ways of obtaining it are
far too slow: the elaborator's `whnf`, whose unfolding of a normalizer run costs seconds where
the kernel needs milliseconds, and a node-by-node kernel read-back, which restarts the
evaluation for every node. Nothing read back here is trusted: a decoded value only shapes the
statement that `decideByKernel` then certifies, and a decoding failure only makes the tactic
fail. The proof is that of core's `decide +kernel` (`Lean.Elab.Tactic.evalDecideCore`),
`of_decide_eq_true` applied to `Eq.refl true` and stored as an auxiliary lemma; ours are the
axiom policy of the lemma cache, the heartbeat budget of the check and the failure report.

`Lean.Kernel.whnf` takes no heartbeat budget and cannot be interrupted. Its allocations still
advance the heartbeat counter of the elaborating thread, so `kernelWhnf` charges each evaluation
to the declaration when it returns and stops with a timeout once `maxHeartbeats` is exceeded,
instead of starting the next evaluation; callers bound the size of what they evaluate. The kernel
check in `decideByKernel` is an `addDecl`, given what is left of the declaration's budget
(`ProofCarrier.runKernelCheck`).
-/

public meta section

namespace CAS.Tactic.KernelReadBack

open Lean Elab Tactic Meta

/--
Run a tactic on a goal from `MetaM` with error recovery disabled, so that a failing step
raises an exception instead of admitting a goal. Any assignment containing `sorry` is
rejected as a failure.
-/
def runTacticOnGoal (goal : MVarId) (tactic : TSyntax `tactic) : MetaM (List MVarId) := do
  let remaining ←
    Term.TermElabM.run' (ctx := { errToSorry := false }) do
      Tactic.run goal (Tactic.withoutRecover (Tactic.evalTactic tactic))
  let assignment ← instantiateMVars (mkMVar goal)
  if assignment.hasSorry then
    throwError "a tactic step admitted a goal"
  return remaining

/-- Run a `MetaM` action, discarding any messages it logs. -/
def withSuppressedMessagesMeta {α : Type} (action : MetaM α) : MetaM α := do
  let saved := (← getThe Core.State).messages
  try
    action
  finally
    modifyThe Core.State fun state ↦ { state with messages := saved }

/-- Reduce a closed term to weak head normal form with the kernel's evaluator, and charge the work
to the declaration's heartbeat budget (`ProofCarrier.chargeKernelEvaluation`). A failure is
reported as "`task` failed in the kernel evaluator". -/
def kernelWhnf (expression : Expr) (task : String := "checked normalization") :
    MetaM Expr := do
  let result ← withTraceNode `cas.profile.kernel
      (fun _ ↦ return m!"kernel evaluation: {task}") do
    return Lean.Kernel.whnf (← getEnv) (← getLCtx) expression
  ProofCarrier.chargeKernelEvaluation s!"{task} in the kernel evaluator"
  match result with
  | .ok reduced => return reduced
  | .error error =>
      throwError
        "{task} failed in the kernel evaluator: \
          {error.toMessageData (← getOptions)}"

/-- The bound `m` of a `Fin m` index type, after reduction; `none` for any other type. -/
def finBound? (index : Expr) : MetaM (Option Expr) := do
  let index ← whnfD (← instantiateMVars index)
  if index.isAppOfArity ``Fin 1 then
    return some index.appArg!
  return none

/-- The index type `Fin m` of a checked expression type `Verified.Expr (Fin m)` or of a list of
such expressions; fails when the index type is not a `Fin`. -/
def finIndexOfType (type : Expr) : MetaM Expr := do
  let type ← whnfD (← instantiateMVars type)
  let element :=
    if type.isAppOfArity ``List 1 then type.appArg! else type
  let element ← whnfD element
  unless element.isAppOfArity ``Verified.Expr 1 do
    throwError
      "expected a checked expression or a list of checked expressions, found{indentExpr type}"
  let index := element.appArg!
  unless (← finBound? index).isSome do
    throwError "kernel read-back needs a `Fin` index type, found{indentExpr index}"
  return index

/-- The serialization index `fun i : Fin m ↦ (i : ℕ)`. -/
private def indexFunction (atomIndex : Expr) : MetaM Expr :=
  withLocalDeclD `i atomIndex fun i ↦ do
    mkLambdaFVars #[i] (← mkAppM ``Fin.val #[i])

/-- Evaluate the serialized code `code : ℕ` in the kernel and return the literal. -/
private def evaluateCode (code : Expr) : MetaM Nat := do
  let value ← kernelWhnf code
  let some literal := value.rawNatLit?
    | throwError "checked normalization did not evaluate to a serialized result"
  return literal

/-- Evaluate a checked expression `expr : Verified.Expr (Fin m)` together with a side list in
one kernel reduction and read both back over `ℕ`-indexed variables. -/
def readBackPair (atomIndex expr side : Expr) :
    MetaM (Verified.Expr Nat × List (Verified.Expr Nat)) := do
  let code ← mkAppM ``Verified.Expr.Serial.encodeResult #[← indexFunction atomIndex, expr, side]
  let some result := Verified.Expr.Serial.decodeResult (← evaluateCode code)
    | throwError "checked normalization produced an unreadable serialized result"
  return result

/-- Evaluate a checked expression `expr : Verified.Expr (Fin m)` in one kernel reduction. -/
def readBackExpression (atomIndex expr : Expr) : MetaM (Verified.Expr Nat) := do
  let nil ← mkAppOptM ``List.nil #[some (mkApp (mkConst ``Verified.Expr [Level.zero]) atomIndex)]
  return (← readBackPair atomIndex expr nil).1

/-- Evaluate a list of checked expressions over `Fin m` in one kernel reduction. -/
def readBackList (atomIndex side : Expr) : MetaM (List (Verified.Expr Nat)) := do
  let zero ← mkAppOptM ``Verified.Expr.nat #[some atomIndex, some (toExpr (0 : Nat))]
  return (← readBackPair atomIndex zero side).2

/-- Evaluate a normalizer run `run : Alg.NormResult (Fin m)` in one kernel reduction and read
back its normal form and side-condition list over `ℕ`-indexed variables. -/
def readBackRun (atomIndex run : Expr) :
    MetaM (Verified.Expr Nat × List (Verified.Expr Nat)) := do
  readBackPair atomIndex (← mkAppM ``Verified.Expr.Alg.NormResult.expr #[run])
    (← mkAppM ``Verified.Expr.Alg.NormResult.nonzero #[run])

/-- Evaluate a requirement collection `requirements : Verified.Expr.ValidityRequirements (Fin m)`
in one kernel reduction and read back its `nonzero` and `positive` lists. -/
def readBackRequirements (atomIndex requirements : Expr) :
    MetaM (List (Verified.Expr Nat) × List (Verified.Expr Nat)) := do
  let code ← mkAppM ``Verified.Expr.Serial.encodeLists
    #[← indexFunction atomIndex,
      ← mkAppM ``Verified.Expr.ValidityRequirements.nonzero #[requirements],
      ← mkAppM ``Verified.Expr.ValidityRequirements.positive #[requirements]]
  let some result := Verified.Expr.Serial.decodeLists (← evaluateCode code)
    | throwError "checked requirements produced an unreadable serialized result"
  return result

/-- The constructor `name` of `Verified.Expr` applied to the index type and the arguments. -/
private def constructorApp (name : Name) (index : Expr) (arguments : Array Expr) : Expr :=
  mkAppN (mkApp (mkConst name [Level.zero]) index) arguments

/-- Quote a checked expression over `ℕ` back as a term over the index type `index = Fin m`,
using numeric literals for the variables. The constructors are applied directly, without
type inference, since the read-back data of a large normal form has thousands of nodes. -/
def quoteNatExpression (index : Expr) : Verified.Expr Nat → MetaM Expr
  | .nat n => return constructorApp ``Verified.Expr.nat index #[toExpr n]
  | .int z => return constructorApp ``Verified.Expr.int index #[toExpr z]
  | .rat a b => return constructorApp ``Verified.Expr.rat index #[toExpr a, toExpr b]
  | .pi => return constructorApp ``Verified.Expr.pi index #[]
  | .e => return constructorApp ``Verified.Expr.e index #[]
  | .var i => do
      let literal ← mkAppOptM ``OfNat.ofNat #[some index, some (mkRawNatLit i), none]
      return constructorApp ``Verified.Expr.var index #[literal]
  | .add a b => do
      return constructorApp ``Verified.Expr.add index
        #[← quoteNatExpression index a, ← quoteNatExpression index b]
  | .mul a b => do
      return constructorApp ``Verified.Expr.mul index
        #[← quoteNatExpression index a, ← quoteNatExpression index b]
  | .sub a b => do
      return constructorApp ``Verified.Expr.sub index
        #[← quoteNatExpression index a, ← quoteNatExpression index b]
  | .div a b => do
      return constructorApp ``Verified.Expr.div index
        #[← quoteNatExpression index a, ← quoteNatExpression index b]
  | .neg a => do return constructorApp ``Verified.Expr.neg index #[← quoteNatExpression index a]
  | .pow a n => do
      return constructorApp ``Verified.Expr.pow index #[← quoteNatExpression index a, toExpr n]
  | .sin a => do return constructorApp ``Verified.Expr.sin index #[← quoteNatExpression index a]
  | .cos a => do return constructorApp ``Verified.Expr.cos index #[← quoteNatExpression index a]
  | .atan a => do
      return constructorApp ``Verified.Expr.atan index #[← quoteNatExpression index a]
  | .asin a => do
      return constructorApp ``Verified.Expr.asin index #[← quoteNatExpression index a]
  | .acos a => do
      return constructorApp ``Verified.Expr.acos index #[← quoteNatExpression index a]
  | .exp a => do return constructorApp ``Verified.Expr.exp index #[← quoteNatExpression index a]
  | .log a => do return constructorApp ``Verified.Expr.log index #[← quoteNatExpression index a]
  | .sqrt a => do
      return constructorApp ``Verified.Expr.sqrt index #[← quoteNatExpression index a]
  | .rpow a b => do
      return constructorApp ``Verified.Expr.rpow index
        #[← quoteNatExpression index a, ← quoteNatExpression index b]

/-- The conditions of a side list read back from the kernel that the structural sign checker
does not prove nonzero, computed in compiled code exactly as `CAS.Verified.Expr.essentialSide`
computes them in the kernel. -/
def essentialConditions (side : List (Verified.Expr Nat)) : List (Verified.Expr Nat) :=
  side.filter fun condition ↦ !Verified.Expr.AutomaticSign.nonzero condition

/-- Quote a list of checked expressions over `ℕ` back as a list term over `index = Fin m`. -/
def quoteNatList (index : Expr) (expressions : List (Verified.Expr Nat)) : MetaM Expr := do
  let element := mkApp (mkConst ``Verified.Expr [Level.zero]) index
  let nil := mkApp (mkConst ``List.nil [Level.zero]) element
  expressions.foldrM (init := nil) fun expression tail ↦ do
    return mkApp3 (mkConst ``List.cons [Level.zero]) element (← quoteNatExpression index expression)
      tail

/-- The largest number of steps spent reading checked data back into a Lean term, constructor by
constructor, when the variables are not indexed by `Fin n`; past it the call fails with an error
that names the option. The routes over `Fin n` read their result in one kernel evaluation. -/
register_option cas.maxReadBackWork : Nat := {
  defValue := 100000
  descr := "maximum constructor read-back steps for checked data over non-Fin variable types"
}

private inductive ReadBackTask where
  | visit (expression : Expr)
  | assemble (head : Expr) (arguments : Array Expr) (positions : Array Nat)

/-- Read generic expression/list data without unfolding a normalizer in the elaborator.
An explicit stack avoids a recursion-depth limit on the resulting constructor tree.
Variable indices remain terms of their original type. -/
private def readBackGeneric (expression : Expr) : MetaM Expr := do
  let mut tasks := [ReadBackTask.visit expression]
  let mut values : Array Expr := #[]
  for _ in [:cas.maxReadBackWork.get (← getOptions)] do
    match tasks with
    | [] =>
        if values.size = 1 then return values[0]!
        throwError "checked constructor read-back produced malformed data"
    | task :: rest =>
      tasks := rest
      match task with
      | .visit expression =>
        let reduced ← kernelWhnf expression
        let head := reduced.getAppFn
        let mut arguments := reduced.getAppArgs
        let name := head.constName!
        let positions ←
          if name == ``List.nil then pure #[]
          else if name == ``List.cons then pure #[1, 2]
          else if name == ``Verified.Expr.var then pure #[]
          else if name == ``Verified.Expr.nat || name == ``Verified.Expr.int then do
            arguments := arguments.set! 1 (← kernelWhnf arguments[1]!)
            pure #[]
          else if name == ``Verified.Expr.rat then do
            arguments := arguments.set! 1 (← kernelWhnf arguments[1]!)
            arguments := arguments.set! 2 (← kernelWhnf arguments[2]!)
            pure #[]
          else if name == ``Verified.Expr.pi || name == ``Verified.Expr.e then pure #[]
          else if name == ``Verified.Expr.pow then do
            arguments := arguments.set! 2 (← kernelWhnf arguments[2]!)
            pure #[1]
          else
            match ← getConstInfo name with
            | .ctorInfo info =>
              unless info.induct == ``Verified.Expr do
                throwError "checked read-back expected expression data, found{indentExpr reduced}"
              pure ((List.range (arguments.size - 1)).map (· + 1)).toArray
            | _ =>
              throwError "checked read-back did not reduce to constructors:{indentExpr reduced}"
        tasks := .assemble head arguments positions :: tasks
        for position in positions.reverse do
          tasks := .visit arguments[position]! :: tasks
      | .assemble head arguments positions =>
        let mut arguments := arguments
        for position in positions.reverse do
          let some value := values.back? | throwError "incomplete checked constructor read-back"
          arguments := arguments.set! position value
          values := values.pop
        values := values.push (mkAppN head arguments)
  throwError "checked constructor read-back exhausted cas.maxReadBackWork; \
    increase that explicit work budget for a larger result"

/-- Read back and quote a normal form and its side list. Finite indices use serialization;
other index types retain their original variables through bounded kernel constructor read-back.
The caller must certify equality with the computed data before using either quoted value. -/
def readBackQuotedPair (index expression side : Expr) : MetaM (Expr × Expr) := do
  if (← finBound? index).isSome then
    let (expression, side) ← readBackPair index expression side
    return (← quoteNatExpression index expression, ← quoteNatList index side)
  return (← readBackGeneric expression, ← readBackGeneric side)

/-- Whether a quoted checked expression is an explicit constructor tree with literal constants
and exponents. Variable indices are not inspected. The fuel bounds the recursion by term size. -/
def isExplicitExpressionWithin : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let expression := expression.consumeMData
      let head := expression.getAppFn.consumeMData
      let arguments := expression.getAppArgs
      let literal (argument : Expr) : Bool :=
        let argument := argument.consumeMData
        argument.rawNatLit?.isSome || argument.nat?.isSome || argument.int?.isSome
      match head with
      | .const name _ =>
          if name == ``Verified.Expr.pi || name == ``Verified.Expr.e then
            arguments.size == 1
          else if name == ``Verified.Expr.nat || name == ``Verified.Expr.int then
            arguments.size == 2 && literal arguments[1]!
          else if name == ``Verified.Expr.rat then
            arguments.size == 3 && literal arguments[1]! && literal arguments[2]!
          else if name == ``Verified.Expr.var then
            arguments.size == 2
          else if name == ``Verified.Expr.pow then
            arguments.size == 3 && isExplicitExpressionWithin fuel arguments[1]! &&
              literal arguments[2]!
          else if name == ``Verified.Expr.add || name == ``Verified.Expr.mul ||
              name == ``Verified.Expr.sub || name == ``Verified.Expr.div ||
              name == ``Verified.Expr.rpow then
            arguments.size == 3 && isExplicitExpressionWithin fuel arguments[1]! &&
              isExplicitExpressionWithin fuel arguments[2]!
          else if name == ``Verified.Expr.neg || name == ``Verified.Expr.sin ||
              name == ``Verified.Expr.cos || name == ``Verified.Expr.atan ||
              name == ``Verified.Expr.asin || name == ``Verified.Expr.acos ||
              name == ``Verified.Expr.exp || name == ``Verified.Expr.log ||
              name == ``Verified.Expr.sqrt then
            arguments.size == 2 && isExplicitExpressionWithin fuel arguments[1]!
          else
            false
      | _ => false

/-- Whether a quoted checked expression is an explicit constructor tree with literal constants
and exponents, without inspecting its variable indices. -/
def isExplicitExpression (expression : Expr) : Bool :=
  isExplicitExpressionWithin (expression.sizeWithoutSharing + 1) expression

/-- Tag of the report of a kernel certificate that reached the kernel's recursion limit. -/
def deepRecursionTag : Name := `CAS.kernelDeepRecursion

/-- Tag of the report of a kernel certificate that the kernel did not reduce to `true`. -/
def rejectionTag : Name := `CAS.kernelRejection

/-- Tag of the report of a kernel certificate whose decision procedure mentions a classical one.
That shows neither that the statement is false nor where the reduction stopped; `cega` uses it
only to order its report. -/
def classicalDecisionTag : Name := `CAS.kernelClassicalDecision

/-- Whether `error` is the report of a kernel certificate of `decideByKernel` that failed after its
statement was closed and its decision procedure synthesized, by the recursion limit or by not
reducing to `true`, and whose decision procedure mentions none of `classicalDecisions`. -/
def isKernelCertificateFailure (error : Exception) : Bool :=
  error.toMessageData.hasTag fun tag ↦ tag == deepRecursionTag || tag == rejectionTag

/-- Classical decision procedures, which the kernel cannot reduce, named in a rejected
certificate's report when its `Decidable` instance mentions one of them. -/
private def classicalDecisions : Array Name := #[``Classical.propDecidable, ``Classical.dec,
  ``Classical.decEq, ``Classical.decPred, ``Classical.decRel, `Real.decidableLT,
  `Real.decidableLE, `Real.decidableEq]

/-- The failure report of a rejected kernel certificate other than a timeout, tagged with
`deepRecursionTag`, `rejectionTag` or `classicalDecisionTag`. A recursion limit is named as
such, with a setting that parses. Any other rejection says that the decision procedure did not
reduce to `true`, which does not show that the statement is false: the procedure may also be
stuck. When the decision procedure in `proof` mentions a classical one (as the order and
equality of real numbers do), the report names it, without claiming that it stopped the check. -/
private def kernelRejection (operation : String) (statement proof : Expr)
    (error : Exception) : MetaM MessageData := do
  if ← ProofCarrier.isKernelDeepRecursion error then
    let depth := maxRecDepth.get (← getOptions)
    return .tagged deepRecursionTag m!"{operation}: the kernel reached its recursion limit \
      (maxRecDepth {depth}) while evaluating{indentExpr statement}\nThis is a resource limit, \
      not a refutation. To raise the limit, write `set_option maxRecDepth {4 * depth} in` \
      before the tactic; or make the computation smaller."
  -- The proof is `of_decide_eq_true (h : decide p = true)` with the instance as its second
  -- argument; only that instance is read, without unfolding.
  let decision := if proof.isAppOfArity ``of_decide_eq_true 3 then proof.getArg! 1 else proof
  let used := decision.getUsedConstants
  let classical := classicalDecisions.filter used.contains
  let cause := if classical.isEmpty then
      m!"The statement may be false, or its decision procedure may not reduce in the kernel."
    else
      m!"Its decision procedure mentions \
        {MessageData.joinSep (classical.toList.map fun name ↦ m!"`{.ofConstName name}`") ", "}, \
        which is classical and never reduces in the kernel. Whether or not that is what stopped \
        this check, the failure says nothing about the truth of the statement."
  let tag := if classical.isEmpty then rejectionTag else classicalDecisionTag
  return .tagged tag m!"{operation} could not certify a checked computation: the kernel did not \
    reduce the decision procedure of{indentExpr statement}\nto `true`. {cause}"

/-- Prove the decidable `statement` the way `decide +kernel` does, so that the kernel evaluates
the checked computation it mentions exactly once, and return the proof. As in core's
`decide +kernel` run from `MetaM`, local definitions are unfolded first, a statement that stays
open is refused, and the proof `of_decide_eq_true (Eq.refl true)` is registered with
`mkAuxLemma` under kind `_proof`, synchronously and with the universe parameters of the
statement. There are four differences: a cached lemma depending on a nonstandard axiom is
neither reused nor written (`ProofCarrier.mkKernelAuxLemma`); the kernel check gets only the
heartbeats the declaration has left and a kernel timeout ends the tactic
(`ProofCarrier.runKernelCheck`); a rejected theorem does not stay in the environment as an
axiom; and the failure report names the statement instead of forcing the potentially expensive
diagnostic of `decide`. -/
def decideByKernel (operation : String) (statement : Expr) : MetaM Expr := do
  let statement ← instantiateMVars statement
  let statement ← if statement.hasFVar then zetaReduce statement else pure statement
  if statement.hasFVar || statement.hasMVar then
    throwError "{operation} could not certify a checked computation: the statement\
      {indentExpr statement}\nis not closed"
  let proof ← mkDecideProof statement
  let levels := (collectLevelParams {} statement).params.toList
  let name ← ProofCarrier.runKernelCheck operation
      (ProofCarrier.mkKernelAuxLemma levels statement proof `_proof)
      fun error ↦ do throwError (← kernelRejection operation statement proof error)
  return mkConst name (levels.map mkLevelParam)

end CAS.Tactic.KernelReadBack
