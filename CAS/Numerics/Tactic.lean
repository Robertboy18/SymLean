/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Finite
public meta import CAS.Numerics.Finite
public import CAS.CEGA
public meta import CAS.CEGA
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Batched CEGA checks

For a goal `∀ i : Fin n, p i` with decidable `p`, `cega [batch := 128]` checks batches of 128
consecutive indices in the kernel, the shorter final batch included, and assembles them with the
coverage theorems of `CAS.Numerics.Finite`. `cega [fast, batch := 128]` evaluates the whole
family of batches once by compiled code when `cega.nativeCertificates` is true, and is the kernel
form otherwise. Batches are internal proof steps, so changing their size does not change the
theorem or require new modules.

## Implementation notes

A domain `Fin (Array.size a)` whose array is built from literal lists, appends and data aliases is
first rewritten to a numeral by kernel-checked `_finiteArraySize` theorems (`List.size_toArray`,
`Array.size_append`), so counting rows never evaluates their contents. We then compile the
predicate once with an abstract index, as the irreducible definitions `_finiteDecidable` and
`_finiteChecker`, and `CAS.Numerics.forall_of_decide_eq_true` reduces the goal to
`∀ i, checker i = true`: specializing a batch does not resynthesize a decision procedure through
large numerical data. Each `BatchAll p (b * size) size` becomes its own kernel theorem through
`decideClosedCertificate`, as `decide +kernel` would prove it, checked at once within the
heartbeats the declaration has left, so an exhausted budget ends the tactic with a timeout.
`rangeAll_singleton`, `rangeAll_append` and `rangeAll_zero` join the batches in a balanced tree,
`forall_of_rangeAll` and `forall_of_batchAll` give the goal, and `decide` proves `0 < size`. The
checker definitions and size theorems are checked in the kernel the same way.

A false or stuck batch fails the tactic with its number and index range (`batchFailure`), so
`first` can try an alternative. A failed batch is not a counterexample: the kernel may also have
reached its recursion limit. The kernel form runs under
`CAS.Tactic.ProofCarrier.withKernelOnlyAxioms`, so the proof may use no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` that the goal and its context do not already use. The native
form proves `∀ b, BatchAll p (b * size) size` in one evaluation, sharing imported tables across
the batches instead of initializing them for every check; it trusts Lean's compiler and runtime
as well, and its work is charged to the declaration too. Both forms check the batches one after
another.
-/

public meta section

open Lean Meta Elab Tactic

/--
`cega [batch := n]`

A finite certificate goal checked in the kernel in batches of `n` consecutive indices, which are
then assembled into one coverage proof.
-/
tactic_extension CAS.CEGA.tacticCega

/--
`cega [fast, batch := n]`

`cega [batch := n]` with the batches checked by compiled code when `cega.nativeCertificates` is
true, and in the kernel otherwise.
-/
tactic_extension CAS.CEGA.tacticCega

-- `&"..."` keeps `batch` and `fast` ordinary identifiers in modules that import this one.
/-- The argument of `cega [batch := n]`. -/
syntax (name := CAS.Numerics.cegaBatch) " [" &"batch" " := " num "]" : cegaArgs
/-- The argument of `cega [fast, batch := n]`. -/
syntax (name := CAS.Numerics.cegaFastBatch) " [" &"fast" ", " &"batch" " := " num "]" : cegaArgs

/-- Unfold one data alias without reducing array operations or row contents. -/
private def unfoldDataAlias? (value : Expr) : MetaM (Option Expr) := do
  let .const name levels := value.getAppFn | return none
  let .defnInfo info ← getConstInfo name | return none
  let body ← instantiateValueLevelParams (.defnInfo info) levels
  return some ((mkAppN body value.getAppArgs).headBeta.consumeMData)

/-- Read only the cons spine of a literal list; entries are never evaluated. -/
private partial def literalListLength? (values : Expr) : Option Nat :=
  let values := values.consumeMData
  if values.isAppOfArity ``List.nil 1 then some 0
  else if values.isAppOfArity ``List.cons 3 then
    (literalListLength? values.getAppArgs[2]!).map (· + 1)
  else none

/-- Keep each structural size argument as a small closed, kernel-checked theorem, checked when
the tactic runs. The theorem is evidence of the cardinality, rather than planner metadata. -/
private def declareArraySize (array : Expr) (count : Nat) (value : Expr) : MetaM Expr := do
  let cardinality ← mkAppM ``Array.size #[array]
  let type ← mkEq cardinality (mkNatLit count)
  if type.hasFVar || type.hasMVar || type.hasLooseBVars ||
      value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "CEGA structural cardinality proofs must be closed"
  let levels := (collectLevelParams {} type).params.toList
  let name ← mkAuxDeclName `_finiteArraySize
  CAS.Tactic.ProofCarrier.runKernelCheck "CEGA structural cardinality"
    (addDecl <| .thmDecl { name, levelParams := levels, type, value })
    fun error ↦ throw error
  return mkConst name (levels.map mkLevelParam)

/-- Prove the size of an appended literal array structurally. In particular,
balanced imported JSON branches never run append loops just to find their size.
Only array aliases, append nodes and literal-list spines are inspected. -/
private partial def structuralArraySize? (array : Expr) : MetaM (Option (Nat × Expr)) := do
  let array := array.consumeMData.headBeta
  if let .letE _ _ value body _ := array then
    return ← structuralArraySize? (body.instantiate1 value)
  if array.isAppOfArity ``Array.append 3 then
    let args := array.getAppArgs
    let some (leftCount, leftProof) ← structuralArraySize? args[1]! | return none
    let some (rightCount, rightProof) ← structuralArraySize? args[2]! | return none
    let count := leftCount + rightCount
    let congruence ← mkAppM ``congrArg₂ #[mkConst ``Nat.add, leftProof, rightProof]
    let sizeAppend ← mkAppOptM ``Array.size_append
      #[some args[0]!, some args[1]!, some args[2]!]
    let value ← mkEqTrans sizeAppend congruence
    return some (count, ← declareArraySize array count value)
  if array.isAppOfArity ``List.toArray 2 then
    let args := array.getAppArgs
    let some count := literalListLength? args[1]! | return none
    -- List.size_toArray removes array evaluation; only a short leaf's
    -- cons-spine length remains definitionally equal to the numeral.
    let value ← mkAppOptM ``List.size_toArray #[some args[0]!, some args[1]!]
    return some (count, ← declareArraySize array count value)
  if array.isAppOfArity ``Array.mk 2 then
    let some count := literalListLength? array.getAppArgs[1]! | return none
    let value ← mkEqRefl (mkNatLit count)
    return some (count, ← declareArraySize array count value)
  if let some unfolded ← unfoldDataAlias? array then
    let some (count, value) ← structuralArraySize? unfolded | return none
    return some (count, ← declareArraySize array count value)
  return none

/-- Rewrite a data-sized finite goal using checked cardinality evidence before
compiling its predicate. Native and kernel batches then share a literal domain;
the equality transport still proves the original dependent statement. -/
private def normalizeArrayFiniteDomain : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let .forallE _ domain _ _ := target | return
  unless domain.isAppOfArity ``Fin 1 do return
  let cardinality := (← zetaReduce domain.appArg!).consumeMData
  unless cardinality.isAppOfArity ``Array.size 2 do return
  if cardinality.hasFVar || cardinality.hasMVar || cardinality.hasLooseBVars then return
  let some (_, proof) ← structuralArraySize? cardinality.appArg! | return
  let result ← goal.rewrite target proof
  unless result.mvarIds.isEmpty do
    throwError "CEGA structural cardinality rewrite introduced unresolved obligations"
  let normalized ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal [normalized]

/-- Add a definition for `compileFiniteChecker`, checked in the kernel now within what is left
of the declaration's budget. -/
private def addCheckerDefinition (name : Name) (value : Expr) : MetaM Expr :=
  CAS.Tactic.ProofCarrier.runKernelCheck "CEGA batch checker"
    (mkAuxDefinitionFor name value)
    fun error ↦ throw error

/-- Compile the predicate with an abstract index, so specializing a batch does not
resynthesize a decision procedure through large numerical data definitions. -/
private def compileFiniteChecker : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let .forallE name domain body info := target | throwError "expected a finite universal goal"
  unless domain.isAppOfArity ``Fin 1 do
    throwError "expected an index of type Fin n"
  withLocalDecl name info domain fun index ↦ do
    let proposition := body.instantiate1 index
    let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) proposition)
    let predicate ← mkLambdaFVars #[index] proposition
    let decidableValue ← mkLambdaFVars #[index] decisionInstance
    let decidableName ← mkAuxDeclName `_finiteDecidable
    let decidablePredicate ← addCheckerDefinition decidableName decidableValue
    setReducibilityStatus decidableName .irreducible
    let decision := mkApp2 (mkConst ``decide) proposition (mkApp decidablePredicate index)
    let checkerValue ← mkLambdaFVars #[index] decision
    let checkerName ← mkAuxDeclName `_finiteChecker
    let checker ← addCheckerDefinition checkerName checkerValue
    setReducibilityStatus checkerName .irreducible
    let equality ← mkEq (mkApp checker index) (mkConst ``Bool.true)
    let checkedType ← mkForallFVars #[index] equality
    let checked ← mkFreshExprSyntheticOpaqueMVar checkedType
    -- The checker and the soundness theorem use the same named decision procedure.
    -- Keeping that procedure out of the proof application avoids rechecking its
    -- full expression at every batch, especially for nested interval arithmetic.
    let proof := mkAppN (mkConst ``CAS.Numerics.forall_of_decide_eq_true [.zero])
      #[domain, predicate, decidablePredicate, checked]
    goal.assign proof
    replaceMainGoal [checked.mvarId!]

/-- Check each leaf in the kernel, synchronously and within `maxHeartbeats`, then join adjacent
ranges in a balanced tree. Only closed propositions are checked. Each leaf's kernel work is
charged to the declaration before the next leaf starts. -/
private partial def checkBatchRange (n predicate : Expr)
    (start count : Nat) (report : Nat → Exception → MetaM Exception) : MetaM Expr := do
  if count == 0 then
    return mkAppN (mkConst ``CAS.Numerics.rangeAll_zero)
      #[n, mkNatLit start, predicate]
  if count == 1 then
    let bound ← mkDecideProof (← mkLt (mkNatLit start) n)
    let index := mkApp3 (mkConst ``Fin.mk) n (mkNatLit start) bound
    let statement ← zetaReduce (mkApp predicate index)
    if statement.hasFVar || statement.hasMVar || statement.hasLooseBVars then
      throwError "CEGA batch checking requires a closed predicate and finite domain"
    -- One kernel theorem per leaf (`decide +kernel` style), checked here: a false leaf or a
    -- kernel timeout fails the tactic.
    let checked ← try
        CAS.CEGA.Elaboration.decideClosedCertificate statement false
      catch error =>
        throw (← report start error)
    checkSystem "CEGA batch"
    return mkAppN (mkConst ``CAS.Numerics.rangeAll_singleton)
      #[n, mkNatLit start, predicate, bound, checked]
  let left := count / 2
  let hleft ← checkBatchRange n predicate start left report
  let hright ← checkBatchRange n predicate (start + left) (count - left) report
  return mkAppN (mkConst ``CAS.Numerics.rangeAll_append)
    #[n, mkNatLit start, mkNatLit left, mkNatLit (count - left), predicate, hleft, hright]

/-- The report of a kernel batch leaf that failed: batch `batch` (from 0) of `count`, the indices
it covers, and the goal as the user wrote it, instead of the internal checker. A failed leaf is
not a counterexample: the kernel may also have run out of recursion depth or been stuck. -/
private def batchFailure (tactic : String) (original : Expr) (size count : Nat)
    (total? : Option Nat) (batch : Nat) (error : Exception) : MetaM Exception := do
  unless CAS.Tactic.KernelReadBack.isKernelCertificateFailure error do
    return error
  let lower := batch * size
  let upper := match total? with
    | some total => min total (lower + size)
    | none => lower + size
  let cause ← if error.toMessageData.hasTag
      (· == CAS.Tactic.KernelReadBack.deepRecursionTag) then do
      let depth := maxRecDepth.get (← getOptions)
      pure m!"The kernel reached its recursion limit (maxRecDepth {depth}) on this batch. To \
        raise the limit, write `set_option maxRecDepth {4 * depth} in` before the tactic; or use \
        smaller batches."
    else
      pure m!"The kernel did not reduce the check of this batch to `true`: the statement may be \
        false for an index in this range, or its decision procedure may not reduce in the kernel."
  return .error (← getRef) m!"{tactic} could not certify batch {batch + 1} of {count}, the \
    indices i with {lower} ≤ i < {upper}, of{indentExpr original}\n{cause}"

private def checkBatches (size : TSyntax `num) (useNative : Bool) : TacticM Unit := do
  unless 0 < size.getNat do
    throwError "CEGA batch size must be positive"
  -- The goal as written, for the report of a failed batch.
  let original ← withMainContext do instantiateMVars (← getMainTarget)
  normalizeArrayFiniteDomain
  compileFiniteChecker
  withMainContext do
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let .forallE name domain body info := target | throwError "expected a finite universal goal"
    let n := domain.appArg!
    let sizeValue := mkNatLit size.getNat
    withLocalDecl name info domain fun index ↦ do
      let predicate ← mkLambdaFVars #[index] (body.instantiate1 index)
      let positiveType ← mkAppM ``LT.lt #[mkNatLit 0, sizeValue]
      let positive ← mkFreshExprSyntheticOpaqueMVar positiveType
      let batchCount := mkApp2 (mkConst ``CAS.Numerics.batchCount) n sizeValue
      let batchDomain := mkApp (mkConst ``Fin) batchCount
      withLocalDeclD `b batchDomain fun batchExpr ↦ do
        let start := mkApp2 (mkConst ``Nat.mul)
          (mkApp2 (mkConst ``Fin.val) batchCount batchExpr) sizeValue
        let batchType := mkAppN (mkConst ``CAS.Numerics.BatchAll)
          #[n, predicate, start, sizeValue]
        let batchPredicate ← zetaReduce (← mkLambdaFVars #[batchExpr] batchType)
        let .lit (.natVal count) ← withTransparency .all (whnf batchCount)
          | throwError "CEGA batching requires a closed natural-number domain"
        let batchProof ← if useNative && count > 0 &&
            (← getOptions).getBool `cega.nativeCertificates false then do
          -- One evaluation shares imported data across the batches. Reinitializing
          -- large tables for every batch can cost more than the row checks themselves.
          -- The evaluation runs here, so a false family fails the tactic.
          let statement ← mkForallFVars #[batchExpr] batchType
          let proof ← CAS.CEGA.Elaboration.decideClosedCertificate statement true
          checkSystem "CEGA native batch"
          pure proof
        else do
          -- Each kernel leaf is its own kernel theorem and sees the compiled helpers.
          -- Empty families need no numerical evaluation.
          let total? := match ← withTransparency .all (whnf n) with
            | .lit (.natVal total) => some total
            | _ => none
          let tactic := if useNative then s!"cega [fast, batch := {size.getNat}]"
            else s!"cega [batch := {size.getNat}]"
          let rangeProof ← checkBatchRange batchCount batchPredicate 0 count
            (batchFailure tactic original size.getNat count total?)
          pure <| mkAppN (mkConst ``CAS.Numerics.forall_of_rangeAll)
            #[batchCount, batchPredicate, rangeProof]
        -- Explicit arguments keep coverage elaboration away from the checker's body.
        goal.assign <| mkAppN (mkConst ``CAS.Numerics.forall_of_batchAll)
          #[n, sizeValue, predicate, positive, batchProof]
        replaceMainGoal [positive.mvarId!]
  evalTactic (← `(tactic| decide))

/-- Check the batches of the main goal; unless native checking was requested and is enabled,
as a kernel-only route (`CAS.Tactic.ProofCarrier.withKernelOnlyAxioms`). -/
private def closeBatches (size : TSyntax `num) (useNative : Bool) : TacticM Unit := do
  if useNative && (← getOptions).getBool `cega.nativeCertificates false then
    checkBatches size true
  else
    CAS.Tactic.ProofCarrier.withKernelOnlyAxioms "cega [batch]" do
      checkBatches size useNative
      return ((), #[])

elab_rules : tactic
  | `(tactic| cega [batch := $size:num]) =>
      CAS.Tactic.ProofCarrier.tacticEntry s!"cega [batch := {size.getNat}]"
        (closeBatches size false)
  | `(tactic| cega [fast, batch := $size:num]) =>
      CAS.Tactic.ProofCarrier.tacticEntry s!"cega [fast, batch := {size.getNat}]"
        (closeBatches size true)
