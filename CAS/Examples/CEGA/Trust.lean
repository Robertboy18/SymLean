/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import CAS.Numerics.Tactic
meta import CAS.Tactic.ProofCarrier

/-!
# The trust contract of `cega`

Every form of `cega` except native `cega [fast]` promises a proof that the kernel checks in full,
using no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The first section prints
the axioms of one theorem per route. The second plants a lemma that depends on another axiom in
Lean's auxiliary-lemma cache, under the statement a kernel route is about to prove, and checks
that the route does not take it. The third checks the resource budgets: a box query with too
many coordinates or digits is refused before any kernel work, and kernel timeouts are reported as
timeouts. The last section collects refusals: false statements, an out-of-scope goal, a false
batch inside `first`.

Native checking needs `cega.nativeCertificates`, which would put native axioms into the library;
those tests are in `tests/cega` and run outside the library build.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Trust

open Lean Meta Elab Lean.Meta.Tactic Lean.Elab.Tactic

-- These tests are about the kernel profile, also when the library is built with native checking.
set_option cega.nativeCertificates false
set_option linter.hashCommand false

/-! ## Kernel routes use only the standard axioms -/

/-- The box route on an ordinary inequality. -/
theorem box_bound (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

/-- The explicit query for the same bound. -/
theorem query_bound (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/-- A closed finite certificate. -/
theorem finite_rows : ∀ i : Fin 32, (i.val : ℤ) ^ 2 < 1024 := by
  cega

/-- `cega [fast]` without native checking is bare `cega`. -/
theorem fast_without_native (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]

/-- Kernel batches. -/
theorem batch_rows : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [batch := 3]

/-- `cega [fast, batch := n]` without native checking checks kernel batches. -/
theorem fast_batch_rows : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [fast, batch := 4]

/-- info: 'CAS.Examples.CEGA.Trust.box_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms box_bound

/-- info: 'CAS.Examples.CEGA.Trust.query_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_bound

/-- info: 'CAS.Examples.CEGA.Trust.finite_rows' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_rows

/-- info: 'CAS.Examples.CEGA.Trust.fast_without_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fast_without_native

/-- info: 'CAS.Examples.CEGA.Trust.batch_rows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_rows

/-- info: 'CAS.Examples.CEGA.Trust.fast_batch_rows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fast_batch_rows

/-! ## A tainted cache entry is not reused

A statement is first registered in the auxiliary-lemma cache with a proof by a fresh axiom, as a
native certificate would register it; core `decide +kernel` then takes that lemma. A
kernel route of `cega` proves the same statement without it and replaces the cache entry. The
statements differ from the theorems above, and the environment is restored afterwards, so the
axiom never reaches the library. The finite route asks the cache for the goal itself; the box
route asks for the compact proposition of its query, read here from a first, clean run. -/

/-- Elaborate a closed statement. -/
meta def statementOf (stx : Term) : TermElabM Expr := do
  let statement ← Term.elabTerm stx (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars statement

/-- Run `tactic` on a fresh goal `statement` and return its proof. -/
meta def proveWith (statement : Expr) (tactic : TSyntax `tactic) : TermElabM Expr := do
  let goal ← mkFreshExprMVar statement
  discard <| Tactic.run goal.mvarId! (evalTactic tactic)
  instantiateMVars goal

/-- The number of nonstandard axioms of a proof. -/
meta def extraAxioms (proof : Expr) : MetaM Nat := do
  return (← CAS.Tactic.ProofCarrier.nonstandardAxioms proof).size

/-- A fresh axiom asserting `statement`. -/
meta def freshAxiom (statement : Expr) : MetaM Expr := do
  let axiomName ← mkAuxDeclName `testedAxiom
  addDecl <| .axiomDecl
    { name := axiomName, levelParams := [], type := statement, isUnsafe := false }
  return mkConst axiomName

/-- Insert a lemma for `statement` proved by a fresh axiom into the auxiliary-lemma cache. -/
meta def plantTaintedLemma (statement : Expr) : MetaM Unit := do
  discard <| mkAuxLemma [] statement (← freshAxiom statement) (cache := false)

/-- The number of nonstandard axioms of the lemma the cache now holds for `statement`. -/
meta def cachedAxioms (statement : Expr) : MetaM Nat := do
  -- A cache hit returns the stored lemma; the value is not used.
  extraAxioms (mkConst (← mkAuxLemma [] statement (mkConst ``True.intro)))

/-- info: core `decide +kernel` takes the planted lemma: 1; `cega` proofs: finite 0, box 0;
cache entries afterwards: finite 0, box 0 -/
#guard_msgs (whitespace := lax) in
run_elab withoutModifyingEnv do
  let finite ← statementOf (← `(∀ i : Fin 31, (i.val : ℤ) ^ 2 < 961))
  plantTaintedLemma finite
  let decided ← extraAxioms (← proveWith finite (← `(tactic| decide +kernel)))
  let finiteProof ← extraAxioms (← proveWith finite (← `(tactic| cega)))
  let finiteEntry ← cachedAxioms finite
  let box ← statementOf (← `(∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * (2 - x) ≤ 1))
  let compact ← withoutModifyingEnv do
    let proof ← proveWith box (← `(tactic| cega))
    let isQueryTheorem : Name → Bool
      | .str _ last => last.startsWith "_cega_"
      | _ => false
    let some query := proof.getUsedConstants.find? isQueryTheorem
      | throwError "the box route used no CEGA query theorem"
    return (← getConstInfo query).type
  plantTaintedLemma compact
  unless (← cachedAxioms compact) == 1 do
    throwError "the planted lemma for the box query is not in the cache"
  let boxProof ← extraAxioms (← proveWith box (← `(tactic| cega)))
  let boxEntry ← cachedAxioms compact
  logInfo m!"core `decide +kernel` takes the planted lemma: {decided}; `cega` proofs: finite \
    {finiteProof}, box {boxProof}; cache entries afterwards: finite {finiteEntry}, box {boxEntry}"

-- A kernel certificate whose own value depends on another axiom is checked but never cached:
-- the next cache lookup for its statement finds nothing and adds the clean proof instead.
/-- info: lemma uses 1 nonstandard axiom; cache entry afterwards uses 0 -/
#guard_msgs (whitespace := lax) in
run_meta withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 3, mkNatLit 3]) (mkNatLit 6)
  let name ← CAS.Tactic.ProofCarrier.mkKernelAuxLemma [] fact (← freshAxiom fact)
    `_test
  let used ← extraAxioms (mkConst name)
  let entry ← extraAxioms (mkConst (← mkAuxLemma [] fact (← mkEqRefl (mkNatLit 6))))
  logInfo m!"lemma uses {used} nonstandard axiom; cache entry afterwards uses {entry}"

/-! ## Which axioms a kernel-only route may use

A route may use an axiom that its inputs already use: the goal, the hypotheses and local
definitions its proof or goal reach, or an explicit carrier. An axiom that only an unused
hypothesis mentions, or that no input mentions, is rejected, and so is `sorryAx` reached through
a local definition or the type of a hypothesis the proof uses. The checks run
`withKernelOnlyAxioms` around `exact` with a fresh axiom, in an environment that is restored
afterwards. -/

/-- Close `goal` by `proof` inside `withKernelOnlyAxioms`: "accepted", or the first words of the
rejection. -/
meta def kernelOnlyExact (goal : MVarId) (proof : Expr) : TermElabM String := do
  let saved ← saveState
  try
    discard <| Tactic.run goal do
      CAS.Tactic.ProofCarrier.withKernelOnlyAxioms "test" do
        closeMainGoal `test proof
        return ((), #[])
    return "accepted"
  catch error =>
    saved.restore
    let text ← error.toMessageData.toString
    return if (text.splitOn "sorryAx").length > 1 then "rejected (sorryAx)"
      else if (text.splitOn "promises a kernel-checked proof").length > 1 then "rejected"
      else s!"failed: {text}"

/--
info: no input: rejected; through a local definition: accepted; unused hypothesis: rejected;
goal: accepted; goal through a local definition: accepted; sorry through a local definition:
rejected (sorryAx); sorry through a hypothesis type: rejected (sorryAx)
-/
#guard_msgs (whitespace := lax) in
run_elab withoutModifyingEnv do
  let fact ← mkEq (← mkAppM ``HAdd.hAdd #[mkNatLit 2, mkNatLit 2]) (mkNatLit 4)
  let ax ← freshAxiom fact
  let noInput ← kernelOnlyExact (← mkFreshExprMVar fact).mvarId! ax
  -- `h := ax` reaches the axiom through a local definition the proof uses.
  let viaLet ← withLetDecl `h fact ax fun h ↦ do
    let proof ← mkAppM ``Eq.trans #[h, ← mkEqRefl (mkNatLit 4)]
    kernelOnlyExact (← mkFreshExprMVar fact).mvarId! proof
  let unused ← withLocalDeclD `u (← mkEq ax ax) fun _ ↦ do
    kernelOnlyExact (← mkFreshExprMVar fact).mvarId! ax
  let viaGoal ← kernelOnlyExact (← mkFreshExprMVar (← mkEq ax ax)).mvarId! (← mkEqRefl ax)
  -- The goal is a local `T := ax = ax`; the proof mentions `ax` directly.
  let viaGoalLet ← withLetDecl `T (mkSort .zero) (← mkEq ax ax) fun t ↦ do
    kernelOnlyExact (← mkFreshExprMVar t).mvarId! (← mkEqRefl ax)
  let viaSorry ← withLetDecl `s fact (← mkSorry fact (synthetic := true)) fun h ↦ do
    kernelOnlyExact (← mkFreshExprMVar fact).mvarId! h
  -- A hypothesis `h : P` whose type is a local `P := sorry`.
  let viaHypothesisType ← withLetDecl `P (mkSort .zero)
      (← mkSorry (mkSort .zero) (synthetic := true)) fun p ↦ do
    withLocalDeclD `h p fun h ↦ do kernelOnlyExact (← mkFreshExprMVar p).mvarId! h
  logInfo m!"no input: {noInput}; through a local definition: {viaLet}; unused hypothesis: \
    {unused}; goal: {viaGoal}; goal through a local definition: {viaGoalLet}; sorry through a \
    local definition: {viaSorry}; sorry through a hypothesis type: {viaHypothesisType}"

/-! ## Budgets

Box queries are refused before any kernel work when their dimension, the nesting of the
planner's monotonicity search, or the requested digits exceed their budgets. Without them, a sum of
six squares on `[1, 2]^6` takes 385 s and 42 GB; with them it is refused at once. -/

/-- exceeds cega.maxFaceReductions (5) -/
#guard_msgs (substring := true, whitespace := lax) in
example (x0 x1 x2 x3 x4 x5 : ℝ) (h0 : x0 ∈ Set.Icc (1 : ℝ) 2) (h1 : x1 ∈ Set.Icc (1 : ℝ) 2)
    (h2 : x2 ∈ Set.Icc (1 : ℝ) 2) (h3 : x3 ∈ Set.Icc (1 : ℝ) 2) (h4 : x4 ∈ Set.Icc (1 : ℝ) 2)
    (h5 : x5 ∈ Set.Icc (1 : ℝ) 2) :
    x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 + x5 * x5 ≤ 24 := by
  cega

/-- exceeds cega.maxDimension (8) -/
#guard_msgs (substring := true, whitespace := lax) in
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (h0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x1 ∈ Set.Icc (0 : ℝ) 1) (h2 : x2 ∈ Set.Icc (0 : ℝ) 1) (h3 : x3 ∈ Set.Icc (0 : ℝ) 1)
    (h4 : x4 ∈ Set.Icc (0 : ℝ) 1) (h5 : x5 ∈ Set.Icc (0 : ℝ) 1) (h6 : x6 ∈ Set.Icc (0 : ℝ) 1)
    (h7 : x7 ∈ Set.Icc (0 : ℝ) 1) (h8 : x8 ∈ Set.Icc (0 : ℝ) 1) :
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 ≤ 9 := by
  cega

/-- exceeds cas.maxDigits (2000) -/
#guard_msgs (substring := true, whitespace := lax) in
example : (3 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 4 := by
  cega (digits := 20000) [enclose] Real.pi

/-- the decimal literal has a power of ten 2000, over the limit 1000 -/
#guard_msgs (substring := true, whitespace := lax) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ 2 := by
  cega [enclose x in [0, 1e2000]] x

/-! Kernel checks share the declaration's heartbeat budget, and running out of it ends the
tactic with a timeout instead of reading as an unproved statement. With `maxHeartbeats 0` there
is no budget, as before. -/

set_option maxHeartbeats 0 in
-- The test is that kernel certificates are checked without a heartbeat budget.
/-- A kernel certificate without a heartbeat budget. -/
theorem unlimited_budget : ∀ i : Fin 8, (i.val : ℤ) ^ 2 < 64 := by
  cega

/-- (deterministic) timeout: CEGA finite certificate: the kernel ran out of the -/
#guard_msgs (substring := true, whitespace := lax) in
set_option maxHeartbeats 5000 in
example : ∀ i : Fin 1, (List.range 200000).foldl (· + ·) 0 ≠ i.val + 1 := by
  cega

/-- (deterministic) timeout: CEGA finite certificate: the kernel ran out of the -/
#guard_msgs (substring := true, whitespace := lax) in
set_option maxHeartbeats 5000 in
example : ∀ i : Fin 1, (List.range 200000).foldl (· + ·) 0 ≠ i.val + 1 := by
  cega [batch := 1]

/-! The leaves of a batch share the budget: one leaf of this family costs about eight million
heartbeats and fits within twenty million, eight leaves do not. Before, every leaf was checked
later with an unlimited budget. -/

set_option maxHeartbeats 20000 in
-- The test is that one leaf fits in this budget.
/-- One batch leaf within the budget. -/
theorem one_leaf_within_budget : ∀ i : Fin 1, (List.range 20000).foldl (· + ·) i.val ≠ 1 := by
  cega [batch := 1]

/-- (deterministic) timeout: CEGA finite certificate -/
#guard_msgs (substring := true, whitespace := lax) in
set_option maxHeartbeats 20000 in
example : ∀ i : Fin 8, (List.range 20000).foldl (· + ·) i.val ≠ 1 := by
  cega [batch := 1]

/--
error: CEGA finite certificate: the kernel reached its recursion limit (maxRecDepth 512) while
evaluating
  ∀ (i : Fin 4096), ↑↑i ^ 2 < 16777216
This is a resource limit, not a refutation. To raise the limit, write
`set_option maxRecDepth 2048 in` before the tactic
-/
#guard_msgs (substring := true, whitespace := lax) in
example : ∀ i : Fin 4096, (i.val : ℤ) ^ 2 < 16777216 := by
  cega

-- The setting the report suggests proves it.
example : ∀ i : Fin 4096, (i.val : ℤ) ^ 2 < 16777216 := by
  set_option maxRecDepth 2048 in cega

/-! ## Refusals -/

/-- cas could not prove this arithmetic relation -/
#guard_msgs (substring := true, whitespace := lax) in
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 1 := by
  cas

/-- the certified value does not give the stated bound -/
#guard_msgs (substring := true, whitespace := lax) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 5 := by
  cega

/-- its outer shape is not supported by these routes -/
#guard_msgs (substring := true, whitespace := lax) in
example : ∀ n : ℕ, n + 0 = n := by
  cega

-- The linters would otherwise report the alternative that never finishes.
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- A false batch fails inside the tactic, so `first` moves on to the next alternative. -/
example : True := by
  first
    | (have : ∀ i : Fin 2, i.val = 0 := by cega [batch := 1]); trivial
    | trivial

/-! A failing `cega [fast]` without native checking runs the semantic routes and the finite
certificate once: the trace shows one finite-certificate attempt. -/

/--
trace: [cega.native] Checking finite certificate applicability (native requested: false)
[cega.native] Starting finite Decidable synthesis
[cega.native] Finite Decidable synthesis completed
[cega.native] Using the finite kernel certificate profile
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.native true in
example : ∀ i : Fin 1, (List.range 100).foldl (· + ·) 0 = i.val := by
  cega [fast]

end CAS.Examples.CEGA.Trust
