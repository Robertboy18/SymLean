/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# Native certificates do not reach kernel routes

With `cega.nativeCertificates`, `cega [fast]` proves a statement by native evaluation. A later
kernel route for the same statement (bare `cega`, `cega` on a box, core `decide +kernel`), in
the same declaration or a later one, must not reuse that proof. `run.sh` elaborates this file
twice, with `Elab.async` false (all declarations share one environment branch, where the
auxiliary-lemma cache could hand the native lemma on) and with the default. Each test uses its
own statement, so that the tests do not share cache entries.
-/

open Lean Meta in
/-- The number of native axioms (`_native.cegaFast.ax_*`) behind a declaration, and whether it
uses any other nonstandard axiom. -/
def nativeAxioms (name : Name) : MetaM (Nat × Bool) := do
  let found ← CAS.Tactic.ProofCarrier.nonstandardAxioms (mkConst name)
  let native := found.filter fun (axiomName, _) ↦
    (axiomName.components.map toString).contains "_native"
  return (native.size, native.size < found.size)

set_option cega.nativeCertificates true in
theorem fastFinite : ∀ i : Fin 32, (i.val : ℤ) ^ 2 < 1024 := by
  cega [fast]

theorem kernelFinite : ∀ i : Fin 32, (i.val : ℤ) ^ 2 < 1024 := by
  cega

-- Core `decide +kernel` right after a native `cega [fast]` of the same statement, with no
-- kernel `cega` in between that could have repaired the cache.
set_option cega.nativeCertificates true in
theorem fastFinite' : ∀ i : Fin 30, (i.val : ℤ) ^ 2 < 900 := by
  cega [fast]

theorem kernelDecide : ∀ i : Fin 30, (i.val : ℤ) ^ 2 < 900 := by
  decide +kernel

set_option cega.nativeCertificates true in
theorem fastBox (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]

theorem kernelBox (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega

/-- Natural intervals lose the dependency in `x * (1 - x)`, so the native polynomial route
fails and the kernel fallback proves the bound. -/
theorem fastFallback (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  set_option cega.nativeCertificates true in cega [fast]

/-- A false finite statement is refused by native evaluation and by the kernel fallback. -/
example : True := by
  fail_if_success
    have : ∀ i : Fin 1, (List.range 1000).foldl (· + ·) 0 = i.val := by
      set_option cega.nativeCertificates true in cega [fast]
  trivial

/-- Both conjuncts in one declaration: the kernel conjunct must not share the native lemma. -/
theorem shared :
    (∀ i : Fin 33, (i.val : ℤ) ^ 2 < 1089) ∧ (∀ i : Fin 33, (i.val : ℤ) ^ 2 < 1089) := by
  constructor
  · set_option cega.nativeCertificates true in cega [fast]
  · cega

/-- A kernel proof earlier in the same declaration is reused by native `cega [fast]` for the same
statement, finite and box alike, instead of adding a native certificate. -/
theorem kernelFirst :
    ((∀ i : Fin 29, (i.val : ℤ) ^ 2 < 841) ∧ (∀ i : Fin 29, (i.val : ℤ) ^ 2 < 841)) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * x ≤ 2) ∧ (∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * x ≤ 2) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · cega
  · set_option cega.nativeCertificates true in cega [fast]
  · cega
  · set_option cega.nativeCertificates true in cega [fast]

/-- info: fastFinite (1, false), kernelFinite (0, false), fastFinite' (1, false),
kernelDecide (0, false), fastBox (1, false), kernelBox (0, false), fastFallback (0, false),
kernelFirst (0, false) -/
#guard_msgs (whitespace := lax) in
open Lean Meta in
run_meta do
  let names := [`fastFinite, `kernelFinite, `fastFinite', `kernelDecide, `fastBox, `kernelBox,
    `fastFallback, `kernelFirst]
  let parts ← names.mapM fun name ↦ do return m!"{name} {← nativeAxioms name}"
  logInfo (MessageData.joinSep parts ", ")

set_option linter.unusedTactic false in
/-- A kernel proof of a box goal is reused by native `cega [fast]` for the same goal even after a
search of the same query, since rolled back, has left its reduction in the memo table. -/
theorem kernelThenMemo :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * x ≤ 3) ∧ (∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * x ≤ 3) := by
  refine ⟨?_, ?_⟩
  · cega
  · try (intro x h0 h1
         cega? [enclose x in [0, 1]] (x * x)
         fail)
    set_option cega.nativeCertificates true in cega [fast]

/-- info: kernelThenMemo (0, false) -/
#guard_msgs in
open Lean Meta in
run_meta logInfo m!"kernelThenMemo {← nativeAxioms `kernelThenMemo}"

/-- info: native conjunct: 1, kernel conjunct: 0 -/
#guard_msgs in
open Lean Meta in
run_meta do
  let some value := ((← getEnv).find? `shared).bind (·.value? (allowOpaque := true))
    | throwError "no value for `shared`"
  let count (proof : Expr) : MetaM Nat := do
    return (← CAS.Tactic.ProofCarrier.nonstandardAxioms proof).size
  logInfo m!"native conjunct: {← count value.getAppArgs[2]!}, \
    kernel conjunct: {← count value.getAppArgs[3]!}"
