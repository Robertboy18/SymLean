/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import CAS.Numerics.Tactic

/-!
# The documented forms of the tactics

The hover of a tactic shows its docstring followed by the entries of its other forms, whatever
form the cursor is on. Each form of `cas`, `cas_nf` and `cega` has its own entry, which starts
with the form, and `cas?` and `cega?` take the arguments of `cas` and `cega`. The same holds for
the reflected tactics `symbolic_eq` and `symbolic_alg_zero_side`.
-/

open Lean

/-- The first code span of the docstring of `tactic` and of each entry appended to it. -/
def documentedForms (tactic : Name) : CoreM (List String) := do
  let some doc ← findDocString? (← getEnv) tactic | throwError "{tactic} has no docstring"
  let firstSpan (text : String) : String := ((text.splitOn "`")[1]?).getD ""
  match doc.splitOn "\n\nExtensions:\n\n" with
  | [main, entries] => return firstSpan main :: (entries.splitOn "\n\n * ").map firstSpan
  | _ => return [firstSpan doc]

/--
info: [cas, cas using h, cas using [h₁, h₂], cas [l₁, l₂], cas [integrate primitive := F]]
[cas_nf, cas_nf using h]
[cega,
 cega [fast],
 cega (prec := n) (depth := n) (panels := n),
 cega [enclose ...] expr,
 cega using carrier,
 cega [batch := n],
 cega [fast, batch := n]]
[cas?]
[cega?]
[symbolic_eq, symbolic_eq [l₁, l₂]]
[symbolic_alg_zero_side, symbolic_alg_zero_side [l₁, l₂]]
-/
#guard_msgs in
run_meta do
  let tactics := [``CAS.ExactTactic.tacticCas, ``CAS.ExactTactic.tacticCas_nf_,
    ``CAS.CEGA.tacticCega, ``CAS.tacticCas?, ``CAS.tacticCega?, ``CAS.symbolicEq,
    ``CAS.symbolicAlgZeroSide]
  let lines ← tactics.mapM fun tactic ↦ do return m!"{← documentedForms tactic}"
  logInfo (MessageData.joinSep lines "\n")
