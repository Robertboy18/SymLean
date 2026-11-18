/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.BinaryGridEvaluation
public import CAS.Numerics.PackedSlots
public import CAS.Numerics.Tactic
import CAS.Numerics.BinaryGridShards

/-!
# Grid tables read by `binary_grid_shard`

`binary_grid_shard` and `fin_cases_blocks` run here on small snapshots, so that a fault that
shows only when the command runs stops the build of the library. No module of SymLean called the
command before: on Lean 4.36 it failed in every downstream module that called it, while SymLean
built (`BUGS.md`, N56).

The source `table 7` has four rows of three sixteenths. Two snapshots of two rows each hold its
numerators, as JSON integers and as decimal strings; `grid` joins the two blocks, and
`table_eq_grid` joins their replays with `fin_cases_blocks`. A third snapshot has one row,
numerators of 98 bits and a source that is a constant without arguments. The examples check the
types of the declarations of the second block, the statements of two replays, every numerator
of the three snapshots, and the docstrings of all twelve generated declarations. Two calls are
refused and declare nothing: a snapshot that starts at another source row, and one with a
numerator too few.
-/

@[expose] public section

namespace CAS.Examples.Numerics.BinaryGridShards

open CAS.Numerics FloatLib.Numerics.Interval

/-- A source table of four rows and three columns: entry `(m, l)` is
`(3 * m + l - shift) / 16`. -/
def table (shift : ℤ) (m : Fin 4) (l : Fin 3) : ℚ := ((3 * m.val + l.val : ℤ) - shift) / 16

binary_grid_shard gridBlock0 (leaf := gridLeaf0) (row := gridRow0)
  (source := table 7) (offset := 0) (check := table_eq_gridBlock0)
  r#"{"precision": 4, "shape": [2, 3], "sourceRowOffset": 0,
    "numerators": [-7, "-6", -5, -4, "-3", -2]}"#

binary_grid_shard gridBlock1 (leaf := gridLeaf1) (row := gridRow1)
  (source := table 7) (offset := 2) (check := table_eq_gridBlock1)
  r#"{"precision": 4, "shape": [2, 3], "sourceRowOffset": 2,
    "numerators": [-1, 0, 1, "2", 3, 4]}"#

/-! ## The generated declarations -/

example : Binary64WordTree 2 := gridLeaf1

example : Fin 2 → Fin 3 → ℤ := gridRow1

example : Fin 2 → Fin 3 → ℤ := gridBlock1

example (m : Fin 2) (l : Fin 3) :
    table 7 ⟨2 + m.val, by have := m.isLt; omega⟩ l = BinaryGrid.toRat 4 (gridBlock1 m l) :=
  table_eq_gridBlock1 m l

/-- The docstrings of `names`, each quoted, one per line. -/
meta def generatedDocs (names : List Lean.Name) : Lean.MetaM String := do
  let docs ← names.mapM fun name ↦ do
    let some doc ← Lean.findDocString? (← Lean.getEnv) name
      | throwError "{name} has no docstring"
    return doc.quote
  return "\n".intercalate docs

/--
info: " Source rows 0 through 1 as packed rows of biased 4-bit slots. "
" Column `l` of source row `0 + m`, decoded from its slot. "
" The integer numerators of source rows 0 through 1. "
" Every block numerator represents its source entry exactly. "
" Source rows 2 through 3 as packed rows of biased 4-bit slots. "
" Column `l` of source row `2 + m`, decoded from its slot. "
" The integer numerators of source rows 2 through 3. "
" Every block numerator represents its source entry exactly. "
-/
#guard_msgs in
run_meta do
  Lean.logInfo (← generatedDocs [``gridLeaf0, ``gridRow0, ``gridBlock0, ``table_eq_gridBlock0,
    ``gridLeaf1, ``gridRow1, ``gridBlock1, ``table_eq_gridBlock1])

/-! ## Blocks joined by `fin_cases_blocks` -/

/-- The numerators of the four source rows, from the two blocks of two rows. -/
def grid (m : Fin 4) (l : Fin 3) : ℤ :=
  ![gridBlock0, gridBlock1] ⟨m.val / 2, by have := m.isLt; omega⟩
    ⟨m.val % 2, Nat.mod_lt _ (by decide)⟩ l

/-- Every numerator is the one of its snapshot, those written as decimal strings among them. -/
example : (List.finRange 4).map (fun m ↦ (List.finRange 3).map (grid m)) =
    [[-7, -6, -5], [-4, -3, -2], [-1, 0, 1], [2, 3, 4]] := by
  decide +kernel

section Join

-- As for a large table: the replays are reindexed without unfolding the data.
attribute [local irreducible] table BinaryGrid.toRat gridBlock0 gridBlock1

/-- Every numerator represents its source entry: the replays of the two blocks, joined by
`fin_cases_blocks`. -/
theorem table_eq_grid (m : Fin 4) (l : Fin 3) : table 7 m l = BinaryGrid.toRat 4 (grid m l) := by
  fin_cases_blocks m 2 table_eq_gridBlock l

end Join

/-! ## A wide numerator and a source without arguments -/

/-- A source of one row whose numerators have 98 bits on the grid of halves: entry `l` is
`l - 123456789012345678901234567890`. -/
def wide (_ : Fin 1) (l : Fin 2) : ℚ :=
  ((2 * l.val : ℤ) - 246913578024691357802469135780) / 2

binary_grid_shard wideGrid (leaf := wideLeaf) (row := wideRow)
  (source := wide) (offset := 0) (check := wide_eq_wideGrid)
  r#"{"precision": 1, "shape": [1, 2], "sourceRowOffset": 0,
    "numerators": ["-246913578024691357802469135780", "-246913578024691357802469135778"]}"#

example (m : Fin 1) (l : Fin 2) :
    wide ⟨0 + m.val, by have := m.isLt; omega⟩ l = BinaryGrid.toRat 1 (wideGrid m l) :=
  wide_eq_wideGrid m l

example : wideGrid 0 0 = -246913578024691357802469135780 ∧
    wideGrid 0 1 = -246913578024691357802469135778 := by
  decide +kernel

/--
info: " Source rows 0 through 0 as packed rows of biased 99-bit slots. "
" Column `l` of source row `0 + m`, decoded from its slot. "
" The integer numerators of source rows 0 through 0. "
" Every block numerator represents its source entry exactly. "
-/
#guard_msgs in
run_meta do
  Lean.logInfo (← generatedDocs [``wideLeaf, ``wideRow, ``wideGrid, ``wide_eq_wideGrid])

/-! ## Refused snapshots -/

/-- error: the snapshot starts at source row 2, not 0 -/
#guard_msgs in
binary_grid_shard shifted (leaf := shiftedLeaf) (row := shiftedRow)
  (source := table 7) (offset := 0) (check := table_eq_shifted)
  r#"{"precision": 4, "shape": [2, 3], "sourceRowOffset": 2,
    "numerators": [-1, 0, 1, 2, 3, 4]}"#

/-- error: invalid grid snapshot: expected 6 numerators, found 5 -/
#guard_msgs in
binary_grid_shard short (leaf := shortLeaf) (row := shortRow)
  (source := table 7) (offset := 2) (check := table_eq_short)
  r#"{"precision": 4, "shape": [2, 3], "sourceRowOffset": 2,
    "numerators": [-1, 0, 1, 2, 3]}"#

/-- info: none of the refused calls declared a constant -/
#guard_msgs in
run_meta do
  let env ← Lean.getEnv
  let names := [`shifted, `shiftedLeaf, `shiftedRow, `table_eq_shifted, `short, `shortLeaf,
    `shortRow, `table_eq_short]
  if names.any fun name ↦ env.contains (`CAS.Examples.Numerics.BinaryGridShards ++ name) then
    throwError "a refused call declared a constant"
  Lean.logInfo "none of the refused calls declared a constant"

end CAS.Examples.Numerics.BinaryGridShards
