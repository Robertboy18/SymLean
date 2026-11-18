/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS.Numerics.BinaryGridEvaluation
import CAS.Numerics.BinaryGridShards
import CAS.Numerics.Tactic

/-!
# A grid table read from a file

The modules that use `binary_grid_shard` and the JSON importers give them `include_str "file"`.
The examples of the library give them string literals instead: a library that tracks its
embedded files rebuilds all its modules when it gains one. This file reads the snapshot
`grid.json` next to it, so the command, `packed_int_rows%` inside it and `json_data%` run on a
text that comes through the check of `include_str` (`CAS/IncludeStr.lean`).
-/

open CAS.Numerics FloatLib.Numerics.Interval

/-- The source of the snapshot, two rows of three sixteenths: entry `(m, l)` is
`(3 * m + l - 7) / 16`. -/
def fileSource (m : Fin 2) (l : Fin 3) : ℚ := ((3 * m.val + l.val : ℤ) - 7) / 16

binary_grid_shard fileGrid (leaf := fileLeaf) (row := fileRow)
  (source := fileSource) (offset := 0) (check := fileSource_eq_fileGrid)
  (include_str "grid.json")

example (m : Fin 2) (l : Fin 3) :
    fileSource ⟨0 + m.val, by have := m.isLt; omega⟩ l = BinaryGrid.toRat 4 (fileGrid m l) :=
  fileSource_eq_fileGrid m l

example : (List.finRange 2).map (fun m ↦ (List.finRange 3).map (fileGrid m)) =
    [[-7, -6, -5], [-4, -3, -2]] := by
  decide +kernel

/-- The numerators of the same file, read by `json_data%`. -/
def fileNumerators : Array ℤ := json_data% (include_str "grid.json") "numerators"

example : fileNumerators = #[-7, -6, -5, -4, -3, -2] := by decide +kernel
