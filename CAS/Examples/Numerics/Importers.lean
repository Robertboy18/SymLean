/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.CompactRows
public import CAS.Numerics.ComputedLiteral
public import CAS.Numerics.NatLiteral
public import CAS.Numerics.NatLiteralPrivate
public import CAS.Numerics.PackedJson
public import CAS.Numerics.PackedJsonLiteral
public import CAS.Numerics.SlotBlocks
public import CAS.Numerics.SlotWindows

-- `nat_literal%` evaluates `packSlots` during elaboration.
meta import CAS.Numerics.PackedSlots

-- `nat_literal_priv%` evaluates `listRowSum`, which this module does not export.
import CAS.Numerics.PackedListComb
meta import CAS.Numerics.PackedListComb

/-!
# The data importers on small inputs

Each term elaborator of `CAS/Numerics` that reads data during elaboration runs here on a small
input, and the kernel reads every stored entry back: `binary64_words%`, `binary64_word_rows%`,
`hex_rows%`, `hex_lower_rows%`, `computed_rows%`, `computed_nat%`, `nat_literal%`,
`nat_literal_priv%`, `json_data%`, `packed_int_rows%`, `packed_int_literal%`,
`json_slot_blocks%`, `json_slot_windows%` and `json_slot_array%`. The library itself calls none
of them, since its tables belong to the projects that use it, so without these runs a fault that
shows only when an importer runs would pass the build of SymLean (`BUGS.md`, N57).

The ten importers that read text get string literals here; `tests/docs/GridFile.lean` reads a
file with `include_str`, outside the library, whose build tracks every such file. An importer
establishes nothing about the entries it stores; the examples below are the checks. The
literals here have fewer than 4096 bits: a larger one gets a compiled implementation, which
`scripts/audit.sh` lists, so `tests/docs/CompactLiteral.lean` runs `nat_literal%` and
`computed_nat%` on such values outside the library.
-/

@[expose] public section

namespace CAS.Examples.Numerics.Importers

open CAS.Numerics

/-! ## Binary64 words -/

/-- The binary64 words of `1` and `-2`. -/
def words : Binary64WordTree 2 := binary64_words% "3ff0000000000000c000000000000000"

example : words.get 0 = 0x3ff0000000000000 ∧ words.get 1 = 0xc000000000000000 ∧
    words.value 0 = 1 ∧ words.value 1 = -2 := by
  decide +kernel

/-- Four words in two rows of two. -/
def wordRows : Binary64WordTree 2 :=
  binary64_word_rows% 2 "0000000000000001000000000000000200000000000000030000000000000004"

example : slot 64 0 (wordRows.get 0) = 1 ∧ slot 64 1 (wordRows.get 0) = 2 ∧
    slot 64 0 (wordRows.get 1) = 3 ∧ slot 64 1 (wordRows.get 1) = 4 := by
  decide +kernel

/-! ## Hexadecimal rows

An entry is one digit for its length, or `0` and three digits for a length above 15, then
that many digits of `2 * c` for `c ≥ 0` and of `-2 * c - 1` for `c < 0`. The entries below have
one digit each. -/

/-- The rows `1, -1, 2` and `-3, 0, 5`. -/
def hexTable : Binary64WordTree 2 := hex_rows% 4 3 "12 11 14 15 10 1a"

example : signedSlot 4 0 (hexTable.get 0) = 1 ∧ signedSlot 4 1 (hexTable.get 0) = -1 ∧
    signedSlot 4 2 (hexTable.get 0) = 2 ∧ signedSlot 4 0 (hexTable.get 1) = -3 ∧
    signedSlot 4 1 (hexTable.get 1) = 0 ∧ signedSlot 4 2 (hexTable.get 1) = 5 := by
  decide +kernel

/-- The rows `1, -2` and `0, 3`, of which the text holds the entries from the diagonal on. -/
def hexTriangle : Binary64WordTree 2 := hex_lower_rows% 4 2 "12 13 16"

example : signedSlot 4 0 (hexTriangle.get 0) = 1 ∧ signedSlot 4 1 (hexTriangle.get 0) = -2 ∧
    signedSlot 4 0 (hexTriangle.get 1) = 0 ∧ signedSlot 4 1 (hexTriangle.get 1) = 3 := by
  decide +kernel

/-! ## Computed rows and literals -/

/-- Row `i` holds `i` and `i * i`. -/
def squareRows : Binary64WordTree 3 := computed_rows% 8 2 (fun i ↦ #[i, i * i])

example : ∀ i : Fin 3, slot 8 0 (squareRows.get i) = i.val ∧
    slot 8 1 (squareRows.get i) = i.val * i.val := by
  decide +kernel

example : computed_nat% (Nat.pow 2 10 + 1) = 1025 := rfl

/-- The entries `1, 2, 3` packed by `packSlots`, whose module this file imports with
`meta import`. -/
def literal : ℕ := nat_literal% (packSlots 8 3 fun i ↦ i + 1)

example : ∀ i : Fin 3, slot 8 i.val literal = i.val + 1 := by decide +kernel

/-- A literal whose term names `listRowSum`, a definition of a module that this file imports
without `public`. -/
def literalPrivate : ℕ := nat_literal_priv% (listRowSum [1, 2, 3])

example : literalPrivate = 6 := by decide +kernel

/-! ## JSON -/

/-- Rationals written as an integer, a string and an object. -/
def weights : Array ℚ :=
  json_data% r#"{"w": [1, "3/10", {"numerator": -5, "denominator": 8}]}"# "w"

example : weights = #[1, 3 / 10, -5 / 8] := by decide +kernel

/-- A record with a pair and an optional field. -/
structure Sample where
  /-- The label. -/
  label : String
  /-- The count. -/
  count : ℕ
  /-- Two signed bounds. -/
  bounds : ℤ × ℤ
  /-- An optional note. -/
  note : Option ℕ
  deriving DecidableEq

/-- A record read from a JSON object, with a decimal string and `null`. -/
def sample : Sample :=
  json_data% r#"{"label": "a", "count": 3, "bounds": [-1, "2"], "note": null}"#

example : sample = ⟨"a", 3, (-1, 2), none⟩ := by decide +kernel

/-- Signed rows of three entries in slots of four bits. -/
def packedRows : Binary64WordTree 2 :=
  packed_int_rows% 4 3 r#"{"a": [1, -2, 3, "4", -5, 6]}"# "a"

example : (List.finRange 2).map (fun m ↦ (List.range 3).map (signedSlot 4 · (packedRows.get m))) =
    [[1, -2, 3], [4, -5, 6]] := by
  decide +kernel

/-- Three signed entries in one literal. -/
def packedLiteral : ℕ := packed_int_literal% 4 3 r#"{"a": [1, "-2", 3]}"# "a"

example : signedSlot 4 0 packedLiteral = 1 ∧ signedSlot 4 1 packedLiteral = -2 ∧
    signedSlot 4 2 packedLiteral = 3 := by
  decide +kernel

/-- Five signed entries in blocks of two. -/
def blocks : ℕ → ℕ := json_slot_blocks% biased 4 2 r#"{"a": [1, -2, 3, -4, 5]}"# "a" 5

example : (List.range 5).map (blockSignedSlot 4 2 blocks) = [1, -2, 3, -4, 5] := by
  decide +kernel

/-- The field `c` of three records, in blocks of two. -/
def fieldBlocks : ℕ → ℕ :=
  json_slot_blocks% nat 4 2 r#"{"rows": [{"c": 1}, {"c": 2}, {"c": 3}]}"# "rows" "c" 3

example : (List.range 3).map (blockSlot 4 2 fieldBlocks) = [1, 2, 3] := by decide +kernel

/-- Two windows, of two and of three entries. -/
def windows : ℕ → ℕ :=
  json_slot_windows% 4 r#"{"a": [1, 2, 3, 4, 5], "o": [0, 2, 5]}"# "a" "o" 2

example : (List.range 2).map (slot 4 · (windows 0)) = [1, 2] ∧
    (List.range 3).map (slot 4 · (windows 1)) = [3, 4, 5] := by
  decide +kernel

/-- Three entries of two rows in one literal. -/
def slotArray : ℕ := json_slot_array% 4 r#"{"a": [[1, 2], [3]]}"# "a" 3

example : slot 4 0 slotArray = 1 ∧ slot 4 1 slotArray = 2 ∧ slot 4 2 slotArray = 3 := by
  decide +kernel

end CAS.Examples.Numerics.Importers
