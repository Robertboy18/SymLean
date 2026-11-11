/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public meta import CAS.Numerics.Binary64

/-!
# Tables stored as blocks of packed slots

`json_slot_blocks% enc w q text key n` reads the `n` entries of the integer column `key` (a
dotted path to an array) of the JSON document `text` and returns a function `ℕ → ℕ`: block `b`
is one natural literal holding the entries `q * b` to `q * b + q - 1` in slots of width `w`, the
first entry lowest. Block indices past the end return the last block.

The encoding `enc` is `nat` for natural entries, `biased` for signed entries stored as
`c + slotBias w` (read back by `signedSlot`), and `zigzag` for signed entries stored as
`2 * |c| + (if c < 0 then 1 else 0)` (read back by `signedCoefficient`). The importer rejects
entries that do not fit `w` bits after encoding. With a field,
`json_slot_blocks% enc w q text key field n` reads the integer at the dotted path `field` of
every record of the array `key`, so a table of records is stored as one block table per field.
A path component that is a natural number selects that entry of an array: the field `"3.1"` of
the rows of an array of arrays of pairs is the second endpoint of the fourth pair of every row.

`blockSlot w q blocks i` is entry `i` of such a table and `blockSignedSlot` its biased signed
reading.

## Implementation notes

Each block is packed by balanced shifts and stored by `mkCompactNatLiteral` as a named
irreducible auxiliary definition, and the function the elaborator returns selects the literals
by a balanced `cond` tree of `Nat.blt` comparisons on the block index. `blockSlot` divides the
index by `q` once, so a kernel lookup reduces one comparison per level of the tree, then one
shift and one mask of a literal of `q * w` bits, and never visits the rest of the table, where
one literal for the whole table would make every read shift all of it. Importing a table
establishes nothing about its entries; certificates check them.
[ZigzagBlocks](ZigzagBlocks.lean) certifies signed products of zigzag tables read by
`blockSlot`.
-/

@[expose] public section

namespace CAS.Numerics

/-- Entry `i` of a table stored in blocks of `q` slots of width `w`: slot `i % q` of block
`i / q`. -/
def blockSlot (w q : ℕ) (blocks : ℕ → ℕ) (i : ℕ) : ℕ :=
  slot w (Nat.mod i q) (blocks (Nat.div i q))

/-- The biased signed reading of entry `i` of a table stored in blocks of `q` slots. -/
def blockSignedSlot (w q : ℕ) (blocks : ℕ → ℕ) (i : ℕ) : ℤ :=
  signedSlot w (Nat.mod i q) (blocks (Nat.div i q))

/-- The signed reading of entry `i` is the entry `blockSlot w q blocks i` minus `slotBias w`. -/
theorem blockSignedSlot_eq (w q : ℕ) (blocks : ℕ → ℕ) (i : ℕ) :
    blockSignedSlot w q blocks i = (blockSlot w q blocks i : ℤ) - slotBias w := rfl

end CAS.Numerics

end

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- `json_slot_blocks% enc w q text key (field)? n` imports the `n` entries of the integer column
`key` of `text`, or the field `field` of the records of the array `key`, as blocks of `q` slots of
width `w`, encoded by `enc` (`nat`, `biased` or `zigzag`). -/
syntax (name := jsonSlotBlocks) "json_slot_blocks% " ident num num term:max str (str)? num : term

/-- Follow a dotted path of object fields; a natural-number component selects an array entry. -/
private def jsonPath (value : Json) (path : String) : Except String Json :=
  path.splitOn "." |>.foldlM (fun (object : Json) field ↦
    match object, field.toNat? with
    | .arr entries, some i =>
      match entries[i]? with
      | some entry => pure entry
      | none => throw s!"index {i} is past the end of an array of {entries.size} entries"
    | _, _ => object.getObjVal? field) value

/-- The `count` integers of the array at `key`, or of the field `field` of its records. -/
private def blockColumn (text key : String) (field : Option String) (count : Nat) :
    TermElabM (Array Int) := do
  let json ← ofExcept (Json.parse text)
  let entries ← ofExcept ((jsonPath json key) >>= fun array ↦ array.getArr?)
  unless entries.size == count do
    throwError "JSON column '{key}' has {entries.size} entries; expected {count}"
  entries.mapIdxM fun i entry ↦ do
    let value := match field with
      | some path => jsonPath entry path
      | none => pure entry
    match value >>= integerEntry with
    | .ok value => pure value
    | .error error => throwError "JSON column '{key}', entry {i}: {error}"

/-- Encode one entry as a slot value, or explain why it does not fit. -/
private def encodeBlockEntry (encoding : Name) (width : Nat) (value : Int) :
    Except String Nat := do
  let encoded : Int ← match encoding with
    | `nat => if value < 0 then throw "negative entry in a natural table" else pure value
    | `biased => pure (value + Int.ofNat ((1 <<< width) >>> 1))
    | `zigzag => pure (Int.ofNat (2 * value.natAbs + if value < 0 then 1 else 0))
    | _ => throw "unknown encoding; expected nat, biased or zigzag"
  unless 0 ≤ encoded && encoded < Int.ofNat (1 <<< width) do
    throw s!"entry {value} does not fit {width} bits"
  return encoded.toNat

/-- A balanced `cond` tree on the bound block index selecting the literals `lo` to `hi - 1`. -/
private partial def blockTree (literals : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then literals[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (mkConst ``cond [Level.one]) (mkConst ``Nat)
      (mkApp2 (mkConst ``Nat.blt) (.bvar 0) (mkNatLit mid))
      (blockTree literals lo mid) (blockTree literals mid hi)

/-- Elaborate `json_slot_blocks%`: read and encode the column, pack each block into a named
literal, and return the block selector. -/
@[term_elab jsonSlotBlocks] def elabJsonSlotBlocks : TermElab := fun stx _ ↦ do
  let `(json_slot_blocks% $enc:ident $w:num $q:num $text $key:str $[$field:str]? $n:num) := stx
    | throwUnsupportedSyntax
  let width := w.getNat
  let perBlock := q.getNat
  unless 0 < width && 0 < perBlock do
    throwError "json_slot_blocks% needs a positive width and block length"
  let values ← blockColumn (← evalString text) key.getString (field.map (·.getString)) n.getNat
  let slots ← values.mapIdxM fun i value ↦ do
    match encodeBlockEntry enc.getId width value with
    | .ok slot => pure slot
    | .error error => throwError "JSON column '{key.getString}', entry {i}: {error}"
  let blockCount := max 1 ((slots.size + perBlock - 1) / perBlock)
  let mut literals := #[]
  for b in [:blockCount] do
    let start := b * perBlock
    let count := min perBlock (slots.size - start)
    let name ← mkAuxDeclName `_slotBlock
    let literal ← mkCompactNatLiteral name (packSlotValues width slots start count)
    -- Blocks stay data during elaboration; kernel and compiled checks read their bodies.
    setReducibilityStatus name .irreducible
    literals := literals.push literal
  return mkLambda `block .default (mkConst ``Nat) (blockTree literals 0 literals.size)

end CAS.Numerics
