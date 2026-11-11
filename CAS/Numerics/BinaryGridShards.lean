/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import CAS.Numerics.PackedJson
import CAS.Numerics.Tactic
public import CAS.Numerics.Json
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import CAS.Numerics.PackedJson

/-!
# Integer-grid tables read from JSON

A grid snapshot is a JSON object with fields `precision`, `shape = [rows, columns]`,
`sourceRowOffset` and `numerators`. The last field holds `rows * columns` integers in row-major
order, as JSON integers or decimal strings, and entry `(i, l)` represents the rational
`numerators[columns * i + l] / 2 ^ precision` at source row `sourceRowOffset + i`.

`binary_grid_shard N (leaf := L) (row := R) (source := f a) (offset := o) (check := T) text`
stores one snapshot as packed rows `L : Binary64WordTree rows`, read with `packed_int_rows%`:
row `i` is one natural number holding its numerators as biased signed slots, of the smallest
width that fits every numerator of the snapshot. `R i l` decodes slot `l` of row `i`, and the
block numerator is `N i l = R i l`. The command proves `T`, the replay
`f a (o + i) l = BinaryGrid.toRat precision (N i l)` for every row `i` and column `l`, with
`cega [fast, batch := 1]`. Modules that use the command import `CAS.Numerics.Tactic`.

`fin_cases_blocks m b P args` closes a goal over `m : Fin n` by `fin_cases m` followed by
`exact P{i / b} ⟨i % b, by decide⟩ args` in case `i`. Aggregates of blocks of `b` rows use it.

## Implementation notes

We elaborate the declarations that the corresponding source text would contain. A lookup
descends the balanced row tree and reads one slot, and the table costs about one slot width per
numerator in the module data. The JSON values are proposals, established only by the replays
against the source: in the default `kernel` certificate profile each row is checked as its own
kernel theorem, and the `fast` profile (`-Kcertificates=fast`) evaluates all rows once with
compiled code, which also trusts Lean's compiler and runtime. Each snapshot is passed as a
literal `include_str` path, so the facet `SymLean.embeddedInputs` of `lakefile.lean` records it
as an input of a library that needs it.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Lean.Elab.Command Term Meta Tactic

/-- A grid snapshot with a checked shape. -/
structure BinaryGridSnapshot where
  /-- Number of fractional bits of the common grid. -/
  precision : Nat
  /-- Number of source rows in the block. -/
  rows : Nat
  /-- Number of columns of each row. -/
  columns : Nat
  /-- Source index of the first row. -/
  offset : Nat
  /-- The integer numerators in row-major order. -/
  numerators : Array Int

/-- Parse a grid snapshot and check its shape. -/
def BinaryGridSnapshot.parse (text : String) : Except String BinaryGridSnapshot := do
  let json ← Json.parse text
  let precision ← json.getObjValAs? Nat "precision"
  let #[rows, columns] ← json.getObjValAs? (Array Nat) "shape"
    | throw "shape must be [rows, columns]"
  unless 0 < rows && 0 < columns do
    throw s!"shape [{rows}, {columns}] needs rows and columns"
  let offset ← json.getObjValAs? Nat "sourceRowOffset"
  let entries ← json.getObjValAs? (Array Json) "numerators"
  unless entries.size == rows * columns do
    throw s!"expected {rows * columns} numerators, found {entries.size}"
  return { precision, rows, columns, offset, numerators := ← entries.mapM integerEntry }

private def loadSnapshot (text : Term) : CommandElabM BinaryGridSnapshot := do
  match BinaryGridSnapshot.parse (← liftTermElabM (evalString text)) with
  | .ok snapshot => return snapshot
  | .error error => throwErrorAt text "invalid grid snapshot: {error}"

private def docComment (text : String) : TSyntax ``Parser.Command.docComment :=
  ⟨mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (" " ++ text ++ " -/")]⟩

private def suffixed (base : Ident) (suffix : String) : Ident :=
  mkIdent (base.getId.appendAfter suffix)

/-- Apply `source` to further arguments as one flat application. -/
private def applySource (source : Term) (args : Array Term) : CommandElabM Term :=
  match source with
  | `($f $xs*) => `($f $xs* $args*)
  | _ => `($source $args*)

/-- The smallest slot width holding every numerator of a snapshot with its bias. -/
def BinaryGridSnapshot.slotWidth (snapshot : BinaryGridSnapshot) : Nat :=
  (snapshot.numerators.foldl (fun (m : Nat) (v : Int) ↦ max m v.natAbs) 0).log2 + 2

set_option hygiene false in
private def gridShardCommands (numerator leaf row check : Ident) (source text : Term)
    (offset : Nat) (snapshot : BinaryGridSnapshot) :
    CommandElabM (Array Syntax × Array Syntax) := do
  let rowCount := quote snapshot.rows
  let columnCount := quote snapshot.columns
  let precision := quote snapshot.precision
  let width := quote snapshot.slotWidth
  let mut data : Array Syntax := #[]
  let doc := docComment s!"Source rows {offset} through {offset + snapshot.rows - 1} as packed \
    rows of biased {snapshot.slotWidth}-bit slots."
  data := data.push (← `($doc:docComment
    def $leaf : CAS.Numerics.Binary64WordTree $rowCount :=
      packed_int_rows% $width $columnCount $text "numerators"))
  let doc := docComment s!"Column `l` of source row `{offset} + m`, decoded from its slot."
  data := data.push (← `($doc:docComment
    def $row (m : Fin $rowCount) (l : Fin $columnCount) : Int :=
      CAS.Numerics.signedSlot $width l.val
        (CAS.Numerics.Binary64WordTree.get $leaf m)))
  let doc := docComment s!"The integer numerators of source rows {offset} through \
    {offset + snapshot.rows - 1}."
  data := data.push (← `($doc:docComment
    def $numerator (m : Fin $rowCount) (l : Fin $columnCount) : Int := $row m l))
  let index ← `(⟨$(quote offset) + m.val, by have := m.isLt; omega⟩)
  let entry ← applySource source #[index, mkIdent `l]
  let doc := docComment "Every block numerator represents its source entry exactly."
  let proof ← `($doc:docComment
    theorem $check (m : Fin $rowCount) (l : Fin $columnCount) :
        $entry = FloatLib.Numerics.Interval.BinaryGrid.toRat $precision ($numerator m l) := by
      have h : ∀ m : Fin $rowCount, ∀ l : Fin $columnCount,
          $entry = FloatLib.Numerics.Interval.BinaryGrid.toRat $precision ($numerator m l) := by
        cega [fast, batch := 1]
      exact h m l)
  return (data, #[proof])

/-- Declare one integer-grid table block read from a JSON snapshot, with its replay. -/
syntax (name := binaryGridShard) "binary_grid_shard " ident
  " (" &"leaf" " := " ident ")" " (" &"row" " := " ident ")"
  " (" &"source" " := " term ")" " (" &"offset" " := " num ")"
  " (" &"check" " := " ident ")" ppSpace term:max : command

/-- Elaborate `binary_grid_shard`: read the snapshot, check that it starts at source row
`offset`, declare the packed rows `leaf`, the decoder `row` and the numerators, and prove the
replay `check`. -/
@[command_elab binaryGridShard] def elabBinaryGridShard : CommandElab := fun stx ↦ do
  let `(binary_grid_shard $numerator:ident (leaf := $leaf:ident) (row := $row:ident)
      (source := $source) (offset := $offset:num) (check := $check:ident) $text) := stx
    | throwUnsupportedSyntax
  let snapshot ← loadSnapshot text
  unless snapshot.offset == offset.getNat do
    throwErrorAt text "the snapshot starts at source row {snapshot.offset}, not {offset.getNat}"
  let (data, proofs) ← gridShardCommands numerator leaf row check source text offset.getNat
    snapshot
  for command in data do
    withEnableInfoTree false <| elabCommand command
  for command in proofs do
    elabCommand command

/-- Close a goal over `m : Fin n` with block lemmas `P0, P1, …` covering `b` indices each. -/
syntax (name := finCasesBlocks) "fin_cases_blocks " ident num ident (ppSpace colGt term:max)* :
  tactic

private def finCasesCount (m : Ident) : TacticM Nat := withMainContext do
  let some decl := (← getLCtx).findFromUserName? m.getId
    | throwErrorAt m "unknown variable {m}"
  let type ← whnf (← instantiateMVars decl.type)
  unless type.isAppOfArity ``Fin 1 do
    throwErrorAt m "{m} must have type Fin n"
  let some n ← (evalNat type.appArg!).run
    | throwErrorAt m "{m} must have type Fin n for a numeral n"
  return n

private def runFinCasesBlocks (m : Ident) (size : Nat) (family : Ident) (args : Array Term) :
    TacticM Unit := do
  let n ← finCasesCount m
  evalTactic (← `(tactic| fin_cases $m:ident))
  for i in [0:n] do
    let block := suffixed family s!"{i / size}"
    let index ← `(⟨$(quote (i % size)), by decide⟩)
    evalTactic (← `(tactic| · exact $block $index $args*))

/-- Elaborate `fin_cases_blocks m b P args`: split `m` with `fin_cases` and close case `i` by
`P{i / b} ⟨i % b, by decide⟩ args`. -/
@[tactic finCasesBlocks] def evalFinCasesBlocks : Tactic := fun stx ↦ do
  let `(tactic| fin_cases_blocks $m:ident $size:num $family:ident $args*) := stx
    | throwUnsupportedSyntax
  runFinCasesBlocks m size.getNat family args

end CAS.Numerics
