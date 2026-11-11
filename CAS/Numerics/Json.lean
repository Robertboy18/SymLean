/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.IncludeStr
public meta import Lean.Elab.Eval
import Lean.Structure

/-!
# Exact data from JSON

`json_data% text` imports the expected data type: `Nat`, `Int`, `Rat`, `Bool`, `String`,
arrays, lists, options (`null` is `none`), pairs and nested structures. Integers may be JSON
integers or decimal strings, so producers need not round large integers through floating
point. Pairs accept two-element JSON arrays or objects with `fst` and `snd` fields. A rational
is an integer, a string such as `"3/10"`, or an object with integer `numerator` and positive
`denominator` fields. An optional dotted key such as `"parameters.denominator"` selects a nested
entry of the document. Field names and types come from the Lean structure; proof fields are
rejected.

For files, use `include_str` as the text argument, with its path one string literal. A library
whose `needs` list `` `@/‹library›:SymLean.embeddedInputs `` tracks the embedded files, so editing
one rebuilds its modules; the libraries of SymLean do. The resulting declarations contain the
values, not runtime file reads.

## Implementation notes

`evalString` reads the text once, during elaboration, and Lean's `Json.parse` parses it;
`dataLiteral` then follows the expected type and writes each value as a term. Natural numbers
and integers become numerals, a rational the quotient of two numerals, the form that Mathlib's
normalization and CAS work with, and a structure the application of its constructor to fields
looked up by name. A list is built as an array, and a large array is a balanced append whose
branches are named auxiliary definitions (above `64` entries, or `8` when the entries are arrays
or lists), so kernel terms and compiled code stay shallow; the branches are irreducible during
elaboration, so unification never expands a table, while kernel reduction and compiled code
still evaluate them. The kernel checks only that the term has its type: the constants are data,
and CEGA must still prove their certificate checks. The other text importers read their text
with `evalString`, and the packed JSON importers ([PackedJson](PackedJson.lean),
[SlotBlocks](SlotBlocks.lean) and the others) read integers with `columnValues` or
`integerEntry`.

The file tracking is the library facet `SymLean.embeddedInputs` of `lakefile.lean`, a text search
of the library's modules, with the check of `CAS.IncludeStr`, which accepts an `include_str` only
when its path is one string literal in the module's file, right after the keyword. This module
imports the check publicly, so every module that can use `json_data%` has it. In a library that
lists the facet, every file read through `include_str` is then tracked, or the build stops,
except for code that reads a file on purpose by other means: code that reads it itself, builds
`include_str` from pieces of text at run time or elaborates it under a file map of its own, and
macros from outside the workspace, which means Lean's, none of which produces `include_str`.
`CAS.IncludeStr` gives the rules of the facet.
-/

public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- An integer from a JSON integer or a decimal string. -/
def integerEntry (entry : Json) : Except String Int := do
  match entry with
  | .str value =>
    match value.toInt? with
    | some value => return value
    | none => throw "expected a decimal integer string"
  | _ => entry.getInt?

/-- The integer column `key` of a JSON document, with exactly `count` entries. -/
def columnValues (text key : String) (count : Nat) : TermElabM (Array Int) := do
  let json ← ofExcept (Json.parse text)
  let entries ← ofExcept (json.getObjValAs? (Array Json) key)
  unless entries.size == count do
    throwError "JSON column '{key}' has {entries.size} entries; expected {count}"
  entries.mapIdxM fun i entry ↦ do
    match integerEntry entry with
    | .ok value => pure value
    | .error error => throwError "JSON column '{key}', entry {i}: {error}"

/-- Evaluate a string term such as `include_str "file"` during elaboration. -/
unsafe def evalStringUnsafe (text : TSyntax `term) : TermElabM String :=
  evalTerm String (mkConst ``String) text

/-- The value of a string term such as `include_str "file"`, read during elaboration. -/
@[implemented_by evalStringUnsafe]
opaque evalString (text : TSyntax `term) : TermElabM String

/-- Name large balanced branches so expressions and generated code stay shallow.
Short arrays remain inline; nested tables use smaller leaves to keep the
compiled code shallow without naming every row. -/
private partial def arrayLiteral (type : Expr) (values : Array Expr) : MetaM Expr := do
  let inlineLimit := if type.isAppOf ``Array || type.isAppOf ``List then 8 else 64
  if values.size ≤ inlineLimit then
    return ← mkArrayLit type values.toList
  let middle := values.size / 2
  let left ← arrayLiteral type (values.extract 0 middle)
  let right ← arrayLiteral type (values.extract middle values.size)
  let value := mkApp3 (mkConst ``Array.append [.zero]) type left right
  let name ← mkAuxDeclName `_jsonColumn
  let result ← mkAuxDefinitionFor (compile := true) name value
  -- Imported tables stay as data during elaboration. Explicit CEGA/kernel checks
  -- can evaluate the unchanged definition bodies and compiled code.
  setReducibilityStatus name .irreducible
  return result

/-- `json_data% text key`: the value of the expected data type read from the JSON document
`text`, or from its entry at the dotted path `key` when the key is given. -/
syntax (name := jsonData) "json_data% " term:max (str)? : term

private def rationalEntry (entry : Json) : Except String (Int × Int) := do
  let pair ← match entry with
    | .str value => do
      match value.splitOn "/" with
      | [numerator, denominator] =>
        pure (← integerEntry (.str numerator), ← integerEntry (.str denominator))
      | [integer] => pure (← integerEntry (.str integer), 1)
      | _ => throw "expected an exact rational string such as '5/8'"
    | .obj _ => do
      pure (← integerEntry (← entry.getObjVal? "numerator"),
        ← integerEntry (← entry.getObjVal? "denominator"))
    | _ => do pure (← integerEntry entry, 1)
  unless 0 < pair.2 do throw "an exact rational must have a positive denominator"
  return pair

/-- The literal of the expected data type read from a JSON entry. -/
partial def dataLiteral (entry : Json) (expected : Expr) : TermElabM Expr := do
  let type ← whnf expected
  if ← isProp type then
    throwError "JSON imports data, not proofs of {type}"
  if type.isConstOf ``Nat then
    let value ← ofExcept (integerEntry entry)
    unless 0 ≤ value do throwError "expected a nonnegative integer"
    return mkNatLit value.toNat
  if type.isConstOf ``Int then
    return mkIntLit (← ofExcept (integerEntry entry))
  if type.isConstOf ``Bool then
    return mkConst (if ← ofExcept entry.getBool? then ``Bool.true else ``Bool.false)
  if type.isConstOf ``String then
    return mkStrLit (← ofExcept entry.getStr?)
  if type.isConstOf ``Rat then
    let (numerator, denominator) ← ofExcept (rationalEntry entry)
    let numeral (value : Int) : TermElabM Expr := do
      let literal ← mkAppOptM ``OfNat.ofNat
        #[some type, some (mkNatLit value.natAbs), none]
      if value < 0 then return ← mkAppM ``Neg.neg #[literal]
      return literal
    -- Ordinary fractions work with Mathlib's normalization and CAS after casting.
    return ← mkAppM ``HDiv.hDiv #[← numeral numerator, ← numeral denominator]
  let args := type.getAppArgs
  if type.isAppOfArity ``Array 1 || type.isAppOfArity ``List 1 then
    let entries ← ofExcept entry.getArr?
    let values ← entries.mapM fun value ↦ dataLiteral value args[0]!
    let array ← arrayLiteral args[0]! values
    if type.isAppOf ``Array then return array
    return ← mkAppM ``Array.toList #[array]
  if type.isAppOfArity ``Option 1 then
    if entry == .null then return ← mkAppOptM ``Option.none #[some args[0]!]
    return ← mkAppM ``Option.some #[← dataLiteral entry args[0]!]
  if type.isAppOfArity ``Prod 2 then
    if let .arr entries := entry then
      unless entries.size == 2 do
        throwError "a JSON pair must contain exactly two entries"
      return ← mkAppM ``Prod.mk
        #[← dataLiteral entries[0]! args[0]!, ← dataLiteral entries[1]! args[1]!]
  let .const name levels := type.getAppFn
    | throwError "unsupported JSON data type {type}"
  let some info := getStructureInfo? (← getEnv) name
    | throwError "unsupported JSON data type {type}"
  let ctor := getStructureCtor (← getEnv) name
  let mut result := mkAppN (mkConst ctor.name levels) args
  for field in info.fieldNames do
    let .forallE _ fieldType _ _ ← whnf (← inferType result)
      | throwError "invalid constructor for JSON data type {type}"
    let value ← ofExcept (entry.getObjVal? field.getString!)
    let term ← dataLiteral value fieldType
    result := mkApp result term
  return result

/-- Elaborate `json_data%`: follow the dotted key, if any, to an entry of the document and read
it as a literal of the expected type. -/
@[term_elab jsonData] def elabJsonData : TermElab := fun stx expected ↦ do
  let `(json_data% $text $[$key:str]?) := stx | throwUnsupportedSyntax
  let some type := expected
    | throwError "json_data% needs an expected type or a type annotation"
  let document ← ofExcept (Json.parse (← evalString text))
  let entry ← match key with
    | some key =>
      key.getString.splitOn "." |>.foldlM
        (fun (object : Json) field ↦ Lean.ofExcept (object.getObjVal? field)) document
    | none => pure document
  dataLiteral entry type

end CAS.Numerics
