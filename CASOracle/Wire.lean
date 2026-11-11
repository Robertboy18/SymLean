/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS.Command.FullSimplify

/-!
# Names, numbers and statements of the oracle requests

Coordinates travel under neutral names `v0, v1, …`, never under the user's identifiers, so no
name can collide with a function or constant of an oracle's language. Numbers that are data
(constants, decimals, interval bounds) travel as text and are read here exactly, with bounds on
their size. Statements are written from checked expressions by `toTerm`, which is total over
`Verified.Expr`, so a display and the theorem cannot disagree about a function; the commands
state theorems about the oracles' proposals and prove them.
-/

namespace CASOracle.Wire

open Lean
open CAS CAS.Command CAS.Command.FullSimplify

/-- A rational number as text, `p` or `p/q`. -/
def ratText (q : ℚ) : String :=
  if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

/-- A rational from the text `p`, `-p` or `p/q`. -/
def parseRat? (text : String) : Option ℚ := do
  if text.length > 4000 then none
  match text.splitOn "/" with
  | [p] => return ((← p.trimAscii.toString.toInt?) : ℚ)
  | [p, q] =>
      let q ← q.trimAscii.toString.toNat?
      if q = 0 then none
      return ((← p.trimAscii.toString.toInt?) : ℚ) / q
  | _ => none

/-- A rational from a decimal `d.ddd`, `-d.ddde±k` or an integer, exactly as written; at most
200 characters and a decimal exponent of at most 400 in size, so that a short text cannot ask for
an enormous power. -/
def parseDecimal? (text : String) : Option ℚ := do
  let text := text.trimAscii.toString
  if text.length > 200 then none
  let (mantissa, exponent) ← match text.splitOn "e" with
    | [m] => some (m, (0 : Int))
    | [m, k] =>
        let k := if k.startsWith "+" then (k.drop 1).toString else k
        some (m, ← k.toInt?)
    | _ => none
  let negative := mantissa.startsWith "-"
  let mantissa := if negative || mantissa.startsWith "+" then (mantissa.drop 1).toString
    else mantissa
  let (whole, fraction) ← match mantissa.splitOn "." with
    | [w] => some (w, "")
    | [w, f] => some (w, f)
    | _ => none
  let digits ← (whole ++ fraction).toNat?
  if exponent.natAbs > 400 then none
  let scale : Int := exponent - fraction.length
  let magnitude : ℚ := if 0 ≤ scale then (digits * 10 ^ scale.toNat : ℚ)
    else (digits : ℚ) / (10 ^ (-scale).toNat : ℚ)
  return if negative then -magnitude else magnitude

/-- A natural number of at most nine digits, from its text (a count or an exponent of an
answer); longer texts are refused before they are read. -/
def smallNat? (text : String) : Option Nat :=
  if text.length ≤ 9 && text.all Char.isDigit then text.toNat? else none

/-- The checked expression of a rational. -/
def ratExprIn {ι : Type} (q : ℚ) : Verified.Expr ι :=
  if q.den = 1 then (if 0 ≤ q.num then .nat q.num.toNat else .neg (.nat q.num.natAbs))
  else if 0 ≤ q.num then .rat q.num q.den else .neg (.rat (-q.num) q.den)

/-- The bounds on an oracle's answer, checked where the answer enters SymLean
(`CASOracle.Translate.read`, and `Translate.admit` for what a command assembles or derives from
it). They limit the answer and heuristic estimates of what simplification, polynomial
conversion and interval evaluation can make of it; they are estimates, not a proof that every
pass stays within them. SymLean's passes take as long on any large input, a user's own `#cas`
input included. -/
structure Limits where
  /-- Longest answer text, in characters. -/
  text : Nat := 20000
  /-- Deepest nesting of brackets in the text. -/
  depth : Nat := 512
  /-- Longest number text. -/
  digits : Nat := 2000
  /-- Largest number of nodes, of the answer and of its reflection. -/
  nodes : Nat := 20000
  /-- Largest exponent of a power, and largest degree. -/
  exponent : Nat := 1000
  /-- Largest number of bits of the numbers computed from the answer, all together, with the
  powers around them written out. -/
  bits : Nat := 100000
  /-- Largest number of terms of an expansion of the answer. -/
  terms : Nat := 10000
  /-- Largest number of steps (one per term inserted into a collected polynomial) that an
  expansion of the answer may take. -/
  work : Nat := 2000000

/-- The wire name `v i` of coordinate `i`. -/
def wireName {n : Nat} (i : Fin n) : String := s!"v{i.val}"

/-- The wire names of `n` coordinates. -/
def wireNames (n : Nat) : List String := (List.finRange n).map wireName

/-- Real term syntax of a checked expression, with coordinate `i` written as `var i`. It is
total over the closed expression type, so no answer can display one function and state
another. When `natVar i = some k`, coordinate `i` is a natural number written `k`, and a real
power whose exponent is built from such coordinates and natural literals by `+` and `*`
(`a ^ (n + 1)`) is written as a natural power (for sums over `ℕ`). -/
partial def toTerm {n : Nat} (var : Fin n → Term) (expression : Verified.Expr (Fin n))
    (natVar : Fin n → Option Term := fun _ ↦ none) : MacroM Term :=
  let rec' (sub : Verified.Expr (Fin n)) : MacroM Term := toTerm var sub natVar
  -- An exponent built from natural coordinates and literals by `+` and `*`, as a term of `ℕ`.
  let rec natExponent : Verified.Expr (Fin n) → MacroM (Option Term)
    | .nat k => return some ⟨Syntax.mkNumLit (toString k)⟩
    | .var i => return natVar i
    | .add a b => do
        let some a ← natExponent a | return none
        let some b ← natExponent b | return none
        return some (← `($a + $b))
    | .mul a b => do
        let some a ← natExponent a | return none
        let some b ← natExponent b | return none
        return some (← `($a * $b))
    | _ => return none
  match expression with
  | .nat k => do
      let k : Term := ⟨Syntax.mkNumLit (toString k)⟩
      `(($k : ℝ))
  | .int z => do
      let k : Term := ⟨Syntax.mkNumLit (toString z.natAbs)⟩
      if z < 0 then `((-($k : ℝ))) else `(($k : ℝ))
  | .rat p q => do
      let a : Term := ⟨Syntax.mkNumLit (toString p.natAbs)⟩
      let b : Term := ⟨Syntax.mkNumLit (toString q)⟩
      if p < 0 then `((-(($a : ℝ) / $b))) else `((($a : ℝ) / $b))
  | .pi => `(Real.pi)
  | .e => `(Real.exp 1)
  | .var i => pure (var i)
  | .add a b => do `($(← rec' a) + $(← rec' b))
  | .mul a b => do `($(← rec' a) * $(← rec' b))
  | .sub a b => do `($(← rec' a) - $(← rec' b))
  | .div a b => do `($(← rec' a) / $(← rec' b))
  | .neg a => do `(-$(← rec' a))
  | .pow a k => do
      let k : Term := ⟨Syntax.mkNumLit (toString k)⟩
      `($(← rec' a) ^ ($k : ℕ))
  | .rpow a b => do
      if let some k ← natExponent b then
        return ← `($(← rec' a) ^ ($k : ℕ))
      `($(← rec' a) ^ ($(← rec' b) : ℝ))
  | .sin a => do `(Real.sin $(← rec' a))
  | .cos a => do `(Real.cos $(← rec' a))
  | .atan a => do `(Real.arctan $(← rec' a))
  | .asin a => do `(Real.arcsin $(← rec' a))
  | .acos a => do `(Real.arccos $(← rec' a))
  | .exp a => do `(Real.exp $(← rec' a))
  | .log a => do `(Real.log $(← rec' a))
  | .sqrt a => do `(Real.sqrt $(← rec' a))

/-- A rational as the term `(p / q)`, elaborated in whatever ring the context gives. -/
def ratTerm (q : ℚ) : MacroM Term := do
  let numerator : Term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let magnitude ← if q.den = 1 then pure numerator else
    let denominator : Term := ⟨Syntax.mkNumLit (toString q.den)⟩
    `(($numerator / $denominator))
  if q.num < 0 then `((-$magnitude)) else pure magnitude

end CASOracle.Wire
