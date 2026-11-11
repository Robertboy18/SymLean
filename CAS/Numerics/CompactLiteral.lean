/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Numerics.CompactLiteralRuntime
public meta import CAS.Numerics.CompactLiteralRuntime
public meta import Lean.Elab.Eval
public meta import Lean.Compiler.ImplementedByAttr

/-!
# Large natural literals in compiled code

`mkCompactNatLiteral` stores a natural number as a named auxiliary definition holding its
literal. From `2 ^ compactLiteralBits = 2 ^ 4096` on, the definition, which the kernel reads,
gets a compiled implementation (`implemented_by`, `natCompact`) whose C output holds only the
name of the definition and a string of the digits, 60-bit fields of `19` decimal characters.
`withLiteralEnv` runs an evaluation in which compiled code reads each compact literal from its
definition in the environment, and `evalNatTerm` evaluates the closed natural-number term of
`nat_literal%` and `computed_nat%`.

## Implementation notes

Lean writes a natural literal above `2 ^ 32` into the C output of a module through `Nat.repr`,
in time quadratic in its length: a literal of `1.6` million bits takes a minute, one of `65`
million bits more than a day. So we keep large literals out of compiled code. The definition
itself is not compiled; its implementation is a second definition, `natCompact` applied to the
name and to a function that reads, with `natOfLimbs`, the string that `limbsOf` writes after
splitting the value by halving. `nat_literal%`, `nat_literal_priv%`, `computed_nat%` and the
native check of a closed certificate by `cega [fast]` evaluate inside `withLiteralEnv`, where
compiled code takes each compact literal from its definition; elsewhere it parses the digits
once per process. Both are written from the same value. The kernel reads only the definition,
since `implemented_by` changes compiled code alone, so the digits reach only compiled code that
runs outside `withLiteralEnv`, such as the row function of `computed_rows%`, and never the
kernel.

The compiler inlines a smaller literal into the code that uses it but calls the implementation
of a compact one. A module that evaluates during elaboration a term using the literals of an
imported module therefore also imports that module with `meta import`. `mkCompactNatLiteral`
stores the literals of `nat_literal%` and `nat_literal_priv%`, those of `computed_nat%` from
`2 ^ 4096` on, the tables of the packed JSON importers and of `binary64_words%` and
`binary64_word_rows%`, and the rows of [CompactRows](CompactRows.lean); `json_data%` writes
ordinary numerals.
-/


public meta section

namespace CAS.Numerics

open Lean Elab Term Meta

/-- The `count` digits of `n < 2 ^ (60 * count)` in base `2 ^ 60`, least significant first, each
as `19` decimal characters, split by halving. -/
partial def limbsOf (n count : Nat) : String :=
  if count ≤ 1 then
    let s := toString n
    String.ofList (List.replicate (19 - s.length) '0') ++ s
  else
    let low := count / 2
    limbsOf (n &&& ((1 <<< (60 * low)) - 1)) low ++ limbsOf (n >>> (60 * low)) (count - low)

/-- Run `act` with the current environment as the one in which compiled code reads compact
literals, so that an evaluation reads each literal from its definition. -/
def withLiteralEnv {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadLiftT IO m]
    [MonadFinally m] (act : m α) : m α := do
  let previous ← (compactLiteralEnv.swap (some (← getEnv)) : IO _)
  try act finally (compactLiteralEnv.set previous : IO _)

/-- Literals of at least this many bits get an implementation by digits in compiled code. -/
def compactLiteralBits : Nat := 4096

/-- A named auxiliary definition `name` with the natural literal `value`, as
`mkAuxDefinitionFor (compile := true) name (mkNatLit value)` does; from `2 ^ compactLiteralBits`
on, compiled code reads the value from a string of decimal fields instead of a literal. -/
def mkCompactNatLiteral (name : Name) (value : Nat) : TermElabM Expr := do
  if value < 2 ^ compactLiteralBits then
    return ← mkAuxDefinitionFor (compile := true) name (mkNatLit value)
  let implName := name ++ `digits
  addAndCompile <| .defnDecl {
    name := implName, levelParams := [], type := mkConst ``Nat
    value := mkApp2 (mkConst ``natCompact) (toExpr name)
      (.lam `u (mkConst ``Unit) (mkApp (mkConst ``natOfLimbs)
        (mkStrLit (limbsOf value (value.log2 / 60 + 1)))) .default)
    hints := .opaque, safety := .safe }
  let literal ← mkAuxDefinitionFor (compile := false) name (mkNatLit value)
  setImplementedBy name implName
  return literal

/-- Evaluate a natural-number term during elaboration. -/
unsafe def evalNatTermUnsafe (term : TSyntax `term) : TermElabM Nat :=
  evalTerm Nat (mkConst ``Nat) term

/-- The value of a closed natural-number term, computed during elaboration. -/
@[implemented_by evalNatTermUnsafe]
opaque evalNatTerm (term : TSyntax `term) : TermElabM Nat

end CAS.Numerics
