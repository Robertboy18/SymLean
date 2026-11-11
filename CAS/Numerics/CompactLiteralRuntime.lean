/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import Lean.Environment
import Batteries.Tactic.Lint.Misc

/-!
# Compiled code of compact literals

The runtime part of [CompactLiteral](CompactLiteral.lean): compiled code reads a compact literal
from its definition in the environment that the literal elaborators and native certificate
checks set while they evaluate (`natCompact`, `withLiteralEnv`), and otherwise from its
decimal digits (`natOfLimbs`), once per process.

## Implementation notes

The compiled implementation of a compact literal calls `natCompact` in whatever module the
literal lives, so `natCompact`, `natOfLimbs` and the two references that `natCompactImpl` reads
are ordinary code here, apart from the `meta` elaborator side in CompactLiteral; `initialize`
gives one of each reference per process. For the kernel, `natCompact key digits` is
`digits ()`. Compiled code runs `natCompactImpl` instead, which looks `key` up in
`compactLiteralEnv`, then in `compactLiteralCache`, and only then forces `digits`. Nothing
checks that these agree: `mkCompactNatLiteral` writes the definition and the digits from one
value, and the kernel reads only the definition, so a disagreement could mislead only compiled
code that runs outside `withLiteralEnv`, never the kernel.
-/

public section

namespace CAS.Numerics

/-- The natural number whose digits in base `2 ^ 60` are the fields `lo` to `hi - 1` of `s`, each
field `19` decimal characters, least significant field first. A field is read by
`Substring.Raw.toNat?` without allocating a big number, and the fields are joined by shifts. -/
partial def natOfLimbsRange (s : String) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then
    ((Substring.Raw.mk s ⟨19 * lo⟩ ⟨19 * hi⟩).toNat?).getD 0
  else
    let mid := (lo + hi) / 2
    (natOfLimbsRange s mid hi <<< (60 * (mid - lo))) ||| natOfLimbsRange s lo mid

/-- The natural number whose digits in base `2 ^ 60` are the `19`-character decimal fields of
`s`, least significant field first. -/
def natOfLimbs (s : String) : Nat :=
  natOfLimbsRange s 0 (s.utf8ByteSize / 19)

/-- The compact literals read so far in this process, by name. -/
initialize compactLiteralCache : IO.Ref (Std.HashMap Lean.Name Nat) ← IO.mkRef {}

/-- The environment of the literal elaborators and of native certificate checks while they
evaluate: compiled code reads a compact literal from its definition there (`natCompact`). -/
initialize compactLiteralEnv : IO.Ref (Option Lean.Environment) ← IO.mkRef none

/-- The value of the literal definition `key`: its body in `compactLiteralEnv` if that
environment has it, otherwise `digits ()` (read once per process, on a thread of its own so that
its allocations do not count against the heartbeats of the elaboration that asked for it). -/
unsafe def natCompactImpl (key : Lean.Name) (digits : Unit → Nat) : Nat :=
  unsafeBaseIO do
    if let some env := ← compactLiteralEnv.get then
      if let some (.defnInfo info) := env.find? key then
        if let some v := info.value.nat? <|> info.value.rawNatLit? then
          return v
    if let some v := (← compactLiteralCache.get).get? key then
      return v
    let v := (Task.spawn (prio := .dedicated) digits).get
    compactLiteralCache.modify (·.insert key v)
    return v

/-- The compiled value of the literal definition `key`, `digits ()`; see `natCompactImpl`. The
kernel unfolds this to `digits ()`; only the compiled implementation reads `key`. -/
@[implemented_by natCompactImpl, nolint unusedArguments]
def natCompact (key : Lean.Name) (digits : Unit → Nat) : Nat :=
  digits ()

end CAS.Numerics
