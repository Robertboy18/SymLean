/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Syntax
public meta import CAS.Command.Syntax

/-!
# Square-root notation in numerical queries

`parseExpression` reads the expression of an explicit CEGA query. It rewrites every
occurrence of the square-root notation `√a`, nested ones included, to `Real.sqrt a` and then
calls the exact `#cas` parser: `Command.parseExact` with the declared coordinates, or
`Command.parseInferred` for a closed query, which must mention no coordinate. The result
keeps the original text for reports.

## Implementation notes

We rewrite before parsing because the exact parser of `CAS.Command.Syntax` reads `sqrt` and
`Real.sqrt` but not the prefix notation `√`. The parse is not trusted: the theorem a query
proves is about the parsed expression, and `cega` closes a goal only when that theorem matches
the goal or transports to it.
-/

public meta section

namespace CAS.CEGA

open Lean

/-- Normalize square-root notation before invoking the shared exact expression parser.
The original surface text is retained for numerical reports. -/
def parseExpression {m : Type → Type} [Monad m] [MonadQuotation m]
    [MonadExceptOf Exception m] [AddErrorMessageContext m]
    (expression : Syntax) (coordinates : List Name) : m Command.ReifiedExpr := do
  let normalized ← expression.rewriteBottomUpM fun stx ↦ do
    match stx with
    | `(√$argument:term) => return (← `($(mkIdent ``Real.sqrt) $argument)).raw
    | _ => return stx
  let reified ←
    if coordinates.isEmpty then
      let result ← Command.parseInferred normalized
      unless result.names.isEmpty do
        throwErrorAt expression "a closed numerical query contains undeclared coordinates: \
          {result.names}"
      pure result
    else
      Command.parseExact normalized coordinates
  return { reified with surface.text? := some (Command.surfaceText expression) }

end CAS.CEGA
