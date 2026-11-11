/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Elab.Tactic.Basic
public import Lean.Expr
import Lean.Elab.Tactic.Basic

/-!
# Optional Euclidean derivative backend

The exact frontend (`CAS/ExactTactic.lean`) and the derivative rewriting of bare `cas`
(`CAS/Tactic/DerivativeRewrite.lean`) dispatch through this environment-scoped
registry. A package that defines Euclidean derivative operators registers its analytic bridges
here explicitly: it defines a `CAS.Tactic.DerivativeRegistry.Backend`, which answers each
`Request` with a `Response`, and tags that definition `@[cas_derivative_backend]`. Importing the
package then enables its derivative operators in `cas`; without such an import they are refused.
Registration can precede or follow the exact frontend in the import graph.

## Implementation notes

Only declaration names are persisted. The attribute compiles a wrapper
`<backend>.casDerivativeTactic` around the backend (`backendTactic`) and registers it as an
elaborator of the internal tactic `cas_derivative_dispatch`. A request runs that tactic, so
Lean's tactic dispatcher calls the compiled backend although the core of `cas` does not import
the package; the request and the response travel in an environment extension, whose previous
state is restored afterwards. The backend's answers are dispatch metadata or proof terms, and
the caller still checks the completed proof of the original goal. Multiple distinct backends
are rejected independently of import order.
-/

public meta section

namespace CAS.Tactic.DerivativeRegistry

open Lean Elab Tactic

/-- Operations supplied by a derivative backend registered with `@[cas_derivative_backend]`. -/
inductive Request where
  /-- Recognize a complete derivative goal. -/
  | isGoal (target : Expr)
  /-- Recognize a derivative subterm of an ordinary identity. -/
  | isTerm (term : Expr)
  /-- Close a derivative goal stated with the backend's operators. -/
  | close (evidence? : Option (TSyntax `term))
  /-- Produce the checked equation rewriting a derivative subterm. -/
  | equation (term : Expr) (evidence? : Option (TSyntax `term))
  /-- Close a derivative identity already written with the checked evaluator. -/
  | reflected (evidence? : Option (TSyntax `term))

/-- A recognition result, derivative equation, or completed tactic invocation. -/
inductive Response where
  /-- Whether the backend recognizes the requested expression. -/
  | matches (value : Bool)
  /-- Proof of a derivative subterm's equality to its computed value. -/
  | equation (proof : Expr)
  /-- The backend closed the main goal. -/
  | closed

/-- A backend supplies recognition, proof production, and reflected differentiation of its
operators. -/
abbrev Backend := Request → TacticM Response

private initialize registry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `CAS.Tactic.DerivativeRegistry.registry
    addImportedFn := fun states ↦
      states.foldl (fun names state ↦
        state.foldl (fun names name ↦
          if names.contains name then names else names.push name) names) #[]
    addEntryFn := fun names name ↦ if names.contains name then names else names.push name
  }

private initialize dispatchState : EnvExtension (Option Request × Option Response) ←
  registerEnvExtension (pure (none, none)) (asyncMode := .local)

/-- Internal syntax used by the environment-scoped backend dispatcher. -/
syntax (name := derivativeBackendTactic) "cas_derivative_dispatch " ident : tactic

/-- Adapt a compiled backend to Lean's tactic dispatcher. -/
def backendTactic (wrapper : Name) (backend : Backend) : Tactic := fun stx ↦ do
  let `(tactic| cas_derivative_dispatch $source:ident) := stx
    | throwUnsupportedSyntax
  unless source.getId == wrapper do throwUnsupportedSyntax
  let some request := (dispatchState.getState (← getEnv)).1
    | throwError "CAS derivative dispatch has no request"
  let response ← backend request
  modifyEnv fun env ↦ dispatchState.setState env (some request, some response)

private def dispatch (request : Request) : TacticM (Option Response) := do
  let names := registry.getState (← getEnv)
  if names.isEmpty then return none
  unless names.size == 1 do
    throwError "multiple CAS derivative backends are imported: {names}"
  let source := names[0]!
  let decl ← getConstInfo source
  unless decl.type.isConstOf ``Backend do
    throwError "CAS derivative backend '{source}' must have type `DerivativeRegistry.Backend`"
  let previous := dispatchState.getState (← getEnv)
  modifyEnv fun env ↦ dispatchState.setState env (some request, none)
  try
    evalTactic (← `(tactic| cas_derivative_dispatch $(mkIdent (source ++ `casDerivativeTactic))))
    let some response := (dispatchState.getState (← getEnv)).2
      | throwError "CAS derivative backend '{source}' returned no response"
    return some response
  finally
    modifyEnv fun env ↦ dispatchState.setState env previous

private def recognizes (request : Request) : TacticM Bool := do
  match ← dispatch request with
  | none => return false
  | some (.matches value) => return value
  | _ => throwError "CAS derivative backend returned an invalid recognition response"

/-- Recognize a derivative goal of the registered backend. -/
def isGoal (target : Expr) : TacticM Bool :=
  recognizes (.isGoal target)

/-- Recognize a derivative subterm of the registered backend. -/
def isTerm (term : Expr) : TacticM Bool :=
  recognizes (.isTerm term)

private def requireResponse (request : Request) : TacticM Response := do
  let some response ← dispatch request
    | throwError "no derivative backend is registered with `@[cas_derivative_backend]`; import \
        a library that provides one (the module doc of CAS.Tactic.DerivativeRegistry explains how)"
  return response

/-- Close a derivative goal of the registered backend; the caller checks the proof and restores
failures. -/
def close (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let .closed ← requireResponse (.close evidence?)
    | throwError "CAS derivative backend did not return a completed invocation"

/-- Produce the equation for a derivative subterm of the registered backend in an ordinary
identity. -/
def equation (term : Expr) (evidence? : Option (TSyntax `term)) : TacticM Expr := do
  let .equation proof ← requireResponse (.equation term evidence?)
    | throwError "CAS derivative backend did not return an equation"
  return proof

/-- Close a reflected derivative identity of the registered backend. -/
def reflected (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let .closed ← requireResponse (.reflected evidence?)
    | throwError "CAS derivative backend did not return a completed invocation"

/-- Register a derivative backend, a declaration of type `DerivativeRegistry.Backend`. -/
syntax (name := casDerivativeBackendAttr) "cas_derivative_backend" : attr

initialize registerBuiltinAttribute {
  name := `casDerivativeBackendAttr
  descr := "register the optional checked derivative backend"
  applicationTime := .afterCompilation
  add := fun source _stx kind ↦ do
    unless kind == .global do throwAttrMustBeGlobal `cas_derivative_backend kind
    unless (registry.getState (← getEnv)).isEmpty do
      throwError "a CAS derivative backend is already registered"
    let decl ← getConstInfo source
    unless decl.type.isConstOf ``Backend do
      throwError "CAS derivative backend '{source}' must have type `DerivativeRegistry.Backend`"
    let wrapper := source ++ `casDerivativeTactic
    addAndCompile (markMeta := true) <| .defnDecl {
      name := wrapper
      levelParams := []
      type := mkConst ``Tactic
      value := mkApp2 (mkConst ``backendTactic) (toExpr wrapper) (mkConst source)
      hints := .regular 0
      safety := .safe
    }
    addDocStringCore wrapper s!"Internal tactic adapter for the derivative backend `{source}`."
    Attribute.add wrapper `tactic
      (← `(attr| tactic $(mkIdent ``derivativeBackendTactic)))
    modifyEnv fun env ↦ registry.addEntry env source
}

end CAS.Tactic.DerivativeRegistry
