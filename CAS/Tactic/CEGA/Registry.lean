/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Attributes
public import Lean.Exception

/-!
# Internal CEGA carrier dispatch

The persistent registry that `cega` uses to recognize checked carrier types.
It is meant for extending the tactic; theorem authors import
`CAS.CEGA` and never construct registry entries.

The built-in carriers are registered in
`CAS.Tactic.CEGA.Registrations`. Downstream modules may register an
additional carrier without modifying the tactic's dispatcher.

## Main definitions

* `cegaCarrierAttr`: the attribute `cega_carrier route projection [theorems]` on a carrier type.
* `CarrierDescriptor`: what a registration records, the diagnostic route, the soundness theorems
  and the certificate projection.
* `registeredCarrier?`: the registration of a type constructor, if there is one.
* `SelectedRoute`: the diagnostic tag of the route that closed a goal.

## Implementation notes

A registration records only dispatch metadata: the tactic still constructs
the indicated projection and validates the resulting proof against the
original goal before assigning it (`CAS/Tactic/CEGA.lean`). We keep the registrations in a
persistent environment extension, keyed by the name of the carrier type. The attribute is
global only, resolves the projection and the theorems to constants when it is applied, rejects
a route name that is not a `SelectedRoute` constructor, and refuses a second registration of
the same type. The entries of the imported modules are merged into one `NameMap` under a
`Thunk`, so the merge runs at the first lookup rather than at import.
-/

public meta section

namespace CAS.Tactic.CEGA

open Lean Elab

/--
Diagnostic classification of the CEGA route selected for a semantic target.

This tag is reporting metadata only. The accepted certificate projection is
validated independently before the route is returned.
-/
inductive SelectedRoute where
  /-- A checked certificate directly matched the goal. -/
  | certificate
  /-- A symbolic approximation attempt supplied the checked certificate. -/
  | symbolicAttempt
  /-- A checked approximation route matched the goal. -/
  | approximationRoute
  /-- An interval enclosure attempt supplied the checked certificate. -/
  | enclosureAttempt
  /-- An exact residual attempt supplied the checked certificate. -/
  | zeroResidualAttempt
  /-- A bounded residual attempt supplied the checked certificate. -/
  | residualAttempt
  /-- A generic route carrying an enclosure certificate matched the goal. -/
  | enclosureRoute
  /-- A generic route carrying an upper-bound certificate matched the goal. -/
  | boundRoute
  /-- A generic route carrying a residual certificate matched the goal. -/
  | residualRoute
deriving DecidableEq, Repr

namespace SelectedRoute

/-- Stable diagnostic label for a checked CEGA route. -/
def label : SelectedRoute → String
  | .certificate => "checked certificate"
  | .symbolicAttempt => "symbolic approximation attempt"
  | .approximationRoute => "approximation route"
  | .enclosureAttempt => "interval enclosure attempt"
  | .zeroResidualAttempt => "exact residual attempt"
  | .residualAttempt => "bounded residual attempt"
  | .enclosureRoute => "enclosure route"
  | .boundRoute => "bound route"
  | .residualRoute => "residual route"

private def ofName? : Name → Option SelectedRoute
  | `certificate => some .certificate
  | `symbolicAttempt => some .symbolicAttempt
  | `approximationRoute => some .approximationRoute
  | `enclosureAttempt => some .enclosureAttempt
  | `zeroResidualAttempt => some .zeroResidualAttempt
  | `residualAttempt => some .residualAttempt
  | `enclosureRoute => some .enclosureRoute
  | `boundRoute => some .boundRoute
  | `residualRoute => some .residualRoute
  | _ => none

end SelectedRoute

/-- Dispatch metadata stored for one registered CEGA carrier type. -/
structure CarrierDescriptor where
  /-- Diagnostic route returned after a successful projection. -/
  route : SelectedRoute
  /-- Direct soundness theorems tried before the generic certificate projection. -/
  soundTheorems : Array Name
  /-- Projection recovering the checked certificate stored by the carrier. -/
  certificateProjection : Name
deriving Repr

private initialize carrierRegistry :
    SimplePersistentEnvExtension
      (Name × CarrierDescriptor) (Thunk (NameMap CarrierDescriptor)) ←
  registerSimplePersistentEnvExtension {
    name := `CAS.Tactic.CEGA.carrierRegistry
    addImportedFn := fun states ↦
      .mk fun _ ↦
        states.foldl
          (fun entries state ↦
            state.foldl
              (fun entries entry ↦ entries.insert entry.1 entry.2)
              entries)
          {}
    addEntryFn := fun entries entry ↦
      entries.map fun current ↦ current.insert entry.1 entry.2
  }

/-- Look up the registered CEGA dispatch data for a carrier type constructor. -/
def registeredCarrier? (env : Environment) (typeName : Name) :
    Option CarrierDescriptor :=
  (carrierRegistry.getState env).get.find? typeName

private def resolveDeclaration (ref : Syntax) : AttrM Name :=
  withRef ref <| resolveGlobalConstNoOverload ref

private def addCarrier
    (source : Name) (routeSyntax projectionSyntax : Syntax)
    (soundTheorems : Array Syntax) (kind : AttributeKind) : AttrM Unit := do
  unless kind == .global do
    throwAttrMustBeGlobal `cega_carrier kind
  let some route := SelectedRoute.ofName? routeSyntax.getId
    | throwErrorAt routeSyntax
        "unknown CEGA route '{routeSyntax.getId}'; use a SelectedRoute constructor name"
  let env ← getEnv
  if (registeredCarrier? env source).isSome then
    throwError "CEGA carrier '{source}' is already registered"
  let projectionName ← resolveDeclaration projectionSyntax
  let soundNames ← soundTheorems.mapM resolveDeclaration
  let descriptor := {
    route
    soundTheorems := soundNames
    certificateProjection := projectionName
  }
  setEnv <| carrierRegistry.addEntry env (source, descriptor)

/--
Register a checked carrier projection for the `cega` tactic.

An optional trailing list names direct soundness theorems to try before
projecting the carrier's generic checked certificate. The positional syntax
avoids reserving ordinary identifiers such as `certificate` or `sound`.
-/
syntax (name := cegaCarrierAttr)
  "cega_carrier" ident ident ("[" ident,* "]")? : attr

initialize registerBuiltinAttribute {
  name := `cegaCarrierAttr
  descr := "register a checked carrier type for projection by the `cega` tactic"
  add := fun source stx kind ↦
    match stx with
    | `(attr| cega_carrier $route:ident $certificateProjection:ident
        [$soundTheorems:ident,*]) =>
        addCarrier source route certificateProjection soundTheorems.getElems kind
    | `(attr| cega_carrier $route:ident $certificateProjection:ident) =>
        addCarrier source route certificateProjection #[] kind
    | _ =>
        throwUnsupportedSyntax
}

end CAS.Tactic.CEGA
