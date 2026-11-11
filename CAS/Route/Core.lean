/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Route.Step

/-!
# Certificate routes

`CertificateRoute Cert` pairs a certificate of type `Cert` with the list of `RouteStep`s
the planner used to build it. The certificate may be a proof, an analytic certificate, or a
certified evaluator context; its type alone determines what the route proves, and the steps
are diagnostic data. The `cega` tactic accepts a route to an enclosure, bound or residual
certificate as a carrier (`CAS.Tactic.CEGA`).
-/

@[expose] public section

namespace CAS

universe u v

/--
A certificate paired with the planner steps that produced it.

Route types specialize this by certificate type, and the certificate type alone
decides whether the route carries a proof, an analytic certificate, or a
certified evaluator context.
-/
structure CertificateRoute (Cert : Sort u) where
  /-- The checked certificate carried by the route. -/
  cert : Cert
  /-- Diagnostic planner steps used to construct the certificate. -/
  steps : List RouteStep := []

namespace CertificateRoute

variable {Cert : Sort u} {Cert' : Sort v}

/-- Replace a route's certificate while preserving its planner steps. -/
def map (route : CertificateRoute Cert) (f : Cert → Cert') :
    CertificateRoute Cert' where
  cert := f route.cert
  steps := route.steps

end CertificateRoute

end CAS
