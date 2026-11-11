/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.SymbolicApprox
public import CAS.Tactic.CEGA.Registry

/-!
# Built-in CEGA carrier registrations

Registers the built-in checked carrier types with the extensible `cega` registry:
symbolic approximation attempts (`CertifiedEvalRegistry.SymbolicApproxAttempt`), interval
enclosure attempts (`EnclosureAttempt`, projected to an enclosure, an upper bound, an absolute
bound, or a midpoint approximation), zero-residual attempts (`ZeroResidualAttempt`), and
residual-bound attempts (`ResidualBoundAttempt`). Each registration names the certificate
projection and, for the symbolic and enclosure attempts, the soundness theorems that `cega` tries
before projecting. The registrations live apart from the carrier definitions so that the
certificate layer does not import tactic code.
-/

@[expose] public section

open CAS
open CAS.Certificate
open CAS.Continuum.RationalInterval

attribute [cega_carrier symbolicAttempt CertifiedEvalRegistry.SymbolicApproxAttempt.toApproxCert
  [CertifiedEvalRegistry.SymbolicApproxAttempt.sound]]
  CertifiedEvalRegistry.SymbolicApproxAttempt

attribute [cega_carrier enclosureAttempt EnclosureAttempt.cert
  [
    EnclosureAttempt.boundOn,
    EnclosureAttempt.boundOn_abs,
    EnclosureAttempt.approxOn_center]]
  EnclosureAttempt

attribute [cega_carrier zeroResidualAttempt ZeroResidualAttempt.toResidualCert]
  ZeroResidualAttempt

attribute [cega_carrier residualAttempt ResidualBoundAttempt.cert]
  ResidualBoundAttempt
