/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.RadicalGenerator
public import CAS.Polynomial.RealRoot.SturmAtlas

/-!
# Checked real-root isolation certificates

A `PolynomialIsolationCertificate` for an original polynomial is a square-free radical with the
same real zero set (`RadicalCertificate`) and a Sturm subdivision of a rational interval for that
radical (`SturmSubdivisionCertificate`). `PolynomialIsolationCertificate.valid` runs the radical
and subdivision checkers, and `PolynomialIsolationCertificate.toRootAtlas` turns an accepted
certificate into ordinary real existence, uniqueness and nonvanishing theorems for the original
polynomial, including repeated-root inputs.

SymLean checks such certificates when a caller supplies them; it has no generator for them. The
root and sign commands (`#cas [roots]`, `#cas [reduce]`, bare `cas`) use their own root-list
search (`RootIsolation.generate`) and the root-list checkers of `RootList` and `SignReduce`
instead.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum

/--
Checked preprocessing and subdivision data for one original polynomial.

The subdivision certifies the square-free radical.  `valid` additionally checks
that the radical has exactly the same real zero set as `original`.
-/
structure PolynomialIsolationCertificate where
  /-- Checked square-free surrogate with the same real zero set as the original polynomial. -/
  radical : RadicalCertificate
  /-- Checked Sturm subdivision that classifies the radical's roots on the search interval. -/
  subdivision : SturmSubdivisionCertificate
deriving DecidableEq

namespace PolynomialIsolationCertificate

/-- Independent checker for the radical and its Sturm subdivision. -/
def valid (original : Sparse.Univariate)
    (certificate : PolynomialIsolationCertificate) : Bool :=
  certificate.radical.valid original &&
    certificate.subdivision.valid certificate.radical.radical

/--
Convert accepted isolation data to the canonical root-atlas interface for the
original polynomial.
-/
noncomputable def toRootAtlas
    {original : Sparse.Univariate}
    (certificate : PolynomialIsolationCertificate)
    (hvalid : certificate.valid original = true) :
    RootAtlas
      (SturmSubdivisionCertificate.LeafIndex certificate.subdivision)
      original
      (Icc (certificate.subdivision.subdivision.interval.lo : ℝ)
        (certificate.subdivision.subdivision.interval.hi : ℝ)) := by
  simp only [valid, Bool.and_eq_true] at hvalid
  exact
    (certificate.subdivision.toRootAtlas hvalid.2).transportAlongRadical
      certificate.radical hvalid.1

end PolynomialIsolationCertificate

end CAS.Polynomial.RealRoot
