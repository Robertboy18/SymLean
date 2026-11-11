/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.Radical
public import CAS.Polynomial.Sparse.Euclidean

/-!
# Automatic generation of certified square-free radicals

`RadicalCertificate.generate?` proposes a `RadicalCertificate` for a sparse rational polynomial
and returns it only when the independent checker `RadicalCertificate.valid` confirms:

* divisibility of the original polynomial by the radical;
* divisibility of a positive radical power by the original polynomial; and
* a Bézout identity between the radical and its derivative.

Consequently no correctness property of the executable factorization or gcd
implementation is used in the proofs.

## Implementation notes

`candidate?` takes the square-free decomposition `Sparse.Univariate.squareFreeFactors?`, an
iteration of gcds and exact quotients over `ℚ` described in `CAS/Polynomial/Sparse/Euclidean.lean`.
The product of its factors without their multiplicities (`factorProduct`) is the proposed radical,
and the largest multiplicity (`maximumMultiplicity`) is the exponent. The two cofactors are exact
quotients (`Sparse.Univariate.exactQuotient?`), and the extended Euclidean algorithm gives the
Bézout coefficients of the radical and its derivative
(`Sparse.Univariate.bezoutCoefficientsCandidate?`).

The root certificates of `#cas [roots]`, `#cas [reduce]` and bare `cas` carry a radical of their
quotient when the quotient is not square-free (`RootListCertificate.radical` in `RootList.lean`).
Their search runs `generate?` in compiled code and quotes the radical it returns; the kernel
checks only `valid` of the quoted radical. `#cas [roots z in ℂ]` also takes its radical from
`generate?`. The generator is in the core library for these certificates, although Hex computes
square-free parts too (`Hex.ZPoly.squareFreeCore`).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Sparse

namespace RadicalCertificate

/--
Product of the `factor` fields of `factors`, ignoring multiplicities, starting from the
constant polynomial `1`. This is the proposed square-free radical before normalization.
-/
def factorProduct
    (factors : List Sparse.Univariate.SquareFreeFactor) :
    Sparse.Univariate :=
  factors.foldl
    (fun product factor ↦
      Verified.Expr.Alg.mvMulPoly product factor.factor)
    (Sparse.monomial 1 0)

/--
Largest `multiplicity` among the given square-free factors, or `1` for the empty list. The
radical raised to this power is divisible by the original polynomial when the factorization
is correct.
-/
def maximumMultiplicity :
    List Sparse.Univariate.SquareFreeFactor → ℕ+
  | [] => ⟨1, by omega⟩
  | factor :: factors =>
      let tail := maximumMultiplicity factors
      ⟨max (tail : Nat) (factor.multiplicity : Nat),
        tail.property.trans_le (le_max_left _ _)⟩

/--
Compute candidate evidence for the square-free radical of `original`.

The factors and multiplicities returned by `Sparse.Univariate.squareFreeFactors?` are not
trusted here. They are used only to choose the radical and exponent; exact quotients and the
final certificate checker recover all theorem-facing identities independently.
-/
def candidate? (original : Sparse.Univariate) :
    Option RadicalCertificate := do
  let factors ← Sparse.Univariate.squareFreeFactors? original
  let radical :=
    Verified.Expr.Alg.mvNormalize (factorProduct factors)
  let exponent := maximumMultiplicity factors
  let originalOverRadical ←
    Sparse.Univariate.exactQuotient? original radical
  let radicalPowerOverOriginal ←
    Sparse.Univariate.exactQuotient?
      (Verified.Expr.Alg.mvPowPoly radical (exponent : Nat)) original
  let bezout ←
    Sparse.Univariate.bezoutCoefficientsCandidate? radical
      (Sparse.derivative (0 : Fin 1) radical)
  some
    { radical := radical
      originalOverRadical := originalOverRadical
      exponent := exponent
      radicalPowerOverOriginal := radicalPowerOverOriginal
      bezoutLeft := bezout.1
      bezoutRight := bezout.2 }

/--
Generate and independently validate a checked radical certificate.
-/
def generate? (original : Sparse.Univariate) :
    Option
      { certificate : RadicalCertificate //
        certificate.valid original = true } :=
  match candidate? original with
  | none => none
  | some certificate =>
      if hvalid : certificate.valid original = true then
        some ⟨certificate, hvalid⟩
      else
        none

end RadicalCertificate

end CAS.Polynomial.RealRoot
