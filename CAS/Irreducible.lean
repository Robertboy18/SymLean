/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

import all Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Compatibility: Mathlib definitions that stay irreducible

This module is not part of `import CAS`, and SymLean does not need it. Import it only into a
file outside the module system whose own proofs relied on the definitions below being
irreducible.

Mathlib v4.35.0 declared the operations of `ℝ`, `Complex.exp`, the Bochner integral, `fderiv`,
`nhds`, `tprod` and some sixty other definitions with `irreducible_def`. Mathlib v4.36.0 hides
their bodies with `@[no_expose]` instead (mathlib4 pull request #45063). A `module` cannot unfold
them either way, since it never sees the bodies. A file outside the module system loads every
body, so there these definitions unfold like any other: `whnf` of `x * y : ℝ` reaches the Cauchy
sequences, and a definitional-equality check between two different real terms, which used to stop
at the first `Real.mul`, unfolds integrals and exponentials before it fails. A proof written for
Mathlib v4.35.0 that tries `rfl`, `exact` or `apply` on speculation can then run out of
heartbeats in such a file.

This module marks these definitions `@[irreducible]` again, in every file that imports it,
directly or through other imports: the ten private operations of `Mathlib.Basic.Real.Basic` and
the 63 public definitions that were irreducible in Mathlib v4.35.0, are not in v4.36.0, and still
exist. That changes elaboration in all those files, also in proofs that have nothing to do with
SymLean, which is why no module of SymLean imports it. The tactics and commands of SymLean bound
their own comparisons instead (`CAS.Elaboration.DefEq`) and behave the same with and without this
module. The list is fixed to Mathlib v4.36.0 and names private declarations of Mathlib, so it has
to be revised with every Mathlib version. The imports here are private: a `module` that imports
this one loads none of them.

Reducibility only guides elaboration. The kernel ignores it, so no proof depends on this module.
-/

set_option allowUnsafeReducibility true in
attribute [irreducible] Real.zero Real.one Real.add Real.neg Real.mul Real.inv' Real.lt Real.le
  Real.sup Real.inf

set_option allowUnsafeReducibility true in
attribute [irreducible]
  AlternatingMap.measure Asymptotics.IsBigO Asymptotics.IsBigOWith Asymptotics.IsLittleO Complex.exp
  ContinuousLinearMap.nonlinearRightInverseOfSurjective
  DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
  DirectSum.IsInternal.subordinateOrthonormalBasis
  DirectSum.IsInternal.subordinateOrthonormalBasisIndex FractionalIdeal.canonicalEquiv
  FractionalIdeal.mul FreeAlgebra.lift FreeAlgebra.ι IsFractionRing.inv IsSepClosed.lift
  IsUnifLocDoublingMeasure.vitaliFamily LinearMap.IsSymmetric.eigenvalues
  LinearMap.IsSymmetric.eigenvectorBasis LinearMap.det LinearMap.detAux MeasureTheory.AnalyticSet
  MeasureTheory.L1.integral MeasureTheory.Measure.finiteSpanningSetsInOpen'
  MeasureTheory.Measure.map MeasureTheory.Measure.pi MeasureTheory.Measure.prod
  MeasureTheory.Measure.rnDeriv MeasureTheory.Measure.singularPart MeasureTheory.integral
  MeasureTheory.lintegral MeasureTheory.toMeasurable Metric.hausdorffEDist Module.Basis.addHaar
  Module.rank NormedSpace.exp Orientation.volumeForm PiNat.firstDiff Polynomial.eval₂ RatFunc.add
  RatFunc.div RatFunc.inv RatFunc.liftOn RatFunc.liftOn' RatFunc.mk RatFunc.mul RatFunc.neg
  RatFunc.one RatFunc.smul RatFunc.sub RatFunc.zero Span.repr StieltjesFunction.measure cfc cfcₙ
  fderiv fderivWithin finprod finsum lipschitzExtensionConstant nhds stdOrthonormalBasis
  tangentConeAt tprod
