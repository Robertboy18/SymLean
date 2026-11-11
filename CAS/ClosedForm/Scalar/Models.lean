/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Scalar.Conditions

/-!
# Standard scalar PDE models

The heat, Poisson, Laplace, Helmholtz, and wave equations as `DiffExpr.Equation`s in the single
unknown `Scalar.u`, with residual shortcuts such as `poissonResidual` and `heat1DResidual` that
lower an equation for a candidate. The heat, wave, and Helmholtz equations take their spatial
coordinates from the caller, as a list (`heatSpatial`, `waveSpatial`, `helmholtzSpatial`, through
`spatialLaplacian`) or as one coordinate (`heat1D`, `wave1D`, `helmholtz1D`). For the heat and
wave equations the caller leaves the time coordinate out: no definition checks that the spatial
coordinates differ from it, and `spatialLaplacian` counts a repeated coordinate with its
multiplicity. `poisson` and `laplace` use `DiffExpr.Lap`, the Laplacian in all `n` coordinates.
The sign conventions are `u_t - Δu = f`, `-Δu = f`, `Δu = 0`, `Δu + k u = f`, and
`u_tt - Δu = f`.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Scalar

/-- Symbolic spatial Laplacian over an explicit finite list of spatial coordinates.

For heat equations the caller names the time coordinate
separately and supplies exactly the coordinates that should appear in `Δ_space`. -/
def spatialLaplacian {n : Nat} (spatial : List (Verified.Expr.SymVar n))
    (expr : DiffExpr n Unknown) : DiffExpr n Unknown :=
  spatial.foldr (fun v acc ↦ DiffExpr.D2 v expr + acc) 0

/-- With no selected spatial coordinates, the formal spatial Laplacian is zero. -/
@[simp] theorem spatialLaplacian_nil {n : Nat} (expr : DiffExpr n Unknown) :
    spatialLaplacian [] expr = 0 := rfl

/-- Prepending a spatial coordinate adds its second derivative. Repeated coordinates
are counted with their multiplicity in the list. -/
@[simp] theorem spatialLaplacian_cons {n : Nat} (v : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (expr : DiffExpr n Unknown) :
    spatialLaplacian (v :: spatial) expr =
      DiffExpr.D2 v expr + spatialLaplacian spatial expr := rfl

/-- Scalar heat equation `u_t - Δ_space u = rhs` with an explicit spatial-coordinate list. -/
def heatSpatial {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (rhs : Verified.Expr (Fin n)) :
    DiffExpr.Equation n Unknown where
  lhs := DiffExpr.D t u - spatialLaplacian spatial u
  rhs := rhs

/-- Compiled symbolic residual for `u_t - Δ_space u = rhs`. -/
def heatSpatialResidual {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (rhs candidate : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  residual (heatSpatial t spatial rhs) candidate

/-- The spatial heat residual uses the generic equation compiler, with sign convention
`u_t - Δ_space u - rhs`. -/
@[simp] theorem heatSpatialResidual_eq_residual {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (rhs candidate : Verified.Expr (Fin n)) :
    heatSpatialResidual t spatial rhs candidate =
      residual (heatSpatial t spatial rhs) candidate := rfl

/-- Scalar Poisson equation `-Δu = rhs`. -/
def poisson {n : Nat} (rhs : Verified.Expr (Fin n)) : DiffExpr.Equation n Unknown :=
  { lhs := -(DiffExpr.Lap u), rhs := rhs }

/-- Compiled symbolic Poisson residual `-Δu - rhs` for a candidate. -/
def poissonResidual {n : Nat} (rhs candidate : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  residual (poisson rhs) candidate

/-- Scalar Laplace equation `Δu = 0`. -/
def laplace {n : Nat} : DiffExpr.Equation n Unknown :=
  { lhs := DiffExpr.Lap u, rhs := 0 }

/-- Compiled symbolic Laplace residual `Δu` for a candidate. -/
def laplaceResidual {n : Nat} (candidate : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  residual (laplace (n := n)) candidate

/-- Scalar Helmholtz equation over an explicit spatial-coordinate list.

The convention is `Δ_space u + k u = rhs`, where `k` may itself be a symbolic coefficient.
This is the ordinary Helmholtz/eigenvalue sign convention, intended for checking concrete
eigenmodes and elementary ansatzes by symbolic differentiation. It is distinct from the coercive
modified Helmholtz form `-Δu + λu = f` with `λ > 0`. -/
def helmholtzSpatial {n : Nat} (spatial : List (Verified.Expr.SymVar n))
    (k rhs : Verified.Expr (Fin n)) : DiffExpr.Equation n Unknown where
  lhs := spatialLaplacian spatial u + (.atom k : DiffExpr n Unknown) * u
  rhs := rhs

/-- One-dimensional scalar Helmholtz equation `u_xx + k u = rhs`. -/
def helmholtz1D {n : Nat} (x : Verified.Expr.SymVar n)
    (k rhs : Verified.Expr (Fin n)) : DiffExpr.Equation n Unknown :=
  helmholtzSpatial [x] k rhs

/-- Scalar wave equation over an explicit spatial-coordinate list.

The convention is `u_tt - Δ_space u = rhs`, with the time coordinate `t` named separately. The
Laplacian runs over `spatial` as given, so the caller leaves `t` out of it. -/
def waveSpatial {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (rhs : Verified.Expr (Fin n)) :
    DiffExpr.Equation n Unknown where
  lhs := DiffExpr.D2 t u - spatialLaplacian spatial u
  rhs := rhs

/-- One-spatial-dimensional wave equation `u_tt - u_xx = rhs`. -/
def wave1D {n : Nat} (t x : Verified.Expr.SymVar n) (rhs : Verified.Expr (Fin n)) :
    DiffExpr.Equation n Unknown :=
  waveSpatial t [x] rhs

/-- One-spatial-dimensional heat equation `u_t - u_xx = rhs`. -/
def heat1D {n : Nat} (t x : Verified.Expr.SymVar n) (rhs : Verified.Expr (Fin n)) :
    DiffExpr.Equation n Unknown where
  lhs := DiffExpr.D t u - DiffExpr.D2 x u
  rhs := rhs

/-- Compiled symbolic one-dimensional heat residual `u_t - u_xx - rhs` for a candidate. -/
def heat1DResidual {n : Nat} (t x : Verified.Expr.SymVar n)
    (rhs candidate : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  residual (heat1D t x rhs) candidate

end Scalar

end CAS
