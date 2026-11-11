/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Substitution in verified expressions

`mapVars` substitutes a reflected expression for each variable. Its evaluation
theorem is the composition law, used for scalar conditions and coordinate
changes.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Replace every variable by a symbolic expression over another variable type. -/
def mapVars {ι : Type*} {κ : Type*} (subst : ι → Verified.Expr κ) :
    Verified.Expr ι → Verified.Expr κ
  | .nat k => .nat k
  | .int k => .int k
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var i => subst i
  | .add a b => .add (mapVars subst a) (mapVars subst b)
  | .mul a b => .mul (mapVars subst a) (mapVars subst b)
  | .sub a b => .sub (mapVars subst a) (mapVars subst b)
  | .div a b => .div (mapVars subst a) (mapVars subst b)
  | .neg a => .neg (mapVars subst a)
  | .pow a k => .pow (mapVars subst a) k
  | .sin a => .sin (mapVars subst a)
  | .cos a => .cos (mapVars subst a)
  | .atan a => .atan (mapVars subst a)
  | .asin a => .asin (mapVars subst a)
  | .acos a => .acos (mapVars subst a)
  | .exp a => .exp (mapVars subst a)
  | .log a => .log (mapVars subst a)
  | .sqrt a => .sqrt (mapVars subst a)
  | .rpow a b => .rpow (mapVars subst a) (mapVars subst b)

/-- Substituting expressions for variables and then evaluating is the same as
evaluating the original expression at the substituted values. -/
@[simp] theorem eval_mapVars {ι : Type*} {κ : Type*} (ρ : κ → ℝ)
    (subst : ι → Verified.Expr κ) (expr : Verified.Expr ι) :
    (mapVars subst expr).eval ρ = expr.eval (fun i ↦ (subst i).eval ρ) := by
  induction expr <;> simp [mapVars, *]

/-- Substituting into a left-associated sum evaluates like the sum of the substituted summands,
so a sum can be normalized summand by summand after substitution. -/
theorem eval_mapVars_addList {ι : Type*} {κ : Type*} (ρ : κ → ℝ)
    (subst : ι → Verified.Expr κ) (summands : List (Verified.Expr ι)) :
    (mapVars subst (addList summands)).eval ρ =
      (addList (summands.map (mapVars subst))).eval ρ := by
  simp only [eval_mapVars, eval_addList, List.map_map, Function.comp_def]

end Verified.Expr

end CAS
