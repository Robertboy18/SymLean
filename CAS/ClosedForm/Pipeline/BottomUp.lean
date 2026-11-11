/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Rational

/-!
# Bottom-up side-conditioned expression transforms

The common recursion of the side-conditioned closed-form passes. A caller supplies a local
transformation for one rebuilt node, together with proofs that the transformation preserves
inherited side conditions and evaluation. `BottomUp.run` applies it throughout the expression
tree, and `BottomUp.eval_run` is the resulting soundness theorem.

## Implementation notes

The node transformation receives the rebuilt node together with the conditions collected in its
children, and returns the new node with the full condition list. It has two obligations: the
returned list implies the inherited one (`inherited_sound`), and under the returned list the new
node evaluates like the rebuilt one (`top_sound`). `BottomUp.eval_run` follows by structural
induction on the expression, through `BottomUp.eval_unaryStep` and `BottomUp.eval_binaryStep`.
The deep forms of the exp-log, square-root square, numeral square-root and square-root pairing
passes are `BottomUp.run` of a one-node step, so each of them proves only that step; the
real-power pass also proves the exponent identification (`identifyExponents`) that follows its
traversal.
-/

@[expose] public section

namespace CAS.Verified.Expr
namespace BottomUp

/--
Rebuild an expression from the leaves upward, applying `top` after each node.

The second argument to `top` contains exactly the side conditions inherited
from the recursively transformed children.
-/
def run {ι : Type*} [DecidableEq ι]
    (top : Verified.Expr ι → List (Verified.Expr ι) → Alg.NormResult ι) :
    Verified.Expr ι → Alg.NormResult ι
  | .nat n => top (.nat n) []
  | .int z => top (.int z) []
  | .rat num den => top (.rat num den) []
  | .pi => top .pi []
  | .e => top .e []
  | .var i => top (.var i) []
  | .add a b =>
      let ra := run top a
      let rb := run top b
      top (.add ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)
  | .mul a b =>
      let ra := run top a
      let rb := run top b
      top (.mul ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)
  | .sub a b =>
      let ra := run top a
      let rb := run top b
      top (.sub ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)
  | .div a b =>
      let ra := run top a
      let rb := run top b
      top (.div ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)
  | .neg a =>
      let ra := run top a
      top (.neg ra.expr) ra.nonzero
  | .pow a k =>
      let ra := run top a
      top (.pow ra.expr k) ra.nonzero
  | .sin a =>
      let ra := run top a
      top (.sin ra.expr) ra.nonzero
  | .cos a =>
      let ra := run top a
      top (.cos ra.expr) ra.nonzero
  | .atan a =>
      let ra := run top a
      top (.atan ra.expr) ra.nonzero
  | .asin a =>
      let ra := run top a
      top (.asin ra.expr) ra.nonzero
  | .acos a =>
      let ra := run top a
      top (.acos ra.expr) ra.nonzero
  | .exp a =>
      let ra := run top a
      top (.exp ra.expr) ra.nonzero
  | .log a =>
      let ra := run top a
      top (.log ra.expr) ra.nonzero
  | .sqrt a =>
      let ra := run top a
      top (.sqrt ra.expr) ra.nonzero
  | .rpow a b =>
      let ra := run top a
      let rb := run top b
      top (.rpow ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)

/-- A binary rewrite preserves evaluation if the parent step preserves both its value
and the conditions inherited from its two sound child rewrites. -/
theorem eval_binaryStep {ι : Type*}
    (top : Verified.Expr ι → List (Verified.Expr ι) → Alg.NormResult ι)
    (inherited_sound : ∀ {ρ : ι → ℝ} rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        Alg.SideHolds ρ inherited)
    (top_sound : ∀ (ρ : ι → ℝ) rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        (top rebuilt inherited).expr.eval ρ = rebuilt.eval ρ)
    (ρ : ι → ℝ) (op : Verified.Expr ι → Verified.Expr ι → Verified.Expr ι)
    (a b : Verified.Expr ι) (ra rb : Alg.NormResult ι)
    (children_sound :
      Alg.SideHolds ρ ra.nonzero →
        Alg.SideHolds ρ rb.nonzero →
          (op ra.expr rb.expr).eval ρ = (op a b).eval ρ)
    (hside : Alg.SideHolds ρ
      (top (op ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)).nonzero) :
    (top (op ra.expr rb.expr) (ra.nonzero ++ rb.nonzero)).expr.eval ρ =
      (op a b).eval ρ :=
  have h := inherited_sound (ρ := ρ) _ _ hside
  (top_sound ρ _ _ hside).trans (children_sound h.append_left h.append_right)

/-- A unary rewrite preserves evaluation if the parent step preserves its value
and the conditions inherited from the sound child rewrite. -/
theorem eval_unaryStep {ι : Type*}
    (top : Verified.Expr ι → List (Verified.Expr ι) → Alg.NormResult ι)
    (inherited_sound : ∀ {ρ : ι → ℝ} rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        Alg.SideHolds ρ inherited)
    (top_sound : ∀ (ρ : ι → ℝ) rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        (top rebuilt inherited).expr.eval ρ = rebuilt.eval ρ)
    (ρ : ι → ℝ) (op : Verified.Expr ι → Verified.Expr ι)
    (a : Verified.Expr ι) (ra : Alg.NormResult ι)
    (child_sound : Alg.SideHolds ρ ra.nonzero →
      (op ra.expr).eval ρ = (op a).eval ρ)
    (hside : Alg.SideHolds ρ (top (op ra.expr) ra.nonzero).nonzero) :
    (top (op ra.expr) ra.nonzero).expr.eval ρ = (op a).eval ρ :=
  (top_sound ρ _ _ hside).trans (child_sound (inherited_sound (ρ := ρ) _ _ hside))

/--
A node transform that preserves inherited side conditions and evaluation gives
a sound bottom-up transform.
-/
theorem eval_run {ι : Type*} [DecidableEq ι]
    (top : Verified.Expr ι → List (Verified.Expr ι) → Alg.NormResult ι)
    (inherited_sound : ∀ {ρ : ι → ℝ} rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        Alg.SideHolds ρ inherited)
    (top_sound : ∀ (ρ : ι → ℝ) rebuilt inherited,
      Alg.SideHolds ρ (top rebuilt inherited).nonzero →
        (top rebuilt inherited).expr.eval ρ = rebuilt.eval ρ)
    (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι,
      Alg.SideHolds ρ (run top expr).nonzero →
        (run top expr).expr.eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | nat _ | int _ | rat _ _ | pi | e | var _ => exact top_sound ρ _ []
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb | rpow a b iha ihb =>
      exact eval_binaryStep top inherited_sound top_sound ρ _ a b _ _
        fun ha hb ↦ by simp [iha ha, ihb hb]
  | pow a k iha =>
      exact eval_unaryStep top inherited_sound top_sound ρ (fun x ↦ .pow x k) a _
        fun ha ↦ by simp [iha ha]
  | neg a iha | sin a iha | cos a iha | atan a iha | asin a iha | acos a iha | exp a iha
  | log a iha | sqrt a iha =>
      exact eval_unaryStep top inherited_sound top_sound ρ _ a _ fun ha ↦ by simp [iha ha]

end BottomUp
end CAS.Verified.Expr
