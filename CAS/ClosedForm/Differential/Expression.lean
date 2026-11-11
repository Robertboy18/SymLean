/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.SymbolicOperators
public import CAS.Expr.Rendering

/-!
# Differential expressions with unknown fields

`DiffExpr n σ` is the syntax in which a PDE on `ℝ^n` is written before any solution is chosen.
`unknown u` stands for the unknown field `u : σ`, `atom e` embeds a closed-form expression
`e : Verified.Expr (Fin n)`, `pderiv i` and `laplacian` are formal differential operators, and
the remaining constructors are the arithmetic and elementary functions of the closed-form
language. `DiffExpr.lower` substitutes a closed-form expression for each unknown (an ansatz) and
computes every derivative with the symbolic differentiator `Verified.Expr.diff`, which gives an
expression in `Verified.Expr (Fin n)`.

## Main definitions

* `DiffExpr`: the inductive syntax, with arithmetic instances so that PDEs can be written in
  ordinary notation mixing numerals, coordinates, closed-form expressions, and unknowns.
* `DiffExpr.D`, `DiffExpr.D2`, `DiffExpr.Lap`: first and second partials in a named coordinate
  and the Laplacian.
* `DiffExpr.Sym`: elementary functions on differential expressions. Several of them are
  encodings rather than primitives (`abs x = sqrt (x^2)`, `tan = sin / cos`, hyperbolic
  functions through `exp`, `max` and `min` through `abs`), so their validity conditions are
  those of the encoding.
* `DiffExpr.lower`: substitution of an ansatz and symbolic differentiation.

## Implementation notes

`lower` simplifies locally as it goes rather than transcribing literally. Atoms pass through
`Verified.Expr.simplify`; arithmetic nodes are rebuilt by the smart constructors
`Verified.Expr.mkAdd`, `Verified.Expr.mkMul`, and so on, which drop neutral and absorbing
elements and fold numerals; the elementary functions keep their raw constructors; a partial
derivative is `Verified.Expr.trigSimplify` of `Verified.Expr.diff`, and the Laplacian is
`Verified.Expr.closedLaplacian`, the simplified sum of the simplified second partials. The
result is not a normal form: whether a lowered residual vanishes is decided afterwards, by
`Alg.zeroCheck` or another checker. Each of these steps preserves evaluation
(`Verified.Expr.eval_simplify`, `Verified.Expr.eval_trigSimplify`, `Verified.Expr.eval_mkAdd`,
...), and `diff i` evaluates to the partial derivative in the `i`-th coordinate at every point
where the differentiated expression is valid (`Verified.Expr.fderiv_eval_eq`,
`Verified.Expr.symbolicFDeriv_apply_single_eq_diff_eval`). `DiffExpr.analyticRequirements`
collects these validity conditions for all derivative nodes. The `lower_*` lemmas are `rfl`
simp lemmas that unfold `lower` on the notation `a + b`, `a * b`, `a - b`, `a / b`, `-a`,
`a ^ k`, `D v a`, and `Lap a`.
-/

@[expose] public section

namespace CAS

/-- A scalar differential expression on `ℝ^n` with unknown fields indexed by `σ`. -/
inductive DiffExpr (n : Nat) (σ : Type*) where
  | atom : Verified.Expr (Fin n) → DiffExpr n σ
  | unknown : σ → DiffExpr n σ
  | add : DiffExpr n σ → DiffExpr n σ → DiffExpr n σ
  | mul : DiffExpr n σ → DiffExpr n σ → DiffExpr n σ
  | sub : DiffExpr n σ → DiffExpr n σ → DiffExpr n σ
  | div : DiffExpr n σ → DiffExpr n σ → DiffExpr n σ
  | neg : DiffExpr n σ → DiffExpr n σ
  | pow : DiffExpr n σ → Nat → DiffExpr n σ
  | sin : DiffExpr n σ → DiffExpr n σ
  | cos : DiffExpr n σ → DiffExpr n σ
  | atan : DiffExpr n σ → DiffExpr n σ
  | asin : DiffExpr n σ → DiffExpr n σ
  | acos : DiffExpr n σ → DiffExpr n σ
  | exp : DiffExpr n σ → DiffExpr n σ
  | log : DiffExpr n σ → DiffExpr n σ
  | sqrt : DiffExpr n σ → DiffExpr n σ
  | pderiv : Fin n → DiffExpr n σ → DiffExpr n σ
  | laplacian : DiffExpr n σ → DiffExpr n σ
deriving Repr

namespace DiffExpr

/-- The numeral `k` as a differential expression is the atom `.atom (.nat k)`. -/
instance {n : Nat} {σ : Type*} (k : Nat) : OfNat (DiffExpr n σ) k :=
  ⟨.atom (.nat k)⟩

/-- Addition notation for differential expressions: `a + b` is `.add a b`. -/
instance {n : Nat} {σ : Type*} : Add (DiffExpr n σ) := ⟨.add⟩
/-- Multiplication notation for differential expressions: `a * b` is `.mul a b`. -/
instance {n : Nat} {σ : Type*} : Mul (DiffExpr n σ) := ⟨.mul⟩
/-- Subtraction notation for differential expressions: `a - b` is `.sub a b`. -/
instance {n : Nat} {σ : Type*} : Sub (DiffExpr n σ) := ⟨.sub⟩
/-- Negation notation for differential expressions: `-a` is `.neg a`. -/
instance {n : Nat} {σ : Type*} : Neg (DiffExpr n σ) := ⟨.neg⟩
/-- Division notation for differential expressions: `a / b` is `.div a b`. -/
instance {n : Nat} {σ : Type*} : Div (DiffExpr n σ) := ⟨.div⟩
/-- Natural-power notation for differential expressions: `a ^ k` is `.pow a k`. -/
instance {n : Nat} {σ : Type*} : Pow (DiffExpr n σ) Nat := ⟨.pow⟩

/-- Coerces a closed-form expression `e` to the atom `.atom e`. -/
instance {n : Nat} {σ : Type*} : Coe (Verified.Expr (Fin n)) (DiffExpr n σ) :=
  ⟨fun expr ↦ .atom expr⟩

/-- Coerces a named variable `v` to the atom `.atom (.var v.idx)`. -/
instance {n : Nat} {σ : Type*} : Coe (Verified.Expr.SymVar n) (DiffExpr n σ) :=
  ⟨fun v ↦ .atom v⟩

/-- `k + d` for a literal `k` and a differential expression `d` builds `.add (.atom (.nat k)) d`. -/
instance {n : Nat} {σ : Type*} : HAdd Nat (DiffExpr n σ) (DiffExpr n σ) where
  hAdd k expr := .atom (.nat k) + expr

/-- `d + k` for a differential expression `d` and a literal `k` builds `.add d (.atom (.nat k))`. -/
instance {n : Nat} {σ : Type*} : HAdd (DiffExpr n σ) Nat (DiffExpr n σ) where
  hAdd expr k := expr + .atom (.nat k)

/-- `v + d` for a named variable `v` and a differential expression `d` builds
`.add (.atom (.var v.idx)) d`. -/
instance {n : Nat} {σ : Type*} : HAdd (Verified.Expr.SymVar n) (DiffExpr n σ) (DiffExpr n σ) where
  hAdd v expr := .atom v + expr

/-- `d + v` for a differential expression `d` and a named variable `v` builds
`.add d (.atom (.var v.idx))`. -/
instance {n : Nat} {σ : Type*} : HAdd (DiffExpr n σ) (Verified.Expr.SymVar n) (DiffExpr n σ) where
  hAdd expr v := expr + .atom v

/-- `e + d` for a closed-form expression `e` and a differential expression `d` builds
`.add (.atom e) d`. -/
instance {n : Nat} {σ : Type*} : HAdd (Verified.Expr (Fin n)) (DiffExpr n σ) (DiffExpr n σ) where
  hAdd expr diffExpr := .atom expr + diffExpr

/-- `d + e` for a differential expression `d` and a closed-form expression `e` builds
`.add d (.atom e)`. -/
instance {n : Nat} {σ : Type*} : HAdd (DiffExpr n σ) (Verified.Expr (Fin n)) (DiffExpr n σ) where
  hAdd diffExpr expr := diffExpr + .atom expr

/-- `k - d` for a literal `k` and a differential expression `d` builds `.sub (.atom (.nat k)) d`. -/
instance {n : Nat} {σ : Type*} : HSub Nat (DiffExpr n σ) (DiffExpr n σ) where
  hSub k expr := .atom (.nat k) - expr

/-- `d - k` for a differential expression `d` and a literal `k` builds `.sub d (.atom (.nat k))`. -/
instance {n : Nat} {σ : Type*} : HSub (DiffExpr n σ) Nat (DiffExpr n σ) where
  hSub expr k := expr - .atom (.nat k)

/-- `v - d` for a named variable `v` and a differential expression `d` builds
`.sub (.atom (.var v.idx)) d`. -/
instance {n : Nat} {σ : Type*} : HSub (Verified.Expr.SymVar n) (DiffExpr n σ) (DiffExpr n σ) where
  hSub v expr := .atom v - expr

/-- `d - v` for a differential expression `d` and a named variable `v` builds
`.sub d (.atom (.var v.idx))`. -/
instance {n : Nat} {σ : Type*} : HSub (DiffExpr n σ) (Verified.Expr.SymVar n) (DiffExpr n σ) where
  hSub expr v := expr - .atom v

/-- `e - d` for a closed-form expression `e` and a differential expression `d` builds
`.sub (.atom e) d`. -/
instance {n : Nat} {σ : Type*} : HSub (Verified.Expr (Fin n)) (DiffExpr n σ) (DiffExpr n σ) where
  hSub expr diffExpr := .atom expr - diffExpr

/-- `d - e` for a differential expression `d` and a closed-form expression `e` builds
`.sub d (.atom e)`. -/
instance {n : Nat} {σ : Type*} : HSub (DiffExpr n σ) (Verified.Expr (Fin n)) (DiffExpr n σ) where
  hSub diffExpr expr := diffExpr - .atom expr

/-- `k * d` for a literal `k` and a differential expression `d` builds `.mul (.atom (.nat k)) d`. -/
instance {n : Nat} {σ : Type*} : HMul Nat (DiffExpr n σ) (DiffExpr n σ) where
  hMul k expr := .atom (.nat k) * expr

/-- `d * k` for a differential expression `d` and a literal `k` builds `.mul d (.atom (.nat k))`. -/
instance {n : Nat} {σ : Type*} : HMul (DiffExpr n σ) Nat (DiffExpr n σ) where
  hMul expr k := expr * .atom (.nat k)

/-- `v * d` for a named variable `v` and a differential expression `d` builds
`.mul (.atom (.var v.idx)) d`. -/
instance {n : Nat} {σ : Type*} : HMul (Verified.Expr.SymVar n) (DiffExpr n σ) (DiffExpr n σ) where
  hMul v expr := .atom v * expr

/-- `d * v` for a differential expression `d` and a named variable `v` builds
`.mul d (.atom (.var v.idx))`. -/
instance {n : Nat} {σ : Type*} : HMul (DiffExpr n σ) (Verified.Expr.SymVar n) (DiffExpr n σ) where
  hMul expr v := expr * .atom v

/-- `e * d` for a closed-form expression `e` and a differential expression `d` builds
`.mul (.atom e) d`. -/
instance {n : Nat} {σ : Type*} : HMul (Verified.Expr (Fin n)) (DiffExpr n σ) (DiffExpr n σ) where
  hMul expr diffExpr := .atom expr * diffExpr

/-- `d * e` for a differential expression `d` and a closed-form expression `e` builds
`.mul d (.atom e)`. -/
instance {n : Nat} {σ : Type*} : HMul (DiffExpr n σ) (Verified.Expr (Fin n)) (DiffExpr n σ) where
  hMul diffExpr expr := diffExpr * .atom expr

/-- `k / d` for a literal `k` and a differential expression `d` builds `.div (.atom (.nat k)) d`. -/
instance {n : Nat} {σ : Type*} : HDiv Nat (DiffExpr n σ) (DiffExpr n σ) where
  hDiv k expr := .atom (.nat k) / expr

/-- `d / k` for a differential expression `d` and a literal `k` builds `.div d (.atom (.nat k))`. -/
instance {n : Nat} {σ : Type*} : HDiv (DiffExpr n σ) Nat (DiffExpr n σ) where
  hDiv expr k := expr / .atom (.nat k)

/-- `v / d` for a named variable `v` and a differential expression `d` builds
`.div (.atom (.var v.idx)) d`. -/
instance {n : Nat} {σ : Type*} : HDiv (Verified.Expr.SymVar n) (DiffExpr n σ) (DiffExpr n σ) where
  hDiv v expr := .atom v / expr

/-- `d / v` for a differential expression `d` and a named variable `v` builds
`.div d (.atom (.var v.idx))`. -/
instance {n : Nat} {σ : Type*} : HDiv (DiffExpr n σ) (Verified.Expr.SymVar n) (DiffExpr n σ) where
  hDiv expr v := expr / .atom v

/-- `e / d` for a closed-form expression `e` and a differential expression `d` builds
`.div (.atom e) d`. -/
instance {n : Nat} {σ : Type*} : HDiv (Verified.Expr (Fin n)) (DiffExpr n σ) (DiffExpr n σ) where
  hDiv expr diffExpr := .atom expr / diffExpr

/-- `d / e` for a differential expression `d` and a closed-form expression `e` builds
`.div d (.atom e)`. -/
instance {n : Nat} {σ : Type*} : HDiv (DiffExpr n σ) (Verified.Expr (Fin n)) (DiffExpr n σ) where
  hDiv diffExpr expr := diffExpr / .atom expr

/-- The first partial derivative with respect to a named coordinate. -/
def D {n : Nat} {σ : Type*} (v : Verified.Expr.SymVar n) (expr : DiffExpr n σ) :
    DiffExpr n σ :=
  .pderiv v.idx expr

/-- The second partial derivative with respect to a named coordinate. -/
def D2 {n : Nat} {σ : Type*} (v : Verified.Expr.SymVar n) (expr : DiffExpr n σ) :
    DiffExpr n σ :=
  D v (D v expr)

/-- The symbolic Laplacian of a differential expression. -/
def Lap {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .laplacian expr

namespace Sym

/-- Symbolic arctangent of a differential expression. -/
def atan {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .atan expr

/-- Symbolic inverse sine of a differential expression. -/
def asin {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .asin expr

/-- Symbolic inverse cosine of a differential expression. -/
def acos {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .acos expr

/-- Symbolic logarithm of a differential expression. -/
def log {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .log expr

/-- Symbolic absolute value, represented by `sqrt (x²)`. -/
def abs {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .sqrt (expr ^ 2)

/-- Symbolic tangent, represented by `sin x / cos x`. -/
def tan {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  .sin expr / .cos expr

/-- Symbolic secant, represented by `1 / cos x`. -/
def sec {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  1 / .cos expr

/-- Symbolic hyperbolic sine. -/
def sinh {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  (.exp expr - .exp (-expr)) / 2

/-- Symbolic hyperbolic cosine. -/
def cosh {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  (.exp expr + .exp (-expr)) / 2

/-- Symbolic hyperbolic tangent. -/
def tanh {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  sinh expr / cosh expr

/-- Symbolic hyperbolic secant. -/
def sech {n : Nat} {σ : Type*} (expr : DiffExpr n σ) : DiffExpr n σ :=
  1 / cosh expr

/-- Symbolic maximum, represented by `(a + b + abs (a - b)) / 2`. -/
def max {n : Nat} {σ : Type*} (a b : DiffExpr n σ) : DiffExpr n σ :=
  (a + b + abs (a - b)) / 2

/-- Symbolic minimum, represented by `(a + b - abs (a - b)) / 2`. -/
def min {n : Nat} {σ : Type*} (a b : DiffExpr n σ) : DiffExpr n σ :=
  (a + b - abs (a - b)) / 2

end Sym

/-- Lower a differential expression after assigning a closed form to each unknown field. -/
def lower {n : Nat} {σ : Type*}
    (ansatz : σ → Verified.Expr (Fin n)) : DiffExpr n σ → Verified.Expr (Fin n)
  | .atom expr => Verified.Expr.simplify expr
  | .unknown u => ansatz u
  | .add a b => Verified.Expr.mkAdd (lower ansatz a) (lower ansatz b)
  | .mul a b => Verified.Expr.mkMul (lower ansatz a) (lower ansatz b)
  | .sub a b => Verified.Expr.mkSub (lower ansatz a) (lower ansatz b)
  | .div a b => Verified.Expr.mkDiv (lower ansatz a) (lower ansatz b)
  | .neg a => Verified.Expr.mkNeg (lower ansatz a)
  | .pow a k => Verified.Expr.mkPow (lower ansatz a) k
  | .sin a => .sin (lower ansatz a)
  | .cos a => .cos (lower ansatz a)
  | .atan a => .atan (lower ansatz a)
  | .asin a => .asin (lower ansatz a)
  | .acos a => .acos (lower ansatz a)
  | .exp a => .exp (lower ansatz a)
  | .log a => .log (lower ansatz a)
  | .sqrt a => .sqrt (lower ansatz a)
  | .pderiv i a => Verified.Expr.trigSimplify ((lower ansatz a).diff i)
  | .laplacian a => Verified.Expr.closedLaplacian (lower ansatz a)

/-- `lower` sends a formal sum to the smart constructor `mkAdd` of the lowered operands. -/
@[simp] theorem lower_add {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a b : DiffExpr n σ) :
    lower ansatz (a + b) = Verified.Expr.mkAdd (lower ansatz a) (lower ansatz b) :=
  rfl

/-- `lower` sends a formal product to the smart constructor `mkMul` of the lowered operands. -/
@[simp] theorem lower_mul {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a b : DiffExpr n σ) :
    lower ansatz (a * b) = Verified.Expr.mkMul (lower ansatz a) (lower ansatz b) :=
  rfl

/-- `lower` sends a formal difference to `mkSub` of the lowered operands. -/
@[simp] theorem lower_sub {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a b : DiffExpr n σ) :
    lower ansatz (a - b) = Verified.Expr.mkSub (lower ansatz a) (lower ansatz b) :=
  rfl

/-- `lower` sends a formal quotient to `mkDiv` of the lowered operands. -/
@[simp] theorem lower_div {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a b : DiffExpr n σ) :
    lower ansatz (a / b) = Verified.Expr.mkDiv (lower ansatz a) (lower ansatz b) :=
  rfl

/-- `lower` sends a formal negation to `mkNeg` of the lowered operand. -/
@[simp] theorem lower_neg {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a : DiffExpr n σ) :
    lower ansatz (-a) = Verified.Expr.mkNeg (lower ansatz a) :=
  rfl

/-- `lower` sends a formal natural power to `mkPow` of the lowered base. -/
@[simp] theorem lower_pow {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a : DiffExpr n σ) (k : Nat) :
    lower ansatz (a ^ k) = Verified.Expr.mkPow (lower ansatz a) k :=
  rfl

/-- Lowering a partial derivative differentiates the lowered operand symbolically in the
coordinate `v.idx` and then applies `trigSimplify`. -/
@[simp] theorem lower_D {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (v : Verified.Expr.SymVar n) (a : DiffExpr n σ) :
    lower ansatz (D v a) = Verified.Expr.trigSimplify ((lower ansatz a).diff v.idx) :=
  rfl

/-- Lowering the Laplacian applies the closed-form symbolic Laplacian to the lowered operand. -/
@[simp] theorem lower_Lap {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n))
    (a : DiffExpr n σ) :
    lower ansatz (Lap a) = Verified.Expr.closedLaplacian (lower ansatz a) :=
  rfl

end DiffExpr

end CAS
