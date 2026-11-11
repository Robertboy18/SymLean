/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Operators

/-!
# Named variables for verified expressions

Readable names for coordinates of `Verified.Expr (Fin n)`.
A `SymVar n` stores a semantic coordinate `idx : Fin n` and a presentation-only
label. Evaluation, differentiation, and every soundness theorem depend only on
the index; changing `prettyName` cannot change the denoted function.

The arithmetic instances let backend code write expressions such as
`Euclid2.x ^ 2 + Euclid2.y ^ 2` without constructing AST nodes explicitly.
Interactive `#cas` users do not need this API because the command reifies
ordinary calculator notation itself.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- A Euclidean coordinate together with its presentation name. -/
structure SymVar (n : Nat) where
  /-- The coordinate used by evaluation and differentiation. -/
  idx : Fin n
  /-- A label used only when presenting the coordinate to a user. -/
  prettyName : String
deriving Repr

namespace SymVar

/-- The coordinate expression represented by a named variable. -/
def expr {n : Nat} (v : SymVar n) : Verified.Expr (Fin n) :=
  .var v.idx

/-- Coerces a named variable `v` to its coordinate expression `expr v = .var v.idx`. -/
instance {n : Nat} : Coe (SymVar n) (Verified.Expr (Fin n)) := ⟨expr⟩

/-- `v ^ k` for a named variable `v` and a natural `k` builds `.pow (.var v.idx) k`. -/
instance {n : Nat} : HPow (SymVar n) Nat (Verified.Expr (Fin n)) where
  hPow v k := (v : Verified.Expr (Fin n)) ^ k

/-- `a + b` for named variables `a` and `b` builds `.add (.var a.idx) (.var b.idx)`. -/
instance {n : Nat} : HAdd (SymVar n) (SymVar n) (Verified.Expr (Fin n)) where
  hAdd a b := (a : Verified.Expr (Fin n)) + (b : Verified.Expr (Fin n))

/-- `k + v` for a literal `k` and a named variable `v` builds `.add (.nat k) (.var v.idx)`. -/
instance {n : Nat} : HAdd Nat (SymVar n) (Verified.Expr (Fin n)) where
  hAdd k v := (Verified.Expr.nat k : Verified.Expr (Fin n)) + (v : Verified.Expr (Fin n))

/-- `v + k` for a named variable `v` and a literal `k` builds `.add (.var v.idx) (.nat k)`. -/
instance {n : Nat} : HAdd (SymVar n) Nat (Verified.Expr (Fin n)) where
  hAdd v k := (v : Verified.Expr (Fin n)) + (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `k + e` for a literal `k` and an expression `e` builds `.add (.nat k) e`. -/
instance {n : Nat} : HAdd Nat (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hAdd k expr := (Verified.Expr.nat k : Verified.Expr (Fin n)) + expr

/-- `e + k` for an expression `e` and a literal `k` builds `.add e (.nat k)`. -/
instance {n : Nat} : HAdd (Verified.Expr (Fin n)) Nat (Verified.Expr (Fin n)) where
  hAdd expr k := expr + (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `v + e` for a named variable `v` and an expression `e` builds `.add (.var v.idx) e`. -/
instance {n : Nat} : HAdd (SymVar n) (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hAdd a b := (a : Verified.Expr (Fin n)) + b

/-- `e + v` for an expression `e` and a named variable `v` builds `.add e (.var v.idx)`. -/
instance {n : Nat} : HAdd (Verified.Expr (Fin n)) (SymVar n) (Verified.Expr (Fin n)) where
  hAdd a b := a + (b : Verified.Expr (Fin n))

/-- `a - b` for named variables `a` and `b` builds `.sub (.var a.idx) (.var b.idx)`. -/
instance {n : Nat} : HSub (SymVar n) (SymVar n) (Verified.Expr (Fin n)) where
  hSub a b := (a : Verified.Expr (Fin n)) - (b : Verified.Expr (Fin n))

/-- `k - v` for a literal `k` and a named variable `v` builds `.sub (.nat k) (.var v.idx)`. -/
instance {n : Nat} : HSub Nat (SymVar n) (Verified.Expr (Fin n)) where
  hSub k v := (Verified.Expr.nat k : Verified.Expr (Fin n)) - (v : Verified.Expr (Fin n))

/-- `v - k` for a named variable `v` and a literal `k` builds `.sub (.var v.idx) (.nat k)`. -/
instance {n : Nat} : HSub (SymVar n) Nat (Verified.Expr (Fin n)) where
  hSub v k := (v : Verified.Expr (Fin n)) - (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `k - e` for a literal `k` and an expression `e` builds `.sub (.nat k) e`. -/
instance {n : Nat} : HSub Nat (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hSub k expr := (Verified.Expr.nat k : Verified.Expr (Fin n)) - expr

/-- `e - k` for an expression `e` and a literal `k` builds `.sub e (.nat k)`. -/
instance {n : Nat} : HSub (Verified.Expr (Fin n)) Nat (Verified.Expr (Fin n)) where
  hSub expr k := expr - (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `v - e` for a named variable `v` and an expression `e` builds `.sub (.var v.idx) e`. -/
instance {n : Nat} : HSub (SymVar n) (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hSub a b := (a : Verified.Expr (Fin n)) - b

/-- `e - v` for an expression `e` and a named variable `v` builds `.sub e (.var v.idx)`. -/
instance {n : Nat} : HSub (Verified.Expr (Fin n)) (SymVar n) (Verified.Expr (Fin n)) where
  hSub a b := a - (b : Verified.Expr (Fin n))

/-- `k * v` for a literal `k` and a named variable `v` builds `.mul (.nat k) (.var v.idx)`. -/
instance {n : Nat} : HMul Nat (SymVar n) (Verified.Expr (Fin n)) where
  hMul k v := (Verified.Expr.nat k : Verified.Expr (Fin n)) * (v : Verified.Expr (Fin n))

/-- `k * e` for a literal `k` and an expression `e` builds `.mul (.nat k) e`. -/
instance {n : Nat} : HMul Nat (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hMul k expr := (Verified.Expr.nat k : Verified.Expr (Fin n)) * expr

/-- `v * k` for a named variable `v` and a literal `k` builds `.mul (.var v.idx) (.nat k)`. -/
instance {n : Nat} : HMul (SymVar n) Nat (Verified.Expr (Fin n)) where
  hMul v k := (v : Verified.Expr (Fin n)) * (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `e * k` for an expression `e` and a literal `k` builds `.mul e (.nat k)`. -/
instance {n : Nat} : HMul (Verified.Expr (Fin n)) Nat (Verified.Expr (Fin n)) where
  hMul expr k := expr * (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `a * b` for named variables `a` and `b` builds `.mul (.var a.idx) (.var b.idx)`. -/
instance {n : Nat} : HMul (SymVar n) (SymVar n) (Verified.Expr (Fin n)) where
  hMul a b := (a : Verified.Expr (Fin n)) * (b : Verified.Expr (Fin n))

/-- `v * e` for a named variable `v` and an expression `e` builds `.mul (.var v.idx) e`. -/
instance {n : Nat} : HMul (SymVar n) (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hMul a b := (a : Verified.Expr (Fin n)) * b

/-- `e * v` for an expression `e` and a named variable `v` builds `.mul e (.var v.idx)`. -/
instance {n : Nat} : HMul (Verified.Expr (Fin n)) (SymVar n) (Verified.Expr (Fin n)) where
  hMul a b := a * (b : Verified.Expr (Fin n))

/-- `a / b` for named variables `a` and `b` builds `.div (.var a.idx) (.var b.idx)`. -/
instance {n : Nat} : HDiv (SymVar n) (SymVar n) (Verified.Expr (Fin n)) where
  hDiv a b := (a : Verified.Expr (Fin n)) / (b : Verified.Expr (Fin n))

/-- `k / v` for a literal `k` and a named variable `v` builds `.div (.nat k) (.var v.idx)`. -/
instance {n : Nat} : HDiv Nat (SymVar n) (Verified.Expr (Fin n)) where
  hDiv k v := (Verified.Expr.nat k : Verified.Expr (Fin n)) / (v : Verified.Expr (Fin n))

/-- `v / k` for a named variable `v` and a literal `k` builds `.div (.var v.idx) (.nat k)`. -/
instance {n : Nat} : HDiv (SymVar n) Nat (Verified.Expr (Fin n)) where
  hDiv v k := (v : Verified.Expr (Fin n)) / (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `k / e` for a literal `k` and an expression `e` builds `.div (.nat k) e`. -/
instance {n : Nat} : HDiv Nat (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hDiv k expr := (Verified.Expr.nat k : Verified.Expr (Fin n)) / expr

/-- `e / k` for an expression `e` and a literal `k` builds `.div e (.nat k)`. -/
instance {n : Nat} : HDiv (Verified.Expr (Fin n)) Nat (Verified.Expr (Fin n)) where
  hDiv expr k := expr / (Verified.Expr.nat k : Verified.Expr (Fin n))

/-- `v / e` for a named variable `v` and an expression `e` builds `.div (.var v.idx) e`. -/
instance {n : Nat} : HDiv (SymVar n) (Verified.Expr (Fin n)) (Verified.Expr (Fin n)) where
  hDiv a b := (a : Verified.Expr (Fin n)) / b

/-- `e / v` for an expression `e` and a named variable `v` builds `.div e (.var v.idx)`. -/
instance {n : Nat} : HDiv (Verified.Expr (Fin n)) (SymVar n) (Verified.Expr (Fin n)) where
  hDiv a b := a / (b : Verified.Expr (Fin n))

/-!
These `simp` lemmas rewrite the named-variable notation to expressions in the coordinates
`.var v.idx`. Each holds by `rfl`, so `simp` can unfold notation such as `x ^ 2 + y ^ 2` to
ordinary `Verified.Expr` syntax.
-/

/-- Coercing a named variable to an expression yields the coordinate `.var v.idx`; the
presentation name is discarded. -/
@[simp] theorem coe_eq_var {n : Nat} (v : SymVar n) :
    (v : Verified.Expr (Fin n)) = .var v.idx := rfl

/-- A natural power of a named variable is the power of its coordinate expression. -/
@[simp] theorem pow_eq_constructor {n : Nat} (v : SymVar n) (k : Nat) :
    v ^ k = (.var v.idx : Verified.Expr (Fin n)) ^ k := rfl

/-- `k + v` for a literal `k` and named variable `v` unfolds to `.add (.nat k) (.var v.idx)`. -/
@[simp] theorem nat_add_eq_constructor {n : Nat} (k : Nat) (v : SymVar n) :
    k + v = (.add (.nat k) (.var v.idx) : Verified.Expr (Fin n)) := rfl

/-- `v + k` for a named variable `v` and literal `k` unfolds to `.add (.var v.idx) (.nat k)`. -/
@[simp] theorem add_nat_eq_constructor {n : Nat} (v : SymVar n) (k : Nat) :
    v + k = (.add (.var v.idx) (.nat k) : Verified.Expr (Fin n)) := rfl

/-- `k - v` for a literal `k` and named variable `v` unfolds to `.sub (.nat k) (.var v.idx)`. -/
@[simp] theorem nat_sub_eq_constructor {n : Nat} (k : Nat) (v : SymVar n) :
    k - v = (.sub (.nat k) (.var v.idx) : Verified.Expr (Fin n)) := rfl

/-- `v - k` for a named variable `v` and literal `k` unfolds to `.sub (.var v.idx) (.nat k)`. -/
@[simp] theorem sub_nat_eq_constructor {n : Nat} (v : SymVar n) (k : Nat) :
    v - k = (.sub (.var v.idx) (.nat k) : Verified.Expr (Fin n)) := rfl

/-- `k * v` for a literal `k` and named variable `v` unfolds to `.mul (.nat k) (.var v.idx)`. -/
@[simp] theorem nat_mul_eq_constructor {n : Nat} (k : Nat) (v : SymVar n) :
    k * v = (.mul (.nat k) (.var v.idx) : Verified.Expr (Fin n)) := rfl

/-- `v * k` for a named variable `v` and literal `k` unfolds to `.mul (.var v.idx) (.nat k)`. -/
@[simp] theorem mul_nat_eq_constructor {n : Nat} (v : SymVar n) (k : Nat) :
    v * k = (.mul (.var v.idx) (.nat k) : Verified.Expr (Fin n)) := rfl

/-- `k / v` for a literal `k` and named variable `v` unfolds to `.div (.nat k) (.var v.idx)`. -/
@[simp] theorem nat_div_eq_constructor {n : Nat} (k : Nat) (v : SymVar n) :
    k / v = (.div (.nat k) (.var v.idx) : Verified.Expr (Fin n)) := rfl

/-- `v / k` for a named variable `v` and literal `k` unfolds to `.div (.var v.idx) (.nat k)`. -/
@[simp] theorem div_nat_eq_constructor {n : Nat} (v : SymVar n) (k : Nat) :
    v / k = (.div (.var v.idx) (.nat k) : Verified.Expr (Fin n)) := rfl

end SymVar

/-- A type whose values select a differentiation coordinate. -/
class DiffVar (ν : Type*) (ι : outParam (Type*)) where
  /-- Extract the semantic coordinate index. -/
  index : ν → ι

/-- Every index type selects its own coordinates: the index of `i : ι` is `i`. -/
instance {ι : Type*} : DiffVar ι ι where
  index := id

/-- A named variable selects the coordinate `v.idx : Fin n`; its presentation name is ignored. -/
instance {n : Nat} : DiffVar (SymVar n) (Fin n) where
  index v := v.idx

/-- Coordinate expression notation for an arbitrary index: `𝕏[i]`. -/
notation "𝕏[" i "]" => Verified.Expr.var i

end Verified.Expr

namespace Euclid1

/-- Time coordinate for one-dimensional symbolic ODE examples. -/
@[simp] def t : Verified.Expr.SymVar 1 := ⟨0, "t"⟩

/-- Spatial coordinate for one-dimensional symbolic examples. -/
@[simp] def x : Verified.Expr.SymVar 1 := ⟨0, "x"⟩

end Euclid1

namespace Euclid2

/-- First coordinate of a two-dimensional symbolic expression. -/
@[simp] def x : Verified.Expr.SymVar 2 := ⟨0, "x"⟩

/-- Second coordinate of a two-dimensional symbolic expression. -/
@[simp] def y : Verified.Expr.SymVar 2 := ⟨1, "y"⟩

end Euclid2

namespace Euclid3

/-- First coordinate of a three-dimensional symbolic expression. -/
@[simp] def x : Verified.Expr.SymVar 3 := ⟨0, "x"⟩

/-- Second coordinate of a three-dimensional symbolic expression. -/
@[simp] def y : Verified.Expr.SymVar 3 := ⟨1, "y"⟩

/-- Third coordinate of a three-dimensional symbolic expression. -/
@[simp] def z : Verified.Expr.SymVar 3 := ⟨2, "z"⟩

end Euclid3

end CAS
