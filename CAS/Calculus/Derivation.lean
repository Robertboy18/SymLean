/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Euclidean
public import CAS.Calculus.Partial

/-!
# Checked symbolic differentiation derivations

`DiffDerivation v input output` records symbolic differentiation with respect to `v` as an
indexed rule tree, one constructor for each constructor of `Verified.Expr`, and
`DiffDerivation.build` constructs the tree of any expression. The soundness theorem
`DiffDerivation.fderiv_apply_single_eq_eval_rawDerivative` says that at a point where the input
is valid, the derivative of the evaluation in the direction of the `i`-th basis vector of `ℝ^n`
is the evaluation of the raw derivative. Division and logarithm retain their nonzero conditions
from `Expr.ValidAt`, inverse sine and inverse cosine exclude their nondifferentiable endpoints,
and square root and the base of a real power retain their strictly positive branch conditions.

## Main definitions

* `DiffRule`: the differentiation rules, named by `DiffRule.label`.
* `DiffDerivation`: the indexed rule tree, built by `DiffDerivation.build`.
* `DiffDerivation.rawDerivative`, `DiffDerivation.simplifiedDerivative`: the derivative of the
  tree, before and after `trigSimplify`.
* `DiffDerivation.ruleLabel`, `DiffDerivation.children`, `DiffDerivation.Packed`: the
  projections of a node for display.

## Main results

* `DiffDerivation.rawDerivative_eq_diff`: the tree computes `input.diff v`.
* `DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative`: simplification keeps the value.
* `DiffDerivation.fderiv_apply_single_eq_eval_rawDerivative`,
  `DiffDerivation.fderiv_apply_single_eq_eval_simplifiedDerivative`: the analytic meaning of the
  raw and the simplified derivative.

## Implementation notes

The output index of every constructor is written as `input.diff v`, so the derivative formulas
are defined once, in `Expr.diff`, and the tree records only which rule was applied at each node,
without a second differentiation function; `rawDerivative_eq_diff` is proved by `cases` and
`rfl`. The tree is there for the InfoView report of `#cas [derive x]`
(`CAS.Command.Differential`), which shows it node by node through `DiffDerivation.ruleLabel` and
`DiffDerivation.children`. These read the indexed tree itself, so the rules shown are the rules
of the derivative that is proved.

The analysis lives in `CAS.Calculus.Euclidean`: the soundness theorems reduce to
`fderiv_eval_eq` and `symbolicFDeriv_apply_single_eq_diff_eval`, and the simplified form adds
`eval_trigSimplify`. The tree is generic in the variable type `ι`; only the soundness theorems
specialize to the coordinates `Fin n`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

universe u

/-- The symbolic differentiation rule represented by one derivation-tree node. -/
inductive DiffRule where
  | constant
  | variable
  | addition
  | multiplication
  | subtraction
  | division
  | negation
  | naturalPower
  | sine
  | cosine
  | arctangent
  | inverseSine
  | inverseCosine
  | exponential
  | logarithm
  | squareRoot
  | realPower
deriving BEq, DecidableEq, Repr

namespace DiffRule

/-- Human-readable mathematical name of a symbolic differentiation rule. -/
def label : DiffRule → String
  | .constant => "constant rule"
  | .variable => "variable rule"
  | .addition => "sum rule"
  | .multiplication => "product rule"
  | .subtraction => "difference rule"
  | .division => "quotient rule"
  | .negation => "negation rule"
  | .naturalPower => "natural power rule"
  | .sine => "sine chain rule"
  | .cosine => "cosine chain rule"
  | .arctangent => "arctangent chain rule"
  | .inverseSine => "inverse-sine chain rule"
  | .inverseCosine => "inverse-cosine chain rule"
  | .exponential => "exponential chain rule"
  | .logarithm => "logarithm chain rule"
  | .squareRoot => "square-root chain rule"
  | .realPower => "real power rule"

end DiffRule

/--
A checked rule tree for one raw symbolic derivative.

`DiffDerivation v input output` is inhabited only when `output` is definitionally
`input.diff v`. Constructor indices refer to `Expr.diff` instead of spelling out its formulas, so
each differentiation rule is written in one place. The separate constructors
for all five constant forms keep explanations aligned with the checked expression syntax.
-/
inductive DiffDerivation {ι : Type u} [DecidableEq ι] (v : ι) :
    Verified.Expr ι → Verified.Expr ι → Type u
  | nat (n : Nat) : DiffDerivation v (.nat n) (diff v (.nat n))
  | int (n : Int) : DiffDerivation v (.int n) (diff v (.int n))
  | rat (num : Int) (den : Nat) :
      DiffDerivation v (.rat num den) (diff v (.rat num den))
  | pi : DiffDerivation v .pi (diff v .pi)
  | e : DiffDerivation v .e (diff v .e)
  | var (name : ι) : DiffDerivation v (.var name) (diff v (.var name))
  | add {a b : Verified.Expr ι}
      (left : DiffDerivation v a (a.diff v))
      (right : DiffDerivation v b (b.diff v)) :
      DiffDerivation v (.add a b) (diff v (.add a b))
  | mul {a b : Verified.Expr ι}
      (left : DiffDerivation v a (a.diff v))
      (right : DiffDerivation v b (b.diff v)) :
      DiffDerivation v (.mul a b) (diff v (.mul a b))
  | sub {a b : Verified.Expr ι}
      (left : DiffDerivation v a (a.diff v))
      (right : DiffDerivation v b (b.diff v)) :
      DiffDerivation v (.sub a b) (diff v (.sub a b))
  | div {a b : Verified.Expr ι}
      (left : DiffDerivation v a (a.diff v))
      (right : DiffDerivation v b (b.diff v)) :
      DiffDerivation v (.div a b) (diff v (.div a b))
  | neg {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.neg a) (diff v (.neg a))
  | pow {a : Verified.Expr ι} (n : Nat) (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.pow a n) (diff v (.pow a n))
  | sin {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.sin a) (diff v (.sin a))
  | cos {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.cos a) (diff v (.cos a))
  | atan {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.atan a) (diff v (.atan a))
  | asin {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.asin a) (diff v (.asin a))
  | acos {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.acos a) (diff v (.acos a))
  | exp {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.exp a) (diff v (.exp a))
  | log {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.log a) (diff v (.log a))
  | sqrt {a : Verified.Expr ι} (inner : DiffDerivation v a (a.diff v)) :
      DiffDerivation v (.sqrt a) (diff v (.sqrt a))
  | rpow {a b : Verified.Expr ι}
      (base : DiffDerivation v a (a.diff v))
      (exponent : DiffDerivation v b (b.diff v)) :
      DiffDerivation v (.rpow a b) (diff v (.rpow a b))

namespace DiffDerivation

/-- Construct the complete rule-level derivation of `expr.diff v`. -/
def build {ι : Type*} [DecidableEq ι] (v : ι) :
    (expr : Verified.Expr ι) → DiffDerivation v expr (expr.diff v)
  | .nat n => .nat n
  | .int n => .int n
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var name => .var name
  | .add a b => .add (build v a) (build v b)
  | .mul a b => .mul (build v a) (build v b)
  | .sub a b => .sub (build v a) (build v b)
  | .div a b => .div (build v a) (build v b)
  | .neg a => .neg (build v a)
  | .pow a n => .pow n (build v a)
  | .sin a => .sin (build v a)
  | .cos a => .cos (build v a)
  | .atan a => .atan (build v a)
  | .asin a => .asin (build v a)
  | .acos a => .acos (build v a)
  | .exp a => .exp (build v a)
  | .log a => .log (build v a)
  | .sqrt a => .sqrt (build v a)
  | .rpow a b => .rpow (build v a) (build v b)

/-- The differentiation rule at the root of a derivation tree. -/
def rule {ι : Type*} [DecidableEq ι] {v : ι} {input output : Verified.Expr ι} :
    DiffDerivation v input output → DiffRule
  | .nat _ | .int _ | .rat _ _ | .pi | .e => .constant
  | .var _ => .variable
  | .add _ _ => .addition
  | .mul _ _ => .multiplication
  | .sub _ _ => .subtraction
  | .div _ _ => .division
  | .neg _ => .negation
  | .pow _ _ => .naturalPower
  | .sin _ => .sine
  | .cos _ => .cosine
  | .atan _ => .arctangent
  | .asin _ => .inverseSine
  | .acos _ => .inverseCosine
  | .exp _ => .exponential
  | .log _ => .logarithm
  | .sqrt _ => .squareRoot
  | .rpow _ _ => .realPower

/-- Human-readable label of the differentiation rule at the root of a tree. -/
def ruleLabel {ι : Type*} [DecidableEq ι] {v : ι} {input output : Verified.Expr ι}
    (derivation : DiffDerivation v input output) : String :=
  derivation.rule.label

/-- The raw derivative displayed by a derivation tree. -/
def rawDerivative {ι : Type*} [DecidableEq ι] {v : ι} {input output : Verified.Expr ι}
    (_derivation : DiffDerivation v input output) : Verified.Expr ι :=
  output

/-- The checked simplifier applied to the raw derivative displayed by a derivation tree. -/
def simplifiedDerivative {ι : Type*} [DecidableEq ι] {v : ι}
    {input output : Verified.Expr ι}
    (derivation : DiffDerivation v input output) : Verified.Expr ι :=
  trigSimplify derivation.rawDerivative

/-- A derivation node with its input and output hidden existentially, for recursive display. -/
structure Packed {ι : Type*} [DecidableEq ι] (v : ι) where
  /-- The expression differentiated at this node. -/
  input : Verified.Expr ι
  /-- The raw symbolic derivative computed at this node. -/
  output : Verified.Expr ι
  /-- The checked rule tree relating the input to its derivative. -/
  derivation : DiffDerivation v input output

/-- Forget the indices of a derivation node, keeping its source and displayed derivative. -/
def pack {ι : Type*} [DecidableEq ι] {v : ι} {input output : Verified.Expr ι}
    (derivation : DiffDerivation v input output) : Packed v :=
  ⟨input, output, derivation⟩

/-- Immediate checked child nodes in mathematical left-to-right order. -/
def children {ι : Type*} [DecidableEq ι] {v : ι} {input output : Verified.Expr ι} :
    DiffDerivation v input output → List (Packed v)
  | .add left right | .mul left right | .sub left right | .div left right =>
      [left.pack, right.pack]
  | .neg inner | .pow _ inner | .sin inner | .cos inner | .atan inner | .asin inner |
      .acos inner |
      .exp inner | .log inner | .sqrt inner =>
      [inner.pack]
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ =>
      []
  | .rpow base exponent =>
      [base.pack, exponent.pack]

namespace Packed

/-- The checked rule represented by a packed derivation node. -/
def rule {ι : Type*} [DecidableEq ι] {v : ι} (node : Packed v) : DiffRule :=
  node.derivation.rule

/-- Human-readable rule label represented by a packed derivation node. -/
def ruleLabel {ι : Type*} [DecidableEq ι] {v : ι} (node : Packed v) : String :=
  node.derivation.ruleLabel

/-- Immediate checked children of a packed derivation node. -/
def children {ι : Type*} [DecidableEq ι] {v : ι} (node : Packed v) : List (Packed v) :=
  node.derivation.children

end Packed

/--
Every rule-level derivation computes the checked raw derivative.

The proof eliminates the indexed rule tree: each constructor already uses `Expr.diff` for its output
index, so no derivative formula is reproved or duplicated here.
-/
theorem rawDerivative_eq_diff {ι : Type*} [DecidableEq ι] {v : ι}
    {input output : Verified.Expr ι} (derivation : DiffDerivation v input output) :
    derivation.rawDerivative = input.diff v := by
  cases derivation <;> rfl

/-- Simplification preserves the value of the derivative displayed by the tree. -/
theorem eval_simplifiedDerivative_eq_rawDerivative {ι : Type*} [DecidableEq ι] {v : ι}
    {input output : Verified.Expr ι} (derivation : DiffDerivation v input output)
    (ρ : ι → ℝ) :
    derivation.simplifiedDerivative.eval ρ = derivation.rawDerivative.eval ρ := by
  exact eval_trigSimplify ρ derivation.rawDerivative

/-- A derivation node computes the derivative of the evaluation in the direction of the `i`-th
basis vector at every valid point.

The side conditions are those of `Verified.Expr.ValidAt`: nonzero denominators and logarithm
arguments, strictly positive square-root arguments and real-power bases, and inverse sine and
cosine arguments different from `±1`. -/
theorem fderiv_apply_single_eq_eval_rawDerivative {n : Nat}
    {i : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : DiffDerivation i input output) (x : ℝ^n)
    (hvalid : input.ValidAt x) :
    fderiv ℝ (fun y : ℝ^n ↦ input.eval y) x (EuclideanSpace.single i 1) =
      derivation.rawDerivative.eval x := by
  rw [fderiv_eval_eq input x hvalid, symbolicFDeriv_apply_single_eq_diff_eval input x i,
    derivation.rawDerivative_eq_diff]

/-- The simplified derivative projection computes the same directional derivative. -/
theorem fderiv_apply_single_eq_eval_simplifiedDerivative {n : Nat}
    {i : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : DiffDerivation i input output) (x : ℝ^n)
    (hvalid : input.ValidAt x) :
    fderiv ℝ (fun y : ℝ^n ↦ input.eval y) x (EuclideanSpace.single i 1) =
      derivation.simplifiedDerivative.eval x := by
  rw [derivation.eval_simplifiedDerivative_eq_rawDerivative]
  exact derivation.fderiv_apply_single_eq_eval_rawDerivative x hvalid

end DiffDerivation

end Verified.Expr

end CAS
