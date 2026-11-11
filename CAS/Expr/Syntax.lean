/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Verified real-expression syntax and semantics

`Verified.Expr ι` is the deeply embedded syntax used by the symbolic procedures of `CAS`. Variable
labels may inhabit any universe: `Expr ι` supports `ι : Type*`, including `String`, `Fin n`, and
types whose elements are themselves types. Syntax and evaluation do not require decidable equality
on labels; symbolic differentiation requires `DecidableEq ι`.

The theorem-facing reifier stores real-valued terms in a finite coordinate table, independently
of the universes of their source data. Its `Fin n` labels and the `Nat` serialization format
are concrete specializations of this expression language.

The constructors are integer and rational literals, `π`, `e`, variables, the field operations
`add`, `mul`, `sub`, `div`, `neg`, natural powers `pow`, the elementary functions `sin`, `cos`,
`atan`, `asin`, `acos`, `exp`, `log`, `sqrt`, and the real power `rpow a b`, which evaluates to
`a ^ b` in the sense of `Real.rpow` and is differentiated only at positive bases.

## Main definitions

* `Expr.eval`: the real-valued semantics of an expression in an environment `ι → ℝ`.
* `Expr.ValidAt`: the domain conditions required by the classical real differentiation rules.
* `Expr.ValidityRequirements`, `Expr.validityRequirements`: the same conditions as lists of
  expressions that must be nonzero or positive, with `ValidityRequirements.validAt_of_holds`.
* `Expr.diff`: the syntax-producing symbolic derivative with respect to one variable.
* `Expr.addList`, `Expr.mulList`, `Expr.containsVar`: finite sums, finite products, and variable
  occurrence.

## Implementation notes

Evaluation is total because the corresponding real operations of Mathlib are total: division by
zero and values of `Real.log` or `Real.sqrt` outside their usual calculus domains still have
meanings in `ℝ`. We keep the analytic hypotheses apart, in `Expr.ValidAt`, which records what a
later correctness theorem needs to interpret a symbolic transformation as an analytic one. Only
syntax and its elementary semantics are here. The correctness theorems for Euclidean
differentiation and checked integration are in the calculus modules, so the expression language
does not depend on that analysis.
-/

@[expose] public section

namespace CAS.Verified

open Real

/-! ## Expression syntax -/

/--
A deeply embedded real expression whose variable labels may inhabit any universe.

The constructor `.rat num den` stores a natural denominator because it mirrors parser output.
Mathematically meaningful use of this constructor is guarded by `Expr.ValidAt`, which requires
`den ≠ 0`; raw evaluation remains total because division in `ℝ` is total.
-/
inductive Expr (ι : Type*) where
  /-- A nonnegative integer literal. -/
  | nat (n : Nat)
  /-- An integer literal. -/
  | int (n : Int)
  /-- A rational literal with an integer numerator and natural denominator. -/
  | rat (num : Int) (den : Nat)
  /-- The circle constant `π`. -/
  | pi
  /-- Euler's number `e = exp 1`. -/
  | e
  /-- A variable identified by an index in `ι`. -/
  | var (name : ι)
  /-- The sum of two expressions. -/
  | add (a b : Expr ι)
  /-- The product of two expressions. -/
  | mul (a b : Expr ι)
  /-- The difference of two expressions. -/
  | sub (a b : Expr ι)
  /-- The quotient of two expressions. -/
  | div (a b : Expr ι)
  /-- The additive inverse of an expression. -/
  | neg (a : Expr ι)
  /-- A natural-number power. -/
  | pow (a : Expr ι) (n : Nat)
  /-- The sine of an expression. -/
  | sin (a : Expr ι)
  /-- The cosine of an expression. -/
  | cos (a : Expr ι)
  /-- The real inverse tangent of an expression. -/
  | atan (a : Expr ι)
  /-- The principal real inverse sine of an expression. -/
  | asin (a : Expr ι)
  /-- The principal real inverse cosine of an expression. -/
  | acos (a : Expr ι)
  /-- The real exponential of an expression. -/
  | exp (a : Expr ι)
  /-- The real logarithm of an expression. -/
  | log (a : Expr ι)
  /-- The nonnegative real square root of an expression. -/
  | sqrt (a : Expr ι)
  /-- A real power `a ^ b` in the sense of `Real.rpow`; `ValidAt` asks for a positive base. -/
  | rpow (a b : Expr ι)
deriving BEq, DecidableEq

/-- `Inhabited` for symbolic expressions, with the default `.nat 0`. -/
instance {ι : Type*} : Inhabited (Expr ι) := ⟨.nat 0⟩

namespace Expr

/-! ## Evaluation and semantic validity -/

/-- Evaluate a symbolic expression in an environment `ι → ℝ`. -/
@[simp] noncomputable def eval {ι : Type*} (ρ : ι → ℝ) : Expr ι → ℝ
  | nat n => n
  | int n => n
  | rat num den => (num : ℝ) / (den : ℝ)
  | pi => Real.pi
  | e => Real.exp 1
  | var name => ρ name
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b
  | sub a b => eval ρ a - eval ρ b
  | div a b => eval ρ a / eval ρ b
  | neg a => -(eval ρ a)
  | pow a n => (eval ρ a) ^ n
  | sin a => Real.sin (eval ρ a)
  | cos a => Real.cos (eval ρ a)
  | atan a => Real.arctan (eval ρ a)
  | asin a => Real.arcsin (eval ρ a)
  | acos a => Real.arccos (eval ρ a)
  | exp a => Real.exp (eval ρ a)
  | log a => Real.log (eval ρ a)
  | sqrt a => Real.sqrt (eval ρ a)
  | rpow a b => eval ρ a ^ eval ρ b

/-- Side conditions needed to justify the classical analytic derivative rules.

Rational literals carry a natural-number denominator in the AST, so validity rules out `den = 0`
there just as it rules out zero denominators for expression-level division.

For `log`, validity excludes zero, matching Mathlib's derivative theorem for the total real
logarithm on both connected components of `ℝ \ {0}`. For `sqrt`, validity requires a strictly
positive argument. This is stronger than what Mathlib's `Real.hasDerivAt_sqrt`
needs (`x ≠ 0`, since `Real.sqrt` is constant on `(-∞, 0]`): it certifies the classical
square-root branch rather than the totalized function, so a goal that is Lean-true only because
of the extension to negative arguments is rejected by the reflective route. Lean's total
`Real.log`/`Real.sqrt` have values outside those analytic domains, but these symbolic derivative
rules certify classical differentiability. Raw `Expr.eval` itself is total and does not require
`ValidAt`.

For `rpow a b`, validity requires a strictly positive base `0 < a`, the hypothesis of Mathlib's
`HasFDerivAt.rpow`; Lean's total `Real.rpow` has values for nonpositive bases that the classical
power rule does not certify.

For `asin` and `acos`, validity excludes the two endpoints `-1` and `1`, matching Mathlib's
derivative theorems for the total real inverse trigonometric functions. Arguments outside
`[-1, 1]` are allowed: there the functions are locally constant and their derivatives are zero.
Unlike `sqrt` and `rpow`, these cases do not restrict evaluation to the classical branch. -/
@[simp] def ValidAt {ι : Type*} (ρ : ι → ℝ) : Expr ι → Prop
  | nat _ | int _ | pi | e | var _ => True
  | rat _ den => den ≠ 0
  | add a b | mul a b | sub a b => ValidAt ρ a ∧ ValidAt ρ b
  | div a b => ValidAt ρ a ∧ ValidAt ρ b ∧ eval ρ b ≠ 0
  | neg a => ValidAt ρ a
  | pow a _ => ValidAt ρ a
  | sin a | cos a | atan a | exp a => ValidAt ρ a
  | asin a | acos a => ValidAt ρ a ∧ eval ρ a ≠ -1 ∧ eval ρ a ≠ 1
  | log a => ValidAt ρ a ∧ eval ρ a ≠ 0
  | sqrt a => ValidAt ρ a ∧ 0 < eval ρ a
  | rpow a b => ValidAt ρ a ∧ ValidAt ρ b ∧ 0 < eval ρ a

/-! ## Symbolic validity requirements

`Expr.ValidAt` is the semantic predicate used by the verified differentiation theorems.
`ValidityRequirements` is its symbolic counterpart. It records the nonzero and
positivity obligations that must hold for the same expression. This lets later layers manipulate
side conditions as checked symbolic data before transporting them back to analytic hypotheses. -/
/-- Symbolic validity obligations for checked expressions.

`nonzero` tracks denominator and logarithm requirements such as `b ≠ 0`, while `positive` tracks
strict branch requirements such as `0 < a` for `sqrt a`. -/
structure ValidityRequirements (ι : Type*) where
  /-- Expressions required to evaluate to nonzero values. -/
  nonzero : List (Expr ι)
  /-- Expressions required to evaluate to strictly positive values. -/
  positive : List (Expr ι)
deriving DecidableEq

/-- Build the symbolic validity obligations needed by `Expr.ValidAt`. -/
def validityRequirements {ι : Type*} : Expr ι → ValidityRequirements ι
  | .nat _ | .int _ | .pi | .e | .var _ =>
      { nonzero := [], positive := [] }
  | .rat _ den =>
      { nonzero := [.nat den], positive := [] }
  | .add a b | .mul a b | .sub a b =>
      let ra := validityRequirements a
      let rb := validityRequirements b
      { nonzero := ra.nonzero ++ rb.nonzero
        positive := ra.positive ++ rb.positive }
  | .div a b =>
      let ra := validityRequirements a
      let rb := validityRequirements b
      { nonzero := ra.nonzero ++ rb.nonzero ++ [b]
        positive := ra.positive ++ rb.positive }
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .exp a =>
      validityRequirements a
  | .asin a | .acos a =>
      let ra := validityRequirements a
      { nonzero := ra.nonzero ++ [Expr.add a (Expr.nat 1), Expr.sub a (Expr.nat 1)]
        positive := ra.positive }
  | .log a =>
      let ra := validityRequirements a
      { nonzero := ra.nonzero ++ [a]
        positive := ra.positive }
  | .sqrt a =>
      let ra := validityRequirements a
      { nonzero := ra.nonzero
        positive := ra.positive ++ [a] }
  | .rpow a b =>
      let ra := validityRequirements a
      let rb := validityRequirements b
      { nonzero := ra.nonzero ++ rb.nonzero
        positive := ra.positive ++ rb.positive ++ [a] }

namespace ValidityRequirements

/-- Semantic interpretation of symbolic validity requirements. -/
def Holds {ι : Type*} (requirements : ValidityRequirements ι) (ρ : ι → ℝ) : Prop :=
  (∀ d ∈ requirements.nonzero, d.eval ρ ≠ 0) ∧
    ∀ d ∈ requirements.positive, 0 < d.eval ρ

/-- Defining equation interpreting the nonzero and positive symbolic requirements. -/
add_decl_doc Holds.eq_1

/-- Transport validity evidence across a computed equality of requirement collections. -/
theorem holds_of_eq {ι : Type*} {expected computed : ValidityRequirements ι}
    {ρ : ι → ℝ} (h : expected = computed) (hholds : computed.Holds ρ) :
    expected.Holds ρ := by
  simpa [h] using hholds

/-- If the symbolic requirements hold, then the checked expression is `ValidAt` the point. -/
theorem validAt_of_holds {ι : Type*} (ρ : ι → ℝ) :
    ∀ expr : Expr ι, (validityRequirements expr).Holds ρ → expr.ValidAt ρ := by
  intro expr
  induction expr with
  | nat | int | pi | e | var => exact fun _ ↦ trivial
  | neg a ih | pow a _ ih | sin a ih | cos a ih | atan a ih | exp a ih => exact ih
  | rat _ den => exact fun h ↦ by simpa using h.1 (.nat den) (by simp [validityRequirements])
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb =>
    rintro ⟨hz, hp⟩
    simp only [validityRequirements, List.forall_mem_append] at hz hp
    exact ⟨iha ⟨hz.1, hp.1⟩, ihb ⟨hz.2, hp.2⟩⟩
  | div a b iha ihb =>
    rintro ⟨hz, hp⟩
    simp only [validityRequirements, List.forall_mem_append, List.forall_mem_singleton] at hz hp
    exact ⟨iha ⟨hz.1.1, hp.1⟩, ihb ⟨hz.1.2, hp.2⟩, hz.2⟩
  | rpow a b iha ihb =>
    rintro ⟨hz, hp⟩
    simp only [validityRequirements, List.forall_mem_append, List.forall_mem_singleton] at hz hp
    exact ⟨iha ⟨hz.1, hp.1.1⟩, ihb ⟨hz.2, hp.1.2⟩, hp.2⟩
  | sqrt a ih =>
    rintro ⟨hz, hp⟩
    simp only [validityRequirements, List.forall_mem_append, List.forall_mem_singleton] at hp
    exact ⟨ih ⟨hz, hp.1⟩, hp.2⟩
  | asin a ih | acos a ih | log a ih =>
    rintro ⟨hz, hp⟩
    simp only [validityRequirements, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, eval, Nat.cast_one, ne_eq,
      add_eq_zero_iff_eq_neg, sub_eq_zero] at hz
    exact ⟨ih ⟨hz.1, hp⟩, hz.2⟩

end ValidityRequirements

/-! ## Symbolic differentiation

`Expr.diff` only constructs an expression. Analytic correctness is proved elsewhere by
theorems relating its evaluation to derivatives under `Expr.ValidAt`.
-/
/-- Symbolic differentiation with respect to a variable `v`. -/
@[simp] def diff {ι : Type*} [DecidableEq ι] (v : ι) : Expr ι → Expr ι
  | nat _ | int _ | rat _ _ | pi | e => .nat 0
  | var name => if name = v then .nat 1 else .nat 0
  | add a b => .add (diff v a) (diff v b)
  | mul a b => .add (.mul (diff v a) b) (.mul a (diff v b))
  | sub a b => .sub (diff v a) (diff v b)
  | div a b => .div (.sub (.mul (diff v a) b) (.mul a (diff v b))) (.pow b 2)
  | neg a => .neg (diff v a)
  | pow a n => .mul (.mul (.nat n) (.pow a (n - 1))) (diff v a)
  | sin a => .mul (.cos a) (diff v a)
  | cos a => .mul (.neg (.sin a)) (diff v a)
  | atan a => .div (diff v a) (.add (.nat 1) (.pow a 2))
  | asin a => .div (diff v a) (.sqrt (.sub (.nat 1) (.pow a 2)))
  | acos a => .neg (.div (diff v a) (.sqrt (.sub (.nat 1) (.pow a 2))))
  | exp a => .mul (.exp a) (diff v a)
  | log a => .div (diff v a) a
  | sqrt a => .div (diff v a) (.mul (.nat 2) (.sqrt a))
  | rpow a b =>
      .add (.mul (.mul (diff v a) b) (.rpow a (.sub b (.nat 1))))
        (.mul (.mul (diff v b) (.rpow a b)) (.log a))

/-! ## Structural operations -/

/-- Fold a list into a left-associated addition, with `0` as the neutral element. -/
def addList {ι : Type*} : List (Expr ι) → Expr ι
  | [] => .nat 0
  | hd :: tl => tl.foldl Expr.add hd

/-- The left-associated sum `addList xs` evaluates to the sum of the values of `xs`. -/
@[simp] theorem eval_addList {ι : Type*} (ρ : ι → ℝ) (xs : List (Expr ι)) :
    (addList xs).eval ρ = (xs.map (fun expr ↦ expr.eval ρ)).sum := by
  cases xs with
  | nil => simp [addList]
  | cons hd tl =>
    simp only [addList, List.map_cons, List.sum_cons]
    induction tl generalizing hd with
    | nil => simp
    | cons x xs ih => simpa [add_assoc] using ih (Expr.add hd x)

/-- The left-associated sum of the list `[f 0, …, f (n - 1)]` evaluates to the finite sum of the
values of `f`. -/
theorem eval_addList_ofFn {ι : Type*} {n : ℕ} (ρ : ι → ℝ) (f : Fin n → Expr ι) :
    (addList (List.ofFn f)).eval ρ = ∑ i, (f i).eval ρ := by
  rw [eval_addList, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Fold a list into a left-associated multiplication, with `1` as the neutral element. -/
def mulList {ι : Type*} : List (Expr ι) → Expr ι
  | [] => .nat 1
  | hd :: tl => tl.foldl Expr.mul hd

/-- A left-associated raw product evaluates to the product of the factor values. -/
@[simp] theorem eval_mulList {ι : Type*} (ρ : ι → ℝ) :
    ∀ factors : List (Expr ι),
      (mulList factors).eval ρ = (factors.map fun factor ↦ factor.eval ρ).prod
  | [] => by simp [mulList]
  | hd :: tl => by
      simp only [mulList, List.map_cons, List.prod_cons]
      induction tl generalizing hd with
      | nil => simp
      | cons x xs ih =>
          simpa [List.foldl_cons, List.map_cons, List.prod_cons, mul_assoc] using
            ih (Expr.mul hd x)

/-- Syntactic check for whether an expression mentions a variable. -/
@[simp] def containsVar {ι : Type*} [DecidableEq ι] (v : ι) : Expr ι → Bool
  | .nat _ | .int _ | .rat _ _ | .pi | .e => false
  | .var name => name = v
  | .add a b | .mul a b | .sub a b | .div a b =>
      containsVar v a || containsVar v b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      containsVar v a
  | .rpow a b => containsVar v a || containsVar v b

/-- An expression that does not syntactically mention `v` has a value independent of the
assignment to `v`. This is the semantic content of `containsVar`: the symbolic procedures may treat
such an expression as a constant when differentiating or integrating in `v`. -/
theorem eval_eq_eval_update_of_not_containsVar {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (v : ι) (expr : Expr ι)
    (h : containsVar v expr = false) (t : ℝ) :
    expr.eval (Function.update ρ v t) = expr.eval ρ := by
  induction expr <;> simp_all [containsVar, eval]

end Expr

end CAS.Verified
