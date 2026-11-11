/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.PolynomialAlgebra
public import CAS.Command.Gamma
public import CAS.Command.LinearAlgebra.Eigen
public import CAS.Command.NumberTheory.Modular
public import CAS.Command.Product
public import CAS.NumberTheory.Jacobi
public meta import CAS.NumberTheory.Jacobi
public meta import CAS.Tactic.CommandShapes
public meta import CAS.Tactic.Classify
public meta import CAS.Tactic.KernelReadBack

/-!
# Closing goals with the algebra, matrix and number theory commands

The `command` route of bare `cas` (`CAS.Command.Goals`) hands the goals that
`CAS.Tactic.CommandShapes.isAlgebraStatement` recognizes to `close`, which reads the goal's own
terms, computes as the corresponding `#cas` command does, and builds the same proof against the
goal:

* in `ℚ[X]`: `gcd p q = g`, `lcm p q = l`, `p / q = s`, `p % q = r`, `p.coeff k = c`,
  `p.natDegree = d`, with `p`, `q` written with `X`, `C`, numerals and ring operations;
* for literal matrices over `ℚ`: `A⁻¹ = B` (from `B * A = 1`), `A.rank = r`, `A.charpoly = p`,
  and equations between literal matrix expressions (transposes, traces, powers, products), decided
  by kernel evaluation;
* for natural numbers: `a ^ b % m = r` (repeated squaring, whose cost grows with the number of
  digits of the exponent); the primality goals `Nat.Prime n` are Hex's (`CASHex.Algebra`);
* `a⁻¹ = b` in `ZMod m` for a unit `a`, from `a * b = 1` evaluated by the kernel, and
  `jacobiSym a n = j` for odd `n`, by one run of the reciprocity loop in the kernel, as
  `#cas (modularInverse a m)` and `#cas (jacobiSymbol a n)` prove them;
* finite sums and products `∑ k ∈ Finset.range n, f k = F n` and `∏ k ∈ Finset.Icc 1 n, f k = F n`
  (also under `∀ n`), by induction on `n`;
* `Real.Gamma q = v` at integers and half-integers, as `#cas (gamma q)` proves it.

## Implementation notes

The proofs are those of the commands, applied to the goal's own terms: `Algebra.gcdProof`,
`Algebra.lcmProof` and `Algebra.divisionProof` of `CAS/Command/Algebra/PolynomialAlgebra.lean`,
`LinearAlgebra.rankScript` of `CAS/Command/LinearAlgebra/RowReduce.lean`,
`LinearAlgebra.charpolyTactic` of `CAS/Command/LinearAlgebra/Eigen.lean`,
`NumberTheory.powModProof` of `CAS/Command/NumberTheory/Basic.lean` (Mathlib's `evalNatPowMod`)
through `CAS.NumberTheory.pow_mod_eq_of_eq`, `CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop` of
`CAS/NumberTheory/Jacobi.lean`, and `Gamma.value?` and `Gamma.factScript` of
`CAS/Command/Gamma.lean`. We read a coefficient or a degree after rewriting `p` to its expanded
form by `polynomialIdentityTactic`, and we build the induction for sums and products here.

We compute the value before we prove anything: a goal that states another gcd, lcm, coefficient,
degree, inverse, rank, modular power or Jacobi symbol is refused with the computed value
(`refute`), and bare `cas` then tries no other route. Each proof is an ordinary term, and the
caller of the route validates the proof assigned to the goal
(`ProofCarrier.attemptClosingMainGoal`); nothing computed here is trusted.
-/

public meta section

namespace CAS.Command.AlgebraGoals

open Lean Elab Lean.Elab.Tactic Meta
open CAS.Command.Algebra (Dense qPolyTerm polynomialIdentityTactic natTerm)
open CAS.Command.LinearAlgebra (QMatrix)
open CAS.Command.NumberTheory (raw)
open CAS.Tactic.CommandShapes (isAlgebraSide)

/-! ## Reading the goal -/

/-- A polynomial of `ℚ[X]` written with `X`, `C q`, numerals, `+`, `-`, `*`, `^` (numeral
exponents) and negation. -/
partial def qPolynomial? (e : Expr) : MetaM (Option Dense) := do
  let e := e.consumeMData
  if e.isAppOf ``Polynomial.X then return some #[0, 1]
  if e.isAppOfArity ``Polynomial.C 3 || (e.isAppOfArity ``DFunLike.coe 6 &&
      (e.getArg! 4).getAppFn.consumeMData.isConstOf ``Polynomial.C) then
    let some q ← Tactic.Classify.rationalLiteral? e.appArg! | return none
    return some (Dense.trim #[q])
  if let some n := e.nat? then return some (Dense.trim #[(n : ℚ)])
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => return Dense.add <$> (← qPolynomial? a) <*> (← qPolynomial? b)
  | HSub.hSub _ _ _ _ a b => return Dense.sub <$> (← qPolynomial? a) <*> (← qPolynomial? b)
  | HMul.hMul _ _ _ _ a b => return Dense.mul <$> (← qPolynomial? a) <*> (← qPolynomial? b)
  | Neg.neg _ _ a => return (Dense.scale (-1)) <$> (← qPolynomial? a)
  | HPow.hPow _ _ _ _ a k =>
      let some k := k.consumeMData.nat? | return none
      return (fun p ↦ Dense.pow p k) <$> (← qPolynomial? a)
  | _ => return none

/-- Whether `type` is `Polynomial ℚ`. -/
def isRatPolynomial (type : Expr) : MetaM Bool := do
  let type ← whnfR type
  unless type.isAppOfArity ``Polynomial 2 do return false
  isDefEq type.appFn!.appArg! (mkConst ``Rat)

/-- The entries of a vector literal `![a, b, …]`. -/
partial def vectorEntries? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  if e.isAppOf ``Matrix.vecEmpty then some []
  else if e.isAppOfArity ``Matrix.vecCons 4 then
    (vectorEntries? e.appArg!).map (e.getArg! 2 :: ·)
  else none

/-- A matrix literal `!![…]` over `ℚ` as rows of rationals. -/
def matrixLiteral? (e : Expr) : MetaM (Option QMatrix) := do
  let e := e.consumeMData
  -- `Matrix.of v` is a coercion of the equivalence `Matrix.of` applied to `v`.
  let v := if e.isAppOfArity ``DFunLike.coe 6 then e.appArg! else e
  let some rows := vectorEntries? v | return none
  let mut out : QMatrix := #[]
  for row in rows do
    let some entries := vectorEntries? row | return none
    let mut values : Array ℚ := #[]
    for entry in entries do
      let some q ← Tactic.Classify.rationalLiteral? entry | return none
      values := values.push q
    out := out.push values
  if out.isEmpty || !(out.all (·.size == out[0]!.size)) then return none
  return some out

/-- The value of a closed natural-number term built from numerals with `+`, `-`, `*`, `/`, `%`
and `^` (powers below `2 ^ 100000`). -/
partial def natValue? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let binary (a b : Expr) (f : Nat → Nat → Option Nat) : MetaM (Option Nat) := do
    let (some x, some y) := (← natValue? a, ← natValue? b) | return none
    return f x y
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => binary a b fun x y ↦ some (x + y)
  | HSub.hSub _ _ _ _ a b => binary a b fun x y ↦ some (x - y)
  | HMul.hMul _ _ _ _ a b => binary a b fun x y ↦ some (x * y)
  | HDiv.hDiv _ _ _ _ a b => binary a b fun x y ↦ some (x / y)
  | HMod.hMod _ _ _ _ a b => binary a b fun x y ↦ some (x % y)
  | HPow.hPow _ _ _ _ a b => binary a b fun x y ↦
      if x ≤ 1 || y * (Nat.log2 x + 1) < 100000 then some (x ^ y) else none
  | _ => return none

/-- The value of an integer literal of any type: a numeral, a negation, or the cast of an integer
literal or of a closed natural-number term as `natValue?` reads it. -/
partial def intLiteral? (e : Expr) : MetaM (Option Int) := do
  let e := e.consumeMData
  if let some n := e.nat? then return some n
  match_expr e with
  | Neg.neg _ _ a => return (← intLiteral? a).map (- ·)
  | Int.cast _ _ a => intLiteral? a
  | IntCast.intCast _ _ a => intLiteral? a
  | Nat.cast _ _ a => return (← natValue? a).map fun n ↦ (n : Int)
  | NatCast.natCast _ _ a => return (← natValue? a).map fun n ↦ (n : Int)
  | _ => return none

/-! ## Closing -/

/-- Refuse a goal of the algebra fragment whose stated value differs from the computed one; bare
`cas` reports this error and tries no other route (`CAS.Tactic.CommandShapes.refutedTag`). -/
def refute {α : Type} (message : MessageData) : TacticM α := do
  throw (.error (← getRef) (.tagged CAS.Tactic.CommandShapes.refutedTag message))

/-- Run `tactic` on the main goal, which it must close. -/
def closeWith (description : String) (tactic : TSyntax `tactic) : TacticM Unit := do
  let goal ← getMainGoal
  let remaining ←
    try
      CAS.Tactic.KernelReadBack.withSuppressedMessagesMeta <|
        CAS.Tactic.KernelReadBack.runTacticOnGoal goal tactic
    catch error => throwError "cas {description}: {error.toMessageData}"
  unless remaining.isEmpty do throwError "cas {description}: goals remain"
  replaceMainGoal []

/-- Close the main goal with a proof term. -/
def closeWithTerm (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  unless ← isDefEq (← goal.getType) (← inferType proof) do
    throwError "cas: internal error: the proof does not have the goal's type"
  goal.assign proof
  replaceMainGoal []

/-- Polynomial goals in `ℚ[X]`. -/
def closePolynomial (lhs rhs : Expr) : TacticM Bool := do
  let identity ← polynomialIdentityTactic
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``GCDMonoid.gcd 5 || lhs.isAppOfArity ``GCDMonoid.lcm 5 then
    let P := lhs.getArg! 3
    let Q := lhs.getArg! 4
    unless ← isRatPolynomial (← inferType P) do return false
    let (some p, some q) := (← qPolynomial? P, ← qPolynomial? Q) | return false
    let PT ← Term.exprToSyntax P
    let QT ← Term.exprToSyntax Q
    let isGcd := lhs.isAppOfArity ``GCDMonoid.gcd 5
    if isGcd && Dense.isZero p && Dense.isZero q then return false
    if !isGcd && (Dense.isZero p || Dense.isZero q) then return false
    let (value, G, script) ← if isGcd then Algebra.gcdProof PT QT p q
      else Algebra.lcmProof PT QT p q
    if let some stated ← qPolynomial? rhs then
      unless Dense.trim stated == Dense.trim value do
        refute m!"cas: the {if isGcd then "gcd" else "lcm"} is \
          {Algebra.denseText "X" value}, not {Algebra.denseText "X" stated}"
    let statement ← if isGcd then `(gcd $PT $QT = $G) else `(lcm $PT $QT = $G)
    closeWith "polynomial gcd" (← `(tactic| (
      have h : $statement := by $script:tactic
      exact h.trans (by $identity:tactic))))
    return true
  if lhs.isAppOfArity ``HDiv.hDiv 6 || lhs.isAppOfArity ``HMod.hMod 6 then
    let P := lhs.getArg! 4
    let Q := lhs.getArg! 5
    unless ← isRatPolynomial (← inferType P) do return false
    let (some p, some q) := (← qPolynomial? P, ← qPolynomial? Q) | return false
    if Dense.isZero q then return false
    let PT ← Term.exprToSyntax P
    let QT ← Term.exprToSyntax Q
    let (_, _, S, R, script) ← Algebra.divisionProof PT QT p q
    let part ← if lhs.isAppOfArity ``HDiv.hDiv 6 then `(term| h.1) else `(term| h.2)
    closeWith "polynomial division" (← `(tactic| (
      have h : $PT / $QT = $S ∧ $PT % $QT = $R := by $script:tactic
      exact ($part).trans (by $identity:tactic))))
    return true
  let isCoeff := CAS.Tactic.CommandShapes.isPolynomialCoeff lhs
  if isCoeff || lhs.isAppOfArity ``Polynomial.natDegree 3 then
    let P := if isCoeff then (lhs.getArg! 4).consumeMData.appArg! else lhs.getArg! 2
    unless ← isRatPolynomial (← inferType P) do return false
    let some p ← qPolynomial? P | return false
    let p := Dense.trim p
    if isCoeff then
      if let (some k, some stated) := (← natValue? lhs.appArg!,
          ← Tactic.Classify.rationalLiteral? rhs) then
        let value := p.getD k 0
        unless value = stated do refute m!"cas: the coefficient is {value}, not {stated}"
    else if let some stated ← natValue? rhs then
      let value := p.size - 1
      unless value = stated do refute m!"cas: the degree is {value}, not {stated}"
    let PT ← Term.exprToSyntax P
    let E ← Algebra.expandedPolynomialTerm (n := 1) (fun _ ↦ ⟨mkIdent `X⟩) false 0
      (Algebra.ofDense (0 : Fin 1) p)
    let rewrite ← `(tactic| rw [show $PT = $E by $identity:tactic])
    let finish ← if isCoeff then
        `(tactic| first
          | (simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_zero]; norm_num)
          | simp)
      else `(tactic| compute_degree!)
    closeWith "polynomial coefficient" (← `(tactic| ($rewrite:tactic; $finish:tactic)))
    return true
  return false

/-- Matrix goals over `ℚ`. -/
def closeMatrix (lhs rhs : Expr) : TacticM Bool := do
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Inv.inv 3 then
    let some A ← matrixLiteral? lhs.appArg! | return false
    let some B ← matrixLiteral? rhs | return false
    unless A.rows = A.cols do return false
    let some inverse := A.inverse?
      | if B.all (·.all (· == 0)) then return false
        else refute m!"cas: the matrix is singular; Mathlib's inverse of it is 0"
    unless inverse == B do refute m!"cas: the inverse is {inverse.text}, not {B.text}"
    closeWith "matrix inverse" (← `(tactic| exact Matrix.inv_eq_left_inv (by decide +kernel)))
    return true
  if lhs.isAppOfArity ``Matrix.rank 6 then
    let At := lhs.appArg!
    let some A ← matrixLiteral? At | return false
    let some stated ← natValue? rhs | return false
    let (r, script) ← LinearAlgebra.rankScript A (← Term.exprToSyntax At)
    unless r = stated do refute m!"cas: the rank is {r}, not {stated}"
    closeWith "matrix rank" script
    return true
  if lhs.isAppOf ``Matrix.charpoly then
    let At := lhs.appArg!
    let some A ← matrixLiteral? At | return false
    unless A.rows = A.cols do return false
    closeWith "characteristic polynomial"
      (← LinearAlgebra.charpolyTactic A (some (← Term.exprToSyntax At)))
    return true
  return false

/-- `a ^ b % m = r` for natural numbers, by repeated squaring; `a⁻¹ = b` in `ZMod m` for a unit
`a`, by `ZMod.inv_eq_of_mul_eq_one` with `a * b = 1` decided by the kernel; and `jacobiSym a n = j`
for odd `n`, by `CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop`. (The primality goals
`Nat.Prime n` are Hex's: the route `hex` of `CASHex.Algebra` takes them.) -/
def closeNumber (target : Expr) : TacticM Bool := do
  let target := target.consumeMData
  let some (_, lhs, rhs) := target.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Inv.inv 3 && (lhs.getArg! 0).consumeMData.isAppOfArity ``ZMod 1 then
    let (some m, some a, some b) := (← natValue? (lhs.getArg! 0).consumeMData.appArg!,
        ← intLiteral? lhs.appArg!, ← intLiteral? rhs)
      | return false
    let (g, s, _) := NumberTheory.extendedGcd (a % m).toNat m
    -- Mathlib's inverse of a non-unit is not `0` in general; such goals are left to other routes.
    if m < 2 ∨ g ≠ 1 then return false
    let r := (s % m).toNat
    unless (b % m).toNat = r do refute m!"cas: the inverse of {a} modulo {m} is {r}, not {b}"
    closeWith "modular inverse"
      (← `(tactic| exact ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide +kernel)))
    return true
  if lhs.isAppOfArity ``jacobiSym 2 then
    let (some a, some n, some stated) := (← intLiteral? (lhs.getArg! 0),
        ← natValue? (lhs.getArg! 1), ← intLiteral? rhs)
      | return false
    unless n % 2 = 1 do return false
    -- The fuel `2 (log₂ (a % n) + log₂ n) + 4` is more than the loop uses, as for the call.
    let residue := (a % n).toNat
    let fuel := 2 * (Nat.log2 residue + Nat.log2 n) + 4
    let some j := CAS.NumberTheory.Jacobi.loop fuel residue n | return false
    unless j = stated do refute m!"cas: the Jacobi symbol ({a} / {n}) is {j}, not {stated}"
    closeWith "Jacobi symbol" (← `(tactic|
      exact CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop $(natTerm fuel) (by decide +kernel)
        (by decide +kernel)))
    return true
  if CAS.Tactic.CommandShapes.isModularPower lhs && (← isDefEq (← inferType lhs) (mkConst ``Nat))
      then
    let power := (lhs.getArg! 4).consumeMData
    let (some a, some b, some m, some r) := (← natValue? (power.getArg! 4),
        ← natValue? (power.getArg! 5), ← natValue? (lhs.getArg! 5), ← natValue? rhs)
      | return false
    if m = 0 then return false
    let (value, proof) := NumberTheory.powModProof a b m
    unless value = r do refute m!"cas: {a} ^ {b} % {m} is {value}, not {r}"
    let term := mkAppN (mkConst ``CAS.NumberTheory.pow_mod_eq_of_eq)
      #[power.getArg! 4, power.getArg! 5, lhs.getArg! 5, rhs, raw a, raw b, raw m, raw r,
        ← mkEqRefl (raw a), ← mkEqRefl (raw b), ← mkEqRefl (raw m), ← mkEqRefl (raw r), proof]
    closeWithTerm term
    return true
  return false

/-- Finite sums and products of `Finset.range n` or `Finset.Icc a n`, `a ≤ 1`, by induction on a
variable upper bound `n`. -/
def closeSumOrProduct (target : Expr) : TacticM Bool := do
  let target := target.consumeMData
  let (quantified, body) := match target with
    | .forallE _ _ body _ => (true, body)
    | _ => (false, target)
  let some (_, lhs, _) := body.eq? | return false
  let lhs := lhs.consumeMData
  unless lhs.isAppOfArity ``Finset.sum 5 || lhs.isAppOfArity ``Finset.prod 5 do return false
  let set := (lhs.getArg! 3).consumeMData
  let isRange := set.isAppOfArity ``Finset.range 1
  let isIcc := set.isAppOfArity ``Finset.Icc 5
  unless isRange || isIcc do return false
  let n := mkIdent `n
  let m := mkIdent `m
  let ih := mkIdent `ih
  -- The bound is `n` or `n + c` for a numeral `c`, where `n` is the quantified variable or a
  -- local variable, on which the induction runs.
  let bound := set.appArg!.consumeMData
  let base := match_expr bound with
    | HAdd.hAdd _ _ _ _ a c => if c.nat?.isSome then a.consumeMData else bound
    | _ => bound
  let intro ← if quantified then
      unless base == mkBVar 0 do return false
      `(tactic| intro $n:ident)
    else match base with
      | .fvar id => do
          let name := (← id.getDecl).userName
          `(tactic| (revert $(mkIdent name):ident; intro $n:ident))
      | _ => return false
  let isSum := lhs.isAppOfArity ``Finset.sum 5
  let stepLemma ← if isSum then
      (if isRange then `(Lean.Parser.Tactic.rwRule| Finset.sum_range_succ)
        else `(Lean.Parser.Tactic.rwRule| Finset.sum_Icc_succ_top (by omega)))
    else
      (if isRange then `(Lean.Parser.Tactic.rwRule| Finset.prod_range_succ)
        else `(Lean.Parser.Tactic.rwRule| Finset.prod_Icc_succ_top (by omega)))
  closeWith "finite sum or product by induction" (← `(tactic| (
    $intro:tactic
    induction $n:ident with
    | zero => first | simp | norm_num [Finset.Icc_self] | rfl
    | succ $m:ident $ih:ident =>
        rw [$stepLemma, $ih:ident]
        (try simp only [Nat.factorial_succ])
        push_cast
        first | ring1 | (field_simp; done) | (field_simp; ring1))))
  return true

/-- `Real.Gamma q = v` at an integer or half-integer `q`, with the value in any form that `ring`,
`norm_num` or `linarith` identifies with the computed `v` or `v * √π`. -/
def closeGamma (lhs : Expr) : TacticM Bool := do
  let lhs := lhs.consumeMData
  unless lhs.isAppOfArity ``Real.Gamma 1 do return false
  let some q ← Tactic.Classify.rationalLiteral? lhs.appArg! | return false
  let fact := mkIdent `hΓ
  let pole := q.den = 1 && q ≤ 0
  let (value, script) ← if pole then
      let n : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
      pure ("0", ← `(tactic|
        (have $fact:ident := Real.Gamma_neg_nat_eq_zero $n; norm_num at $fact:ident)))
    else
      let some (v, radical) := Gamma.value? q | return false
      let some script ← Gamma.factScript q fact | return false
      pure (Gamma.valueText v radical, script)
  try
    closeWith "Gamma value" (← `(tactic| (
      $script:tactic
      first
        | exact $fact:ident
        | (rw [$fact:ident]; ring1)
        | (rw [$fact:ident]; norm_num)
        | linarith [$fact:ident])))
  catch _ =>
    throwError "cas: Γ({q}) is {value}{if pole then " in Mathlib (a pole)" else ""}; the stated \
      value is not identified with it"
  return true

/-- Close a goal of the algebra fragment with its computed side on the left. -/
def closeOriented : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  if ← closeNumber target then return
  if ← closeSumOrProduct target then return
  let some (_, lhs, rhs) := target.eq? | throwError "cas: no algebra command states this goal"
  if ← closePolynomial lhs rhs then return
  if ← closeMatrix lhs rhs then return
  if ← closeGamma lhs then return
  -- Other equations between closed matrix expressions over `ℚ`.
  let type ← inferType lhs
  if !target.hasFVar && !target.hasMVar && (type.isAppOf ``Matrix ||
      (← whnfR type).isForall) then
    closeWith "matrix equation" (← `(tactic| decide +kernel))
    return
  throwError "cas: no algebra command states this goal"

/-- Close a goal recognized by `CAS.Tactic.CommandShapes.isAlgebraStatement`; an equation stated
with the computed side on the right is reversed first. -/
def close : TacticM Unit := do
  let target ← withMainContext do return (← instantiateMVars (← getMainTarget)).consumeMData
  if let some (_, lhs, rhs) := target.eq? then
    if !isAlgebraSide lhs && isAlgebraSide rhs then
      let reversed ← withMainContext do
        (← getMainGoal).apply (← mkAppOptM ``Eq.symm #[none, some rhs, some lhs])
      let [goal] := reversed | throwError "cas: could not reverse the equation"
      replaceMainGoal [goal]
  closeOriented

end CAS.Command.AlgebraGoals
