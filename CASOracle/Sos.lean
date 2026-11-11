/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS
import Mathlib.Tactic.Positivity
import CASOracle.Accept
import CASOracle.Translate

/-!
# Sums of squares

`cas [oracle := o]` on `0 ≤ p`, `a ≤ b` or `a ≥ b` between polynomials, possibly under `∀`
binders and premises, asks the oracle for a certificate `p = ∑ dᵢ * ℓᵢ ^ 2 * ∏ gⱼ`: the `dᵢ` are
positive rational numbers, the `ℓᵢ` polynomials, and the `gⱼ` come from hypotheses `0 ≤ gⱼ` (or
`a ≤ b`, read as `0 ≤ b - a`) in context. The polynomials are polynomials over atoms: a subterm
that is not a sum, difference, product, negation, numeral, power with a literal natural exponent
at most 1000 or division by a nonzero numeral, such as `Real.sin x`, counts as a variable. The
oracle finds a positive semidefinite Gram matrix numerically with cvxpy and rounds it to exact
rationals. Lean checks the identity with `ring` and the sign of each term with `positivity` by
running, as printed, the script that the tactic then suggests, which no longer needs the oracle:

```
intro x y hx hy
rw [ge_iff_le, ← sub_nonneg, show b - a = S by ring]
positivity
```

On `0 < p`, `a < b` or `a > b` the sum must also have a positive term: a positive constant, or a
positive constant times hypotheses `0 < hⱼ` (or `a < b`), a factor possibly repeated. The oracle
looks for such a sum equal to `p` first. When it finds none, it looks for a multiplier `M`, a sum
of squares (times hypotheses) of degree at most 2 and then at most 4, such that `M * p` is one:

```
intro x y
refine pos_of_mul_pos_right (a := M) ?_ (by positivity)
rw [show M * p = S by ring]
positivity
```

This is how `0 < (x * y - 1) ^ 2 + x ^ 2` is proved. Without premises the positive term of a sum
equal to `p` is a constant `c > 0`, and this `p` takes values below every such `c`, at `x = 1 / y`
for large `y`, so no such sum equals `p`; but `(1 + y ^ 2) * p = 1 + (x - y + x * y ^ 2) ^ 2`.

`#cas [sos x, y, oracle := o] p` states and proves `∀ x y : ℝ, 0 ≤ p` (or `∀ x y : ℝ, p` when `p`
is an inequality, strict or not) and prints the certificate, with an `example` of the statement
proved by the script. A refusal of the oracle says nothing about the inequality: a nonnegative
polynomial such as Motzkin's need not be a sum of squares, and a positive one need not have a
certificate of the degrees tried.

## Implementation notes

We let `positivity` judge the sign in every form. A sum of nonnegative terms with one positive
term is positive, and `positivity` finds the hypotheses `0 < hⱼ` in context, so the strict goals
need no lemma of ours; with a multiplier, Mathlib's `pos_of_mul_pos_right` turns `0 < M * p` and
`0 ≤ M` into `0 < p`. `positivity` runs in the goal's local context and may use any hypothesis
there, so the form of a strict certificate is ours to check: we refuse one in which no term is a
positive constant or a positive constant times strict premises.

None of the search below is trusted: the proof is the identity, checked by `ring`, and the
signs, checked by `positivity`. The search is Parrilo's Gram-matrix method. A product `g` of
hypotheses gets a block `Q`, and its terms are `zᵀ Q z * g` for a vector `z` of monomials, so a
certificate is a positive semidefinite `Q` for each block subject to linear conditions, the
coefficients of the identity. cvxpy solves this semidefinite program with CLARABEL, or with SCS
when CLARABEL gives no answer, maximizing the smallest eigenvalue `t ≤ 1` of the blocks.
For `0 ≤ p` without hypotheses `z` holds the monomials whose squares lie in the Newton polytope
of `p`, which suffices by Reznick's theorem (Theorem 3 of Peyrl and Parrilo). For `0 < p`
without hypotheses, the first search, for `p = S + c` with `c > 0`, uses the Newton polytope of
the support of `p` with the constant monomial added, which contains that of `p - c`. In the
other searches, with hypotheses or with a multiplier, `z` holds every monomial whose square
times `g` stays within the degree of the identity, and in a block of `M` within the degree
bound of `M`. The exact step is Peyrl and Parrilo's (their Section 3.1): we round each entry to
the closest fraction with a bounded denominator, for the bounds 1, 2, 3, 4, 6, ... up to
`10 ^ 8` in turn, correct the rounded point by its exact least-norm projection onto the linear
conditions, and accept it when an exact LDLᵀ factorization shows each block positive
semidefinite. Peyrl and Parrilo assume a positive definite solution. When no rounding is
accepted and a numerical block `Q` is singular, we round a basis of its numerical kernel, the
span of the eigenvectors whose eigenvalues are below `10⁻⁶ * max(1, maxᵢ |λᵢ|)`, to fractions
with denominators at most 1000. This rounded kernel is not checked to annihilate `Q` exactly:
we refuse unless each of its basis vectors `v` has
`‖Q v‖ ≤ 10⁻⁵ * max(1, maxᵢⱼ |Qᵢⱼ|) * max(1, ‖v‖)`, and since the search is not trusted, a wrong
kernel can lose a certificate but not give a false one. We then replace `z` by `Vᵀ z`, with `V`
a basis of the vectors orthogonal to the rounded kernel, and solve again, at most three times.
Peyrl and Parrilo read the Newton polytope, and the removal of known zeros of `p`, as a facial
reduction in the sense of Borwein and Wolkowicz; reading the face from the numerical kernel is
our own heuristic.

For a strict goal we add a `1 × 1` block for each positive term. Maximizing the smallest
eigenvalue favours a margin for these terms, but a rounding can still lose all of them; then
the next denominator is tried. With a multiplier the identity `M * p = S` is homogeneous, and
we fix its scale by asking the weights of the positive terms to add up to 1.

A script over the elaborated atoms and the script printed from their delaborated forms can
differ, so the goal is proved by the printed script itself: we print it on one line, parse that
line back and run it on the goal, in the goal's local context, and the same line is what the
tactic suggests and what `#cas` prints. When the run fails, for an atom printed as an
inaccessible name `x✝` for instance, the goal is proved from the same certificate over the
elaborated atoms, and the tactic suggests the call itself rather than a script. In `#cas` the
goal also holds the variables of the section, as implementation details, so that each name of
the script means what it means where the command is; they are not premises, `positivity` and
instance search skip them, and a proof that mentions one is refused. `#cas` prints the script in
an `example` of the statement only once `checkExample` has elaborated that `example` where the
command is to a declaration of the statement with no `sorry`. We check that the oracle has the
task before we ask it. Once it has been asked, every refusal, up to the kernel's check of the
proof, ends with the sentence that it says nothing about the inequality.

The search is bounded. The oracle is sent the first eight named hypotheses in context that are
inequalities between terms of the goal's type, counted before they are read as polynomials; the
other hypotheses are not sent, but `positivity` sees them. Each Gram matrix is over at most 40
monomials. A square multiplies a product of distinct hypotheses, with at most 64 such products
for the sum and the multiplier together. A positive term is a positive constant times a product
of strict hypotheses of positive degree, a hypothesis possibly repeated, with at most 32 such
products, the empty one included. Without hypotheses an odd degree is refused at once, since no
sum of squares has odd degree.

## References

* Pablo A. Parrilo, "Semidefinite programming relaxations for semialgebraic problems",
  *Mathematical Programming* 96 (2003), no. 2, pp. 293-320,
  <https://doi.org/10.1007/s10107-003-0387-5>.
* Helfried Peyrl and Pablo A. Parrilo, "Computing sum of squares decompositions with rational
  coefficients", *Theoretical Computer Science* 409 (2008), no. 2, pp. 269-281,
  <https://doi.org/10.1016/j.tcs.2008.09.025>.
* Bruce Reznick, "Extremal PSD forms with few terms", *Duke Mathematical Journal* 45 (1978),
  no. 2, pp. 363-374, <https://doi.org/10.1215/S0012-7094-78-04519-2>.
* Jon M. Borwein and Henry Wolkowicz, "Facial reduction for a cone-convex programming problem",
  *Journal of the Australian Mathematical Society, Series A* 30 (1981), no. 3, pp. 369-380,
  <https://doi.org/10.1017/S1446788700017250>.
* Steven Diamond and Stephen Boyd, "CVXPY: A Python-Embedded Modeling Language for Convex
  Optimization", *Journal of Machine Learning Research* 17 (2016), no. 83, pp. 1-5,
  <https://jmlr.org/papers/v17/15-408.html>. Tested with version 1.9.2.
* Akshay Agrawal, Robin Verschueren, Steven Diamond and Stephen Boyd, "A rewriting system for
  convex optimization problems", *Journal of Control and Decision* 5 (2018), no. 1, pp. 42-60,
  <https://doi.org/10.1080/23307706.2017.1397554>.
* Paul J. Goulart and Yuwen Chen, "Clarabel: An interior-point solver for conic programs with
  quadratic objectives", arXiv:2405.12762, 2024, <https://arxiv.org/abs/2405.12762>. Tested
  with version 0.11.1.
* Brendan O'Donoghue, Eric Chu, Neal Parikh and Stephen Boyd, "Conic Optimization via Operator
  Splitting and Homogeneous Self-Dual Embedding", *Journal of Optimization Theory and
  Applications* 169 (2016), no. 3, pp. 1042-1068, <https://doi.org/10.1007/s10957-016-0892-3>.
  SCS is tested with version 3.2.11.
* Brendan O'Donoghue, "Operator Splitting for a Homogeneous Embedding of the Linear
  Complementarity Problem", *SIAM Journal on Optimization* 31 (2021), no. 3, pp. 1999-2023,
  <https://doi.org/10.1137/20M1366307>.
-/

namespace CASOracle.Sos

open Lean Elab Command Meta Term Tactic
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire

/-- The digits of `k` as subscripts, such as `₁₂`. -/
def subscript (k : Nat) : String :=
  String.map (fun c ↦ Char.ofNat (c.toNat - '0'.toNat + 0x2080)) (toString k)

/-- The first name `base` followed by a subscript of at least `start` that is not `taken`, and
the next index. -/
def freshName (base : String) (taken : NameSet) (start : Nat) : Name × Nat := Id.run do
  let mut k := start
  while taken.contains (Name.mkSimple s!"{base}{subscript k}") do
    k := k + 1
  return (Name.mkSimple s!"{base}{subscript k}", k + 1)

/-- Whether `e` is the literal `0`. -/
def isZeroLiteral (e : Lean.Expr) : Bool :=
  match e.consumeMData.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some 0
  | (``Zero.zero, _) => true
  | _ => false

/-- An order fact `small ≤ big` or `small < big` (also written with `≥` and `>`): its type, the
two sides, and whether it is strict. -/
def orderFact? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Bool) :=
  match e.consumeMData.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) => some (α, a, b, false)
  | (``GE.ge, #[α, _, a, b]) => some (α, b, a, false)
  | (``LT.lt, #[α, _, a, b]) => some (α, a, b, true)
  | (``GT.gt, #[α, _, a, b]) => some (α, b, a, true)
  | _ => none

/-- Whether the conclusion of `target`, under its `∀` binders and premises, is `a ≤ b`, `a < b`,
`a ≥ b` or `a > b`. -/
def isOrderGoal (target : Lean.Expr) : MetaM Bool :=
  forallTelescope target fun _ body ↦ do
    return (orderFact? (← instantiateMVars body)).isSome

/-- Names for the `∀` binders and premises of `target`: the user's names for the variables, and
fresh names `h₁, h₂, …` for the premises. -/
def introNames (target : Lean.Expr) : MetaM (Array Name) :=
  forallTelescope target fun xs _ ↦ do
    let mut taken : NameSet := {}
    for decl in ← getLCtx do
      taken := taken.insert decl.userName
    let mut names : Array Name := #[]
    let mut next := 1
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if ← isProp decl.type then
        let (name, k) := freshName "h" taken next
        names := names.push name
        taken := taken.insert name
        next := k
      else if decl.userName.hasMacroScopes then
        let (name, _) := freshName "x" taken 1
        names := names.push name
        taken := taken.insert name
      else
        names := names.push decl.userName
    return names

/-- A hypothesis `0 ≤ g` or `0 < g` used by a certificate: `g`, its term for the check and its
term as shown, whether it is strict, and the `have` that states it, if the hypothesis is `a ≤ b`
or `a < b` with `a ≠ 0`. -/
structure Hypothesis where
  /-- The factor `g`. -/
  factor : Lean.Expr
  /-- Its term, with the atoms as elaborated expressions. -/
  run : Term
  /-- Its term as shown. -/
  shown : Term
  /-- Whether the hypothesis is `0 < g`. -/
  strict : Bool
  /-- The `have hᵢ := sub_nonneg.mpr h` (or `sub_pos.mpr h`) that states `0 ≤ g` (or `0 < g`). -/
  step? : Option (TSyntax `tactic)

/-- A term of the certificate: the weight `d`, the polynomial `ℓ` (none for `±1`) and the
indices of the hypotheses it multiplies, an index possibly repeated. -/
structure Square (n : Nat) where
  /-- The positive weight. -/
  weight : Verified.Expr (Fin n)
  /-- The polynomial that is squared, if it is not `±1`. -/
  base? : Option (Verified.Expr (Fin n))
  /-- The hypotheses that multiply the square. -/
  hypotheses : List Nat

/-- Whether a term of the certificate is positive under the strict premises alone: its square is
`1` or that of a nonzero constant, and the hypotheses it multiplies are all `strict`. -/
def Square.isPositive {n : Nat} (square : Square n) (strict : Nat → Bool) : Bool :=
  (square.base?.all fun base ↦ (Translate.constantValue? base).any (· != 0)) &&
    square.hypotheses.all strict

/-- The term `∑ dᵢ * ℓᵢ ^ 2 * ∏ gⱼ` of a certificate, with the atoms `atomTerms` and the factors
`factorTerms`. -/
def certificateTerm {n : Nat} (oracle : Oracle) (squares : Array (Square n))
    (atomTerms factorTerms : Array Term) : TermElabM Term := do
  let ringTermOf (expression : Verified.Expr (Fin n)) : TermElabM Term := do
    match Translate.ringTerm (fun i ↦ atomTerms[i.val]!) expression with
    | .ok term => liftMacroM term
    | .error reason =>
        throwError "cas [oracle := {oracle.name}]: the oracle's certificate is refused: {reason}"
  let mut sum : Option Term := none
  for square in squares do
    let mut factors : Array Term := #[]
    if Translate.constantValue? square.weight != some 1 then
      factors := factors.push (← ringTermOf square.weight)
    if let some base := square.base? then
      let b ← ringTermOf base
      factors := factors.push (← `($b ^ 2))
    for j in square.hypotheses do
      factors := factors.push factorTerms[j]!
    let product ← match factors.toList with
      | [] => `(1)
      | f :: fs => fs.foldlM (fun acc g ↦ `($acc * $g)) f
    sum := some (← match sum with
      | none => pure product
      | some s => `($s + $product))
  match sum with
  | some s => return s
  | none => `(0)

/-- Read the oracle's records `square d ; ℓ` and `multiplied J ; d ; ℓ`, or with `multiplier`
those of the multiplier, `multiplier_square d ; ℓ` and `multiplier_multiplied J ; d ; ℓ`; the
other records are left out. -/
def readSquares (oracle : Oracle) (n : Nat) (found : Array Record) (hypotheses : Nat)
    (multiplier : Bool := false) : TermElabM (Array (Square n)) := do
  let refuse {α : Type} (why : String) : TermElabM α :=
    throwError "cas [oracle := {oracle.name}]: the certificate of {oracle.name} is refused: {why}"
  let squareKey := if multiplier then "multiplier_square" else "square"
  let multipliedKey := if multiplier then "multiplier_multiplied" else "multiplied"
  let mut squares : Array (Square n) := #[]
  for record in found do
    unless record.key == squareKey || record.key == multipliedKey do continue
    let fields := Translate.row record.payload
    let (indices, weightText, baseText) ← match record.key == multipliedKey, fields with
      | false, [d, l] => pure (([] : List Nat), d, l)
      | true, [j, d, l] => do
          let some js := ((j.splitOn " ").filter (fun s ↦ !s.isEmpty)).mapM String.toNat?
            | refuse s!"the indices {j} are not numbers"
          pure (js, d, l)
      | _, _ => refuse s!"the record {record.key} {record.payload} is not a term of a sum of \
          squares"
    for j in indices do
      unless j < hypotheses do refuse s!"there is no hypothesis {j}"
    let weight : Verified.Expr (Fin n) ← Translate.readAnswer oracle wireName weightText
    let some value := Translate.constantValue? weight
      | refuse s!"the weight {weightText} is not a number"
    unless 0 < value do refuse s!"the weight {weightText} is not positive"
    let base : Verified.Expr (Fin n) ← Translate.readAnswer oracle wireName baseText
    let base? := match Translate.constantValue? base with
      | some c => if c == 1 || c == -1 then none else some base
      | none => some base
    squares := squares.push { weight := weight, base? := base?, hypotheses := indices }
  return squares

/-- A certificate that `proveBySos` checked. -/
structure Checked where
  /-- The sum `S` as shown, or the identity `M * p = S` when the oracle multiplied `p` by `M`. -/
  certificate : Term
  /-- Whether the inequality is strict. -/
  strict : Bool
  /-- Whether the oracle multiplied `p` by a sum of squares `M`. -/
  multiplied : Bool
  /-- The script that proved the goal, as the line of text that was parsed and run and as the
  tactic parsed from it; `none` when the goal was proved over the elaborated atoms instead. -/
  replayed? : Option (String × TSyntax `tactic)

/-- The tactics as one tactic. -/
def tacticSequence (tactics : Array (TSyntax `tactic)) : TermElabM (TSyntax `tactic) :=
  if h : tactics.size = 1 then pure (tactics[0]'(by omega)) else `(tactic| ($tactics;*))

/-- The text of `script` on one line and the tactic parsed back from it, when that tactic closes
`goal` with a proof free of `sorry` and of metavariables, universe metavariables included, and
its run logs no error. Then the proof is kept and the messages of the run are dropped; otherwise
the state is restored and the result is `none`. The run is a probe whose failure the caller
answers by falling back, so every exception it throws gives `none`, except a runtime exception,
which is rethrown after the state is restored, and an interrupt, which is not caught. -/
def closesAsPrinted (goal : MVarId) (script : TSyntax `tactic) :
    TermElabM (Option (String × TSyntax `tactic)) := do
  -- On one line, so that the parse does not depend on where a long line breaks.
  let text := (← PrettyPrinter.ppTactic script).pretty 100000
  let .ok parsed := Parser.runParserCategory (← getEnv) `tactic text | return none
  -- The positions in `parsed` are offsets in `text`; the tactic is placed at the call instead.
  let info := SourceInfo.fromRef (← getRef)
  let tactic : TSyntax `tactic := ⟨parsed.rewriteBottomUp (·.setInfo info)⟩
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  -- The run starts from an empty log, so that an error in the log after it is one it added.
  Core.resetMessageLog
  let closed ← tryCatchRuntimeEx (do
      let remaining ← Tactic.run goal <| withoutErrToSorry <| Tactic.withoutRecover <|
        evalTactic tactic
      let proof ← instantiateMVars (mkMVar goal)
      return remaining.isEmpty && !proof.hasSorry && !proof.hasMVar &&
        !(← Core.getMessageLog).hasErrors) fun error ↦ do
    if error.isRuntime then
      saved.restore (restoreInfo := true)
      throw error
    return false
  if closed then
    Core.setMessageLog messages
    return some (text, tactic)
  saved.restore (restoreInfo := true)
  return none

/-- Rethrow `error`, with its message replaced by `f` of it when it is an error other than a
runtime exception. Runtime exceptions keep their message, whose kind is how Lean tells them from
other errors, and the internal exceptions, interrupts among them, are rethrown unchanged too. -/
def rethrowWith {m : Type → Type} {α : Type} [MonadExceptOf Exception m]
    (f : MessageData → MessageData) (error : Exception) : m α :=
  match error with
  | .error ref message =>
      if error.isRuntime then throwThe Exception error
      else throwThe Exception (.error ref (f message))
  | .internal .. => throwThe Exception error

/-- Run `x`, which asks the oracle and checks its answer, so that every error it throws once
`asked` is set ends with the sentence that the refusal says nothing about the inequality.
Runtime exceptions and the other exceptions that are not errors are rethrown unchanged
(`rethrowWith`). -/
def refusingAnswer {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf Exception m]
    [MonadLiftT (ST IO.RealWorld) m] (asked : IO.Ref Bool) (x : m α) : m α :=
  tryCatchThe Exception x fun error ↦ do
    if (← asked.get) then
      rethrowWith (fun message ↦ m!"{message}\nThis says nothing about the inequality.") error
    else
      throwThe Exception error

/-- Prove `goal`, an inequality between polynomials under `∀` binders and premises, from the
oracle's certificate: `p = S` for `0 ≤ p`, and for `0 < p` either `p = S` with a positive term in
`S`, or `M * p = S` with `0 ≤ M`. The proof is the script as printed when that script checks, and
otherwise the same certificate over the elaborated atoms. An oracle without the task `sos` is
refused first; `asked` is set just before the request is sent to the oracle's program. -/
def proveBySos (oracle : Oracle) (asked : IO.Ref Bool) (goal : MVarId) : TermElabM Checked := do
  let fromOracle (message : MessageData) : MessageData :=
    m!"cas [oracle := {oracle.name}]: {message}"
  -- The cheap refusal comes first, before `asked` is set: nothing has been asked yet.
  try requireTask oracle "sos" catch error => rethrowWith fromOracle error
  let target ← goal.withContext do instantiateMVars (← goal.getType)
  let names ← goal.withContext (introNames target)
  let ids : Array Ident := names.map mkIdent
  let introTactic? : Option (TSyntax `tactic) ← if names.isEmpty then pure none else
    some <$> `(tactic| intro $ids*)
  -- The certificate is read, and checked when the printed script fails, on a copy of the goal.
  let copy ← goal.withContext do return (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
  let inner ← match introTactic? with
    | none => pure copy
    | some tactic => do
        match ← Tactic.run copy (evalTactic tactic) with
        | [g] => pure g
        | _ => throwError "cas [oracle := {oracle.name}]: the binders of the goal do not \
            introduce"
  inner.withContext do
    let goalType := (← instantiateMVars (← inner.getType)).consumeMData
    let some (type, small, big, strict) := orderFact? goalType
      | throwError "cas [oracle := {oracle.name}]: the goal is not an inequality"
    let flipped := goalType.isAppOf ``GE.ge || goalType.isAppOf ``GT.gt
    -- The first eight named hypotheses `0 ≤ g`, `0 < g`, `a ≤ b` and `a < b` (or with `≥` and
    -- `>`) between terms of the goal's type, counted before they are read as polynomials.
    let mut taken : NameSet := {}
    for decl in ← getLCtx do
      taken := taken.insert decl.userName
    let mut next := 1
    let mut candidates : Array Hypothesis := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
      if candidates.size ≥ 8 then break
      let some (α, low, high, strictFact) := orderFact? (← instantiateMVars decl.type) | continue
      unless ← isDefEq α type do continue
      let highRun ← Term.exprToSyntax high
      let highShown : Term ← PrettyPrinter.delab high
      if isZeroLiteral low then
        candidates := candidates.push
          { factor := high, run := highRun, shown := highShown, strict := strictFact,
            step? := none }
      else
        let factor ← mkAppM ``HSub.hSub #[high, low]
        let lowRun ← Term.exprToSyntax low
        let lowShown : Term ← PrettyPrinter.delab low
        let (name, k) := freshName "h" taken next
        taken := taken.insert name
        next := k
        let given := mkIdent decl.userName
        let hName := mkIdent name
        -- Names from `mkIdent` carry no macro scopes, so the suggestion prints them as written.
        let lemmaName := mkIdent (if strictFact then `sub_pos.mpr else `sub_nonneg.mpr)
        let step ← `(tactic| have $hName:ident := $lemmaName:ident $given:ident)
        let run ← `($highRun - $lowRun)
        let shown ← `($highShown - $lowShown)
        candidates := candidates.push
          { factor, run, shown, strict := strictFact, step? := some step }
    -- The polynomial `p` of `0 ≤ p` or `0 < p`.
    let smallZero := isZeroLiteral small
    let p ← if smallZero then pure big else mkAppM ``HSub.hSub #[big, small]
    let (pReified, pAtoms) ← (CAS.Command.Ideal.reifyPoly p).run #[]
    -- `reifyPoly` makes an atom of every subterm that is not a polynomial operation, so every
    -- factor is a polynomial over the atoms; the `catch` only guards against a failure of the
    -- reification itself.
    let mut atoms := pAtoms
    let mut exprs := #[pReified]
    let mut kept : Array Hypothesis := #[]
    for hypothesis in candidates do
      try
        let (reified, extended) ← (CAS.Command.Ideal.reifyPoly hypothesis.factor).run atoms
        atoms := extended
        exprs := exprs.push reified
        kept := kept.push hypothesis
      catch _ => pure ()
    let hypotheses := kept
    let isStrict (j : Nat) : Bool := (hypotheses[j]?.map (·.strict)).getD false
    let n := atoms.size
    let typed := exprs.map (CAS.Command.Ideal.overAtoms n)
    let texts ← typed.mapM (Translate.write (Translate.requestLanguage oracle) wireName)
    let wire := wireNames n
    let hypothesisTexts := (texts.extract 1 texts.size).toList.map (pyRead · wire)
    -- For `0 < p`, the oracle learns which hypotheses are strict, and may answer with a
    -- multiplier.
    let strictIndices := (List.range hypotheses.size).filter isStrict
    let (keys, strictArgument) := if strict then
        (["square", "multiplied", "multiplier_square", "multiplier_multiplied"],
          s!", strict=[{", ".intercalate (strictIndices.map toString)}]")
      else (["square", "multiplied"], "")
    -- The task was checked at the start, so the request is now sent. From here on, the callers'
    -- `refusingAnswer` adds to every error that it says nothing about the inequality.
    asked.set true
    let found ← try
        askPython oracle "sos" keys
          s!"{pyRead (texts[0]?.getD "0") wire}, [{", ".intercalate hypothesisTexts}], \
            {pyVariables wire}{strictArgument}" (allowEmpty := true)
      catch error => rethrowWith fromOracle error
    if found.isEmpty then
      throwError "cas [oracle := {oracle.name}]: {oracle.name} found no sum of squares"
    -- An answer that cannot be read as a certificate of the required form is refused.
    let squares ← readSquares oracle n found hypotheses.size
    let multiplier ← readSquares oracle n found hypotheses.size (multiplier := true)
    -- `positivity` may use any hypothesis in context, so we check the positive term here.
    if strict && !squares.any (·.isPositive isStrict) then
      throwError "cas [oracle := {oracle.name}]: the sum of squares proposed by {oracle.name} is \
        refused: no term is a positive constant or a positive constant times strict premises"
    let atomRun ← atoms.mapM fun a ↦ Term.exprToSyntax a
    let atomShown ← atoms.mapM fun a ↦ do return (← PrettyPrinter.delab a : Term)
    let factorsRun := hypotheses.map (·.run)
    let factorsShown := hypotheses.map (·.shown)
    let sumRun ← certificateTerm oracle squares atomRun factorsRun
    let sumShown ← certificateTerm oracle squares atomShown factorsShown
    let multiplierRun ← certificateTerm oracle multiplier atomRun factorsRun
    let multiplierShown ← certificateTerm oracle multiplier atomShown factorsShown
    let bigRun ← Term.exprToSyntax big
    let smallRun ← Term.exprToSyntax small
    let bigShown : Term ← PrettyPrinter.delab big
    let smallShown : Term ← PrettyPrinter.delab small
    let pRun : Term ← if smallZero then pure bigRun else `($bigRun - $smallRun)
    let pShown : Term ← if smallZero then pure bigShown else `($bigShown - $smallShown)
    -- The goal becomes `0 ≤ p` or `0 < p`, and then `0 ≤ S` or `0 < S` through `p = S`, or
    -- through `0 < M * p` and `M * p = S` with a multiplier. The script as shown proves the
    -- identity by `ring`, the check over the elaborated atoms by `ring1`, whose failure logs no
    -- `ring_nf` suggestion.
    let flipLemma := mkIdent (if strict then `gt_iff_lt else `ge_iff_le)
    let subLemma := mkIdent (if strict then `sub_pos else `sub_nonneg)
    let mulPos := mkIdent `pos_of_mul_pos_right
    let factorName := mkIdent `a
    let script (mT pT sT : Term) (close : TSyntax `tactic) :
        TermElabM (Array (TSyntax `tactic)) := do
      if multiplier.isEmpty then
        let rewrite ← match flipped, smallZero with
          | false, true => `(tactic| rw [show $pT = $sT by $close:tactic])
          | false, false => `(tactic| rw [← $subLemma:ident, show $pT = $sT by $close:tactic])
          | true, true => `(tactic| rw [$flipLemma:ident, show $pT = $sT by $close:tactic])
          | true, false =>
              `(tactic| rw [$flipLemma:ident, ← $subLemma:ident, show $pT = $sT by $close:tactic])
        return #[rewrite, ← `(tactic| positivity)]
      let normalize : Array (TSyntax `tactic) ← match flipped, smallZero with
        | false, true => pure #[]
        | false, false => pure #[← `(tactic| rw [← $subLemma:ident])]
        | true, true => pure #[← `(tactic| rw [$flipLemma:ident])]
        | true, false => pure #[← `(tactic| rw [$flipLemma:ident, ← $subLemma:ident])]
      return normalize ++ #[
        ← `(tactic| refine $mulPos:ident ($factorName:ident := $mT) ?_ (by positivity)),
        ← `(tactic| rw [show $mT * $pT = $sT by $close:tactic]),
        ← `(tactic| positivity)]
    -- Only the hypotheses the certificate multiplies are stated.
    let used := (squares ++ multiplier).foldl (fun acc s ↦ acc ++ s.hypotheses) ([] : List Nat)
    let steps := ((List.range hypotheses.size).filter used.contains).toArray.filterMap
      fun j ↦ (hypotheses[j]?).bind (·.step?)
    let shown := introTactic?.toArray ++ steps ++
      (← script multiplierShown pShown sumShown (← `(tactic| ring)))
    let replayed? ← closesAsPrinted goal (← tacticSequence shown)
    unless replayed?.isSome do
      let check := steps ++ (← script multiplierRun pRun sumRun (← `(tactic| ring1)))
      -- Without error recovery, a failed `ring1` inside `show` is an error rather than a `sorry`.
      try
        let remaining ← Tactic.run inner <| withoutErrToSorry <| Tactic.withoutRecover <|
          evalTactic (← `(tactic| ($check;*)))
        unless remaining.isEmpty do throwError "goals remain"
      catch error =>
        rethrowWith (fun message ↦ fromOracle m!"the sum of squares proposed by {oracle.name} is \
          refused{indentD message}") error
      goal.assign (mkMVar copy)
    let certificate ← if multiplier.isEmpty then pure sumShown
      else `($multiplierShown * $pShown = $sumShown)
    return { certificate, strict, multiplied := !multiplier.isEmpty, replayed? }

/-- Close the main goal, an inequality between polynomials, from the oracle's sum of squares.
Returns the tactic to record for `cas?` and the suggestion: the script that proved the goal, as
the line of text that was parsed and run, or the call itself when that script does not check
here and the goal was proved over the elaborated atoms. Once the oracle has been asked, every
refusal ends with the sentence that it says nothing about the inequality. -/
def closeBySos (oracle : Oracle) :
    TacticM (TSyntax `tactic × Lean.Meta.Tactic.TryThis.Suggestion) := do
  let call : TSyntax `tactic := ⟨← getRef⟩
  let result ← IO.mkRef (none : Option Checked)
  let asked ← IO.mkRef false
  refusingAnswer asked <| closeGoal s!"cas [oracle := {oracle.name}]" fun goal ↦ do
    result.set (some (← proveBySos oracle asked goal))
  let some checked ← result.get
    | throwError "cas [oracle := {oracle.name}]: the sum of squares gave no script"
  if let some (text, tactic) := checked.replayed? then
    return (tactic, ({ suggestion := .string text } : Lean.Meta.Tactic.TryThis.Suggestion))
  logInfo m!"cas [oracle := {oracle.name}]: the script as printed does not check here, so no \
    oracle-free script is suggested; the goal is proved from the same certificate over the \
    elaborated atoms"
  return (call, ({ suggestion := .tsyntax call } : Lean.Meta.Tactic.TryThis.Suggestion))

/-- `#cas [sos x, y, oracle := o] p` proves that the polynomial `p` is nonnegative for all real
`x`, `y`, or proves `p` when it is an inequality, strict or not, and prints the certificate.

## Theorem
`∀ x y : ℝ, 0 ≤ p`, or `∀ x y : ℝ, p` when `p` is an inequality such as
`x ≥ 0 → y > 0 → a > b`. The certificate is an identity `q = S`, which `ring` checks, where `q`
is the difference of the two sides and `S = ∑ dᵢ * ℓᵢ ^ 2 * ∏ gⱼ` has positive rational weights
`dᵢ` and factors `gⱼ` from premises `0 ≤ gⱼ` or `0 < gⱼ`; `positivity` proves `0 ≤ S`. For a
strict inequality some term of `S` is a positive constant, or a positive constant times strict
premises, and `positivity` proves `0 < S`. When the oracle finds no such `S` equal to `q`, it
looks for a multiplier `M`, also a sum `∑ dᵢ * ℓᵢ ^ 2 * ∏ gⱼ`, such that `M * q = S`, and
`pos_of_mul_pos_right` turns `0 < M * q` and `0 ≤ M` into `0 < q`.

## Conditions and limits
`p` is a polynomial with rational coefficients over atoms. Sums, differences, products,
negations, numerals, powers `a ^ k` with a literal natural exponent `k ≤ 1000` and divisions
`a / k` by a nonzero numeral in a division ring are read as such; every other subterm, such as
`x ^ 1001` or `x / y`, counts as a variable, and subterms equal up to reducible unfolding count as
the same variable. Of the oracles only `sympy` has this task; another one is refused before it
is asked. The oracle `sympy` needs cvxpy (`pip install cvxpy`) in its Python. It looks
numerically for positive semidefinite Gram matrices, each over at most 40 monomials, and rounds
them to exact rationals. It is sent the first eight named premises that are inequalities between
real terms, counted before they are read as polynomials; the other premises are not sent, but
`positivity` sees all of them. A square multiplies a product of distinct premises, with at most
64 such products for `S` and `M` together. A positive term is a positive constant times a
product of strict premises of positive degree, a premise possibly repeated, with at most 32 such
products, the empty one included. The multiplier has degree at most 2, then at most 4, and is
tried only when the search without one fails; its terms may carry premises, so that `0 ≤ M` may
rest on them.

## Options
None.

## Examples
```lean
#cas [sos x, y, oracle := sympy] (x^4 + y^4 - 4*x*y + 2)
#cas [sos x, oracle := sympy] (x^4 - x + 1 > 0)
#cas [sos x, y, oracle := sympy] ((x*y - 1)^2 + x^2 > 0)
```
print a sum of squares equal to the polynomial, with a positive constant term in the second, and
for the third, which takes values below every positive constant, so that no sum with a positive
constant term equals it, the identity `M * q = S` with a multiplier. Each comes with an
`example` of the statement proved without the oracle by a script, which is printed on one line
exactly as it was parsed and checked on the goal. The goal has the variables of the section in
scope, so that each name of the script means what it means where the command is, also when a
variable has the name of a lemma that the script uses. They are not premises, `positivity` and
instance search skip them, and a proof that uses one is refused. The `example` is printed only
once it states the statement and elaborates without errors where the command is to a declaration
of the statement with no `sorry`; otherwise the line of the `Oracle-free proof` is `none`,
followed by the check that failed. The declaration can have another type: the `example` command
takes as arguments the variables of the section that its proof uses, so a script that uses one
there declares another proposition.

## In a proof
`cas [oracle := sympy]` proves `0 ≤ p`, `0 < p`, `a ≤ b`, `a < b`, `a ≥ b` and `a > b` between
polynomials, under `∀` binders and premises. It prints the script on one line, parses that line
back and runs it on the goal, and the line it suggests is that text. When the script does not
check, for an atom printed as `x✝` for instance, the goal is proved from the same certificate
over the atoms as elaborated, and the suggestion is the call itself:
```lean
example : ∀ x : ℝ, 0 < x → 0 < x ^ 3 + x := by
  cas [oracle := sympy]
```

## See also
Mathematica `PolynomialSumOfSquaresList`; `cas [oracle := o]` for ideal memberships and
consequences of equations.

## Possible issues
A nonnegative polynomial need not be a sum of squares: for Motzkin's
`x^4*y^2 + x^2*y^4 - 3*x^2*y^2 + 1` the oracle finds no positive semidefinite Gram matrix.
Without premises a polynomial of odd degree is refused at once, since no sum of squares has odd
degree. For a strict inequality the oracle may find no sum with a positive term, as for
`x ≠ 0 → 0 < x ^ 2`, whose premise is not an inequality and is not sent. Every refusal that
comes after the oracle was asked ends with "This says nothing about the inequality.", whether
the oracle found nothing, its answer could not be read, its certificate failed the check, or the
kernel refused the proof. -/
syntax (name := casSosCommand)
  "#cas" "[" &"sos" (atomic(ident ", "))+ &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [sos x, y, oracle := o] p`. The statement is elaborated without the variables
of the section. The proof is searched on a goal whose local context holds them as implementation
details: the candidates for premises, the hypotheses that `positivity` compares and instance
search skip them, and a proof with a free variable is refused. Their names still resolve, so the
script is printed and replayed with the names in scope where the command is, and the premises it
introduces are named apart from them. The report prints the `example` that `checkExample` gives
for the statement and the script, or a `none` line that says which check failed: the replay of
the script on the goal, or that the `example` states the statement, that it elaborates without
errors to a declaration with no `sorry`, or that this declaration has the statement as its
type. -/
@[command_elab casSosCommand]
def elabSos : CommandElab := fun stx ↦ do
  let `(#cas [sos $[$xs:ident, ]* oracle := $o:ident] $p:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let shownNames := xs.map fun x ↦ renderName x.getId
  let asked ← IO.mkRef false
  refusingAnswer asked <| withAuditedEvidence "sos" do
    let (statement, inequality) ← liftTermElabM do
      let elabFun (body : Term) : TermElabM Lean.Expr := do
        let abstraction ← xs.foldrM (fun x acc ↦ `(fun $x:ident : ℝ ↦ $acc)) body
        let f ← withoutErrToSorry (elabTerm abstraction none)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars f
      let f ← elabFun p
      let inequality ← lambdaTelescope f fun _ body ↦ isProp body
      let f ← if inequality then pure f else elabFun (← `(0 ≤ $p))
      let statement ← lambdaTelescope f fun ys body ↦ mkForallFVars ys body
      if statement.hasMVar then
        throwErrorAt p "sos: {p} is not a statement about real numbers {shownNames.toList}"
      return (statement, inequality)
    let (sumText, checked, report) ← runTermElabM fun _ ↦ do
      -- Every local of the command's context, the variables of the section, becomes an
      -- implementation detail with no local instance. The candidates for premises of
      -- `proveBySos`, the hypotheses that `positivity` compares and instance search skip them,
      -- and a proof that mentions one is refused below. Their names still resolve, so the
      -- script is printed and replayed with the names in scope where the command is: a variable
      -- named `sub_pos` is what `sub_pos` means in the script, and `introNames` names the
      -- premises apart from them.
      let lctx ← getLCtx
      let lctx := lctx.foldl (fun lctx decl ↦ lctx.setKind decl.fvarId .implDetail) lctx
      withLCtx lctx #[] do
        let goal ← mkFreshExprSyntheticOpaqueMVar statement
        let checked ← proveBySos oracle asked goal.mvarId!
        let proof ← instantiateMVars goal
        if proof.hasMVar then throwError "sos: the proof is incomplete"
        if proof.hasFVar then throwError "sos: the proof uses a variable of the section"
        -- The proposition is printed with the names of the section in scope, as the script is.
        let report ← addMessageContext (← evidence #[("Sum of squares", statement, proof)])
        let sumText := toString (← PrettyPrinter.ppTerm checked.certificate)
        return (sumText, checked, report)
    -- The script introduces the binders of the statement itself, so the `example` has none.
    let proofLine : MessageData ← match checked.replayed? with
      | none => pure m!"none: the script as printed does not check here; the statement is \
          proved from the same certificate over the atoms as elaborated"
      | some (text, _) => do
        match ← checkExample statement #[text] (binders := false) with
        | .ok shown => pure m!"{shown}"
        | .error .notStated => pure m!"none: the script checks on the goal, but where the \
            command is, the `example` with it does not state the proposition proved"
        | .error .notElaborated => pure m!"none: the script checks on the goal, but where the \
            command is, the `example` with it does not elaborate without errors to a \
            declaration with no `sorry`"
        | .error .otherDeclaration => pure m!"none: the script checks on the goal, but where \
            the command is, the declaration of the `example` with it is not the proposition \
            proved"
    let domain := if h : shownNames.size = 1 then s!"{shownNames[0]'(by omega)} ∈ ℝ"
      else s!"({", ".intercalate shownNames.toList}) ∈ ℝ^{shownNames.size}"
    logReport stx {
      domain := domain
      input := surfaceText p
      inputType := if inequality then "polynomial inequality" else "polynomial"
      output := sumText
      outputType :=
        if checked.multiplied then "multiplier and sum of squares with a positive term (checked)"
        else if checked.strict then "sum of squares with a positive term (checked)"
        else "sum of squares (checked)"
    } #[computationNode "Oracle-free proof" #[proofLine],
        hintsNode oracle #[if checked.multiplied then m!"the Gram matrices of the sum and of the \
            multiplier were found numerically by cvxpy and rounded to exact rationals"
          else m!"the Gram matrix was found numerically by cvxpy and rounded to exact \
            rationals"], report]

end CASOracle.Sos
