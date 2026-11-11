/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Groebner
public import CAS.Command.Reduce
public import CAS.Command.Systems
public meta import CAS.Command.Groebner
public meta import CAS.Command.Reduce
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Nonlinear polynomial systems: `#cas [solve x, y, …]`

`#cas [solve x, y] (p₁ = q₁ ∧ p₂ = q₂ ∧ …)` with polynomial equations over ℚ, at least one of
them nonlinear, finds every real solution of a system with finitely many complex solutions
and proves the list complete:

```
∃ ρ, (bounds on ρ j) ∧ ∀ x y, (p₁ = q₁ ∧ p₂ = q₂) ↔ (x = a₀ ∧ y = b₀) ∨ (x = a₁ ∧ y = b₁) ∨ ⋯
```

A rational root gives exact coordinates. An irrational root appears as `ρ j` in its isolating
interval of width `10 ^ (-20)`, the coordinates as polynomials in `ρ j`; the report adds their
decimal values. Systems with infinitely many complex solutions, and linear systems, which the
linear `solve` command handles, are not taken.

## Implementation notes

The method is a lexicographic Gröbner basis over ℚ, computed by Buchberger's algorithm with
recorded derivations (`CAS.Command.Groebner`, `CAS/Command/Groebner.lean`), in shape position,
`v - g_v(t)` for the unknowns and one polynomial `R(t)`, where `t` is an unknown or, when each
unknown takes one of its values at two solutions, a separating form `t = x + c y + c² z + ⋯`,
tried for `c = 1, 2, …` up to `(n - 1) D (D - 1) / 2 + 1` for `n` unknowns and `D` complex
solutions counted with multiplicity (`standardCount`); the report names the form. Two distinct
solutions agree under the form for at most `n - 1` values of `c`, so the search fails only for a
system with a repeated complex solution. That a separating form then gives a basis in shape
position is the classical shape lemma; the proof does not use it, since it checks the basis it
gets. The proof has four parts:

* the system is equivalent to `R(t) = 0 ∧ x = g_x(t) ∧ ⋯`: one direction replays the
  derivation of the basis as `linear_combination` steps, the other divides each equation by
  the basis;
* at a root `s` of `R` with `x = g_x(s), …`, the form `t` equals `s`, by one more division;
* the real roots of `R` are isolated by `reduceCheck` (`CAS/Polynomial/RealRoot/SignReduce.lean`)
  on the root list of `Reduce.rootData`, one kernel evaluation;
* `solve_of_reduceCheck` turns these into the list of points, one for each real root.

When the basis is `1`, the replayed derivation of `1 = 0` proves that the system has no
solution. The `linear_combination` steps grow with the degree of `R`, so the proof, its kernel
check and the check of the report each run under a budget of at least ten million heartbeats
(`withProofBudget`).
-/

public meta section

namespace CAS.Command.PolySystems

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Polynomial
open CAS.Polynomial.RealRoot
open CAS.Command.SpecialFunctions
open CAS.Command.Groebner

/-- The polynomial of an expression, with division by nonzero rational constants. -/
def polyOf? {n : Nat} : Verified.Expr (Fin n) → Option (Verified.Expr.Alg.MvPoly n)
  | .add a b => return Verified.Expr.Alg.mvAdd (← polyOf? a) (← polyOf? b)
  | .sub a b => return Verified.Expr.Alg.mvSub (← polyOf? a) (← polyOf? b)
  | .mul a b => return Verified.Expr.Alg.mvMulPoly (← polyOf? a) (← polyOf? b)
  | .neg a => return Verified.Expr.Alg.mvNeg (← polyOf? a)
  | .pow a k => return Verified.Expr.Alg.mvPowPoly (← polyOf? a) k
  | .div a b => do
      let pa ← polyOf? a
      match Verified.Expr.Alg.mvNormalize (← polyOf? b) with
      | [(c, mono)] =>
          if c != 0 && (List.finRange n).all (mono · == 0) then
            return Verified.Expr.Alg.mvMulPoly pa [(1 / c, Verified.Expr.Alg.mvOne n)]
          else none
      | _ => none
  | other => Verified.Expr.Alg.mvPolyOf? other

/-- A polynomial as real term syntax, with variable `i` read as `vars[i]`. -/
def polySyntax (vars : Array (TSyntax `term)) (p : Poly) : CommandElabM (TSyntax `term) := do
  let zero ← `((0 : ℝ))
  let monomial (m : Mono) : CommandElabM (Option (TSyntax `term)) := do
    let mut result : Option (TSyntax `term) := none
    for i in [0:m.size] do
      let e := m.getD i 0
      if e == 0 then continue
      let v := vars.getD i zero
      let factor ← if e == 1 then pure v else
        let eLit : TSyntax `term := ⟨Syntax.mkNumLit (toString e)⟩
        `($v ^ $eLit)
      result := some (← match result with
        | none => pure factor
        | some r => `($r * $factor))
    return result
  let term (c : ℚ) (m : Mono) : CommandElabM (TSyntax `term) := do
    let magnitude ← ratSyntax c
    match ← monomial m with
    | none => `(($magnitude : ℝ))
    | some mono => if c == 1 then pure mono else `($magnitude * $mono)
  match p with
  | [] => pure zero
  | (m, c) :: rest =>
      let first ← if c < 0 then `(-$(← term (-c) m)) else term c m
      rest.foldlM (fun total (m, c) ↦ do
        if c < 0 then `($total - $(← term (-c) m)) else `($total + $(← term c m))) first

/-- `linear_combination ∑ cᵢ hᵢ`, or `linear_combination` for the empty sum. -/
def combination (vars : Array (TSyntax `term)) (terms : List (TSyntax `term × Poly)) :
    CommandElabM (TSyntax `term) := do
  let mut total : Option (TSyntax `term) := none
  for (h, c) in terms do
    let isOne := match c with
      | [(m, d)] => d == 1 && m.all (· == 0)
      | _ => false
    let piece ← if isOne then pure h else `(($(← polySyntax vars c)) * $h)
    total := some (← match total with
      | none => pure piece
      | some t => `($t + $piece))
  match total with
  | none => `(by linear_combination)
  | some t => `(by linear_combination $t:term)

/-- An enclosure of a polynomial in one variable on `[lo, hi]`, by Horner's rule in interval
arithmetic. -/
def evalOn (coefficients : List ℚ) (lo hi : ℚ) : ℚ × ℚ :=
  coefficients.foldr (fun c (a, b) ↦
    let products := [lo * a, lo * b, hi * a, hi * b]
    let low := products.foldl min (lo * a)
    let high := products.foldl max (lo * a)
    (c + low, c + high)) (0, 0)

/-- A rational rounded to fifteen decimals, without trailing zeros. -/
def approx (q : ℚ) : String :=
  let scaled : ℚ := q * 10 ^ 15
  let text := Digits.renderSigned
    (scaled.floor + if scaled - scaled.floor ≥ 1 / 2 then 1 else 0) 15
  let trimmed := (text.toList.reverse.dropWhile (· == '0')).reverse
  String.ofList (if trimmed.getLast? == some '.' then trimmed.dropLast else trimmed)

/-- One attempt: the user unknown placed at each internal position, and the separating form
`t = ∑ c_v v` when the last internal variable is not an unknown. -/
structure Attempt where
  /-- The user unknown at each internal position, position `0` the largest variable. -/
  order : Array Nat
  /-- The coefficients `c_v` of `t = ∑ c_v v` by user unknown, with `t` an extra last
  variable; `none` when the last unknown of `order` is the last variable. -/
  form : Option (Array Int)

/-- Each unknown last, the last unknown first. -/
def byUnknown (n : Nat) : List Attempt :=
  (List.range n).reverse.map fun t ↦
    { order := ((List.range n).filter (· != t) ++ [t]).toArray, form := none : Attempt }

/-- The separating form `t = x₁ + c x₂ + c² x₃ + ⋯` in `n` unknowns. -/
def separating (n c : Nat) : Attempt :=
  { order := (List.range n).toArray, form := some ((Array.range n).map fun i ↦ (c : Int) ^ i) }

/-- The number of monomials in `n` variables that no monomial of `leads` divides, for the leading
monomials of a zero-dimensional basis: the dimension of the quotient ring, which is the number of
complex solutions counted with multiplicity. -/
def standardCount (n : Nat) (leads : List Mono) : Nat := Id.run do
  let mut count := 0
  let mut stack : List Mono := [Array.replicate n 0]
  let mut seen : List Mono := []
  while true do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if seen.contains m || leads.any (divides · m) then continue
      seen := m :: seen
      count := count + 1
      for i in [0:n] do
        stack := m.set! i (m.getD i 0 + 1) :: stack
  return count

/-- The Gröbner basis of `polys` for one attempt: in the order of the attempt, with the extra last
variable `t` and the equation `t = ∑ c_v v` when the attempt has a separating form. -/
def basisOf {n : Nat} (polys : Array (Verified.Expr.Alg.MvPoly n)) (attempt : Attempt) :
    Except String Result :=
  let size := if attempt.form.isSome then n + 1 else n
  let inputs := polys.toList.map (ofMvPoly size attempt.order)
  match attempt.form with
  | none => groebner inputs
  | some form =>
      let combination := (List.range n).foldl (fun total v ↦
        add total (scale (form.getD v 0) (var size v))) []
      groebner (inputs ++ [sub (var size n) combination])

/-- A separating form as text, such as `x + 6*y + 36*z`. -/
def formText (names : Array Name) (form : Array Int) : String :=
  let terms := (names.toList.zip form.toList).filterMap fun (name, c) ↦
    let v := renderName name
    if c == 0 then none else some (c, if c == 1 || c == -1 then v else s!"{c.natAbs}*{v}")
  match terms with
  | [] => "0"
  | (c, first) :: rest =>
      rest.foldl (fun text (c, term) ↦ text ++ (if c < 0 then " - " else " + ") ++ term)
        ((if c < 0 then "-" else "") ++ first)

/-- The family of separating forms as text, such as `x + c*y + c^2*z`. -/
def familyText (names : Array Name) : String :=
  " + ".intercalate (names.toList.zipIdx.map fun (name, i) ↦
    let v := renderName name
    if i = 0 then v else if i = 1 then s!"c*{v}" else s!"c^{i}*{v}")

/-- Run `x` under a budget of at least ten million heartbeats, for the elaborator and for the
kernel checks that `x` runs; `maxHeartbeats 0`, no limit, stays unlimited. The
`linear_combination` steps of a proof grow with the degree of the eliminant. -/
def withProofBudget {α : Type} (x : TermElabM α) : TermElabM α := do
  let option := maxHeartbeats.get (← getOptions)
  let budget := if option == 0 then 0 else max option 10000000
  withOptions (fun options ↦ maxHeartbeats.set options budget) <|
    withTheReader Core.Context (fun context ↦ { context with maxHeartbeats := budget * 1000 }) <|
      withCurrHeartbeats x

/-- The outcome of the Gröbner stage. -/
inductive Outcome where
  | inconsistent (result : Result)
  | shape (attempt : Attempt) (result : Result) (eliminant : Nat) (solved : Array Nat)

/-- Run `#cas [solve x, y, …] system` for a nonlinear polynomial system. -/
def logPolySystem (ref : Syntax) (unknowns : Array (TSyntax `ident)) (input : Syntax) :
    CommandElabM Unit := do
  let names := unknowns.map (·.getId)
  let n := names.size
  let equations := Systems.conjuncts input
  let mut polys : Array (Verified.Expr.Alg.MvPoly n) := #[]
  let mut equationSyntax : Array (TSyntax `term) := #[]
  let mut nonlinear := false
  for equation in equations do
    let (lhs, rhs) ← match equation with
      | `($l:term = $r:term) => pure (l, r)
      | _ => throwUnsupportedSyntax
    let reified ← try parseExact (← `($lhs - $rhs)) names.toList catch _ => throwUnsupportedSyntax
    let p? : Option (Verified.Expr.Alg.MvPoly n) :=
      if h : reified.names.length = n then
        h ▸ polyOf? reified.expr
      else none
    let some p := p? | throwUnsupportedSyntax
    if p.any (fun (c, m) ↦ c != 0 && Verified.Expr.Alg.mvTotalDegree m > 1) then
      nonlinear := true
    polys := polys.push p
    equationSyntax := equationSyntax.push ⟨equation⟩
  unless nonlinear do throwUnsupportedSyntax
  let m := polys.size
  -- The Gröbner stage: each unknown last, then the separating forms.
  let mut found : Option Outcome := none
  let mut positiveDimensional := false
  let mut failure : Option String := none
  let mut leads : Option (List Mono) := none
  for attempt in byUnknown n do
    match basisOf polys attempt with
    | .error message => failure := some message
    | .ok result =>
        if result.isUnit then
          found := some (.inconsistent result)
          break
        if !result.isZeroDimensional n then
          positiveDimensional := true
          break
        if let some (r, solved) := result.shape? n then
          found := some (.shape attempt result r solved)
          break
        if leads.isNone then leads := some (result.basis.map fun k ↦ (lead (result.poly k)).1)
  if positiveDimensional then
    throwErrorAt input "solve: the system has infinitely many complex solutions; the nonlinear \
      solver takes systems with finitely many"
  -- The forms `t = x₁ + c x₂ + c² x₃ + ⋯` for `c = 1, 2, …, C`. Two distinct solutions agree
  -- under the form for at most `n - 1` values of `c`, and the `D` solutions counted with
  -- multiplicity make at most `D (D - 1) / 2` pairs, so some `c ≤ C` separates them all; the
  -- shape lemma then gives shape position when every solution is simple.
  let mut formBound : Option Nat := none
  if found.isNone then
    if let some basisLeads := leads then
      let count := standardCount n basisLeads
      let bound := (n - 1) * (count * (count - 1) / 2) + 1
      let mut complete := true
      for c in [1:bound + 1] do
        let attempt := separating n c
        match basisOf polys attempt with
        | .error message =>
            failure := some message
            complete := false
        | .ok result =>
            if let some (r, solved) := result.shape? (n + 1) then
              found := some (.shape attempt result r solved)
              break
      if complete then formBound := some bound
  let some outcome := found | do
    if let some bound := formBound then
      throwErrorAt input "solve: no separating form {familyText names} with c ≤ {bound} gives a \
        Gröbner basis in shape position, so the system has a repeated complex solution"
    throwErrorAt input "solve: {failure.getD "no shape-position Gröbner basis was found"}"
  let idents : Array (TSyntax `term) := unknowns.map fun u ↦ ⟨u.raw⟩
  let hyp (stem : String) (k : Nat) : TSyntax `term := ⟨mkIdent (Name.mkSimple s!"{stem}{k}")⟩
  let sName : Name := if names.contains `s then `s₀ else `s
  let sTerm : TSyntax `term := ⟨mkIdent sName⟩
  let system ← match equationSyntax.toList.reverse with
    | [] => throwUnsupportedSyntax
    | last :: rest => rest.foldlM (fun total e ↦ `($e ∧ $total)) last
  let domain := s!"({renderNames names.toList}) ∈ ℝ^{n}"
  match outcome with
  | .inconsistent result =>
      -- The basis is `{1}`: replay the derivation of `1 = 0`.
      let some unit := result.basis.head? | throwError "solve: empty basis"
      let vars := idents
      let mut body ← `(absurd $(hyp "hg" unit) one_ne_zero)
      for k in (result.closure [unit]).reverse do
        let node := result.nodes.getD k default
        if node.input then continue
        let terms := node.combo.map fun (j, c) ↦ (hyp "hg" j, c)
        let statement ← `($(← polySyntax vars node.poly) = 0)
        let name : TSyntax `ident := mkIdent (Name.mkSimple s!"hg{k}")
        body ← `(have $name : $statement := $(← combination vars terms); $body)
      let patterns := (List.range m).map fun k ↦ hyp "hg" k
      let pattern ← if m == 1 then pure patterns.head! else `(⟨$(patterns.toArray),*⟩)
      let statement ← `(∀ $unknowns* : ℝ, ¬ ($system))
      let proofSyntax ← `(fun $unknowns* ↦ fun $pattern ↦ $body)
      let proof ← liftTermElabM <| withProofBudget do
        let type ← elabType statement
        synthesizeSyntheticMVarsNoPostponing
        let proof ← withoutErrToSorry <| elabTermEnsuringType proofSyntax type
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars proof
      let report ← liftTermElabM <| withProofBudget do
        evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            "The system has no solution" proof]
      logReport ref {
        domain
        input := surfaceText input
        inputType := "polynomial system"
        output := "False"
        outputType := "equivalent real solution predicate"
      } #[computationNode "Gröbner basis" #[m!"the reduced basis is 1"], report]
  | .shape attempt result r solved =>
      let size := if attempt.form.isSome then n + 1 else n
      let last := size - 1
      -- The term `t`, the internal variables, and the position of each unknown.
      let tTerm : TSyntax `term ← match attempt.form with
        | none => pure (idents.getD (attempt.order.getD last 0) sTerm)
        | some form =>
            let linear := (List.range n).foldl (fun total v ↦
              add total (scale (form.getD v 0) (var n v))) []
            `(($(← polySyntax idents linear)))
      let internal : Array (TSyntax `term) := (Array.range size).map fun i ↦
        if i == last then tTerm else idents.getD (attempt.order.getD i 0) sTerm
      let position (v : Nat) : Nat := (attempt.order.toList.findIdx? (· == v)).getD v
      let univariateAt (arg : TSyntax `term) : Array (TSyntax `term) :=
        (Array.range size).map fun i ↦ if i == last then arg else arg
      let eliminant := result.poly r
      let tVar? : Option Nat := if attempt.form.isNone then attempt.order[last]? else none
      -- `g_v` for each unknown: the identity for `t` itself.
      let gOf (v : Nat) : Option Poly :=
        if tVar? == some v then none
        else (result.poly (solved.getD (position v) 0)).tail.map fun (mono, c) ↦ (mono, -c)
      let atArg (arg : TSyntax `term) (v : Nat) : CommandElabM (TSyntax `term) :=
        match gOf v with
        | none => pure arg
        | some g => polySyntax (univariateAt arg) g
      let conditionAt (arg : TSyntax `term) : CommandElabM (TSyntax `term) := do
        let mut parts : Array (TSyntax `term) := #[]
        for v in [0:n] do
          parts := parts.push (← `($(idents.getD v sTerm) = $(← atArg arg v)))
        match parts.toList.reverse with
        | [] => `(True)
        | lastPart :: rest => rest.foldlM (fun total e ↦ `($e ∧ $total)) lastPart
      let eliminantAt (arg : TSyntax `term) : CommandElabM (TSyntax `term) :=
        polySyntax (univariateAt arg) eliminant
      -- Forward: replay the derivation of the basis.
      let targets := r :: solved.toList
      let mut parts : Array (TSyntax `term) := #[← `(by linear_combination $(hyp "hg" r):term)]
      for v in [0:n] do
        parts := parts.push <| ← match gOf v with
          | none => `(by linear_combination)
          | some _ => `(by linear_combination $(hyp "hg" (solved.getD (position v) 0)):term)
      let mut forward ← `(⟨$parts,*⟩)
      for k in (result.closure targets).reverse do
        let node := result.nodes.getD k default
        if node.input && k < m then continue
        let terms := node.combo.map fun (j, c) ↦ (hyp "hg" j, c)
        let statement ← `($(← polySyntax internal node.poly) = 0)
        let name : TSyntax `ident := mkIdent (Name.mkSimple s!"hg{k}")
        forward ← `(have $name : $statement := $(← combination internal terms); $forward)
      let patterns := (List.range m).map fun k ↦ hyp "hg" k
      let pattern ← if m == 1 then pure patterns.head! else `(⟨$(patterns.toArray),*⟩)
      -- Backward: divide each equation by the basis.
      let hypothesisOf (k : Nat) : TSyntax `term :=
        if k == r then hyp "hr" 0
        else match (List.range n).find? (fun v ↦ (gOf v).isSome &&
            solved.getD (position v) 0 == k) with
          | some v => hyp "hq" v
          | none => hyp "hr" 0
      let mut backwardParts : Array (TSyntax `term) := #[]
      for k in [0:m] do
        let some (remainder, quotients) := reduce result.nodes targets (result.poly k)
          | throwErrorAt input "solve: the division by the basis exceeded its budget"
        unless remainder.isEmpty do
          throwErrorAt input "solve: an equation does not reduce to zero by the basis"
        backwardParts := backwardParts.push
          (← combination internal (quotients.map fun (j, c) ↦ (hypothesisOf j, c)))
      let backwardPattern ←
        `(⟨$(hyp "hr" 0), $((Array.range n).map fun v ↦ hyp "hq" v),*⟩)
      let backward ← if m == 1 then pure backwardParts[0]! else `(⟨$backwardParts,*⟩)
      let idealStatement ← `(∀ $unknowns* : ℝ, ($system) ↔
        $(← eliminantAt tTerm) = 0 ∧ $(← conditionAt tTerm))
      let idealProof ← `(fun $unknowns* ↦
        ⟨fun $pattern ↦ $forward, fun $backwardPattern ↦ $backward⟩)
      -- `t = s` on the roots: `t - s = ∑ c_v (v - g_v(s)) + q R(s)`.
      let form := attempt.form.getD ((Array.range n).map fun v ↦
        if tVar? == some v then 1 else 0)
      let difference := (List.range n).foldl (fun total v ↦
        let g := match gOf v with
          | some g => g
          | none => var size last
        add total (scale (form.getD v 0) g)) (scale (-1) (var size last))
      let some (rest, quotient) := reduce result.nodes [r] difference
        | throwErrorAt input "solve: the division by the eliminant exceeded its budget"
      unless rest.isEmpty do
        throwErrorAt input "solve: the separating form is not determined by the eliminant"
      let tauTerms := ((List.range n).filterMap fun v ↦
          if form.getD v 0 == 0 then none else some (hyp "hq" v, constant size (form.getD v 0)))
        ++ quotient.map fun (_, c) ↦ (hyp "hr" 0, c)
      let tauStatement ← `(∀ $unknowns* : ℝ, ∀ $(⟨sTerm.raw⟩) : ℝ,
        $(← eliminantAt sTerm) = 0 → $(← conditionAt sTerm) → $tTerm = $sTerm)
      let tauProof ← `(fun $unknowns* $(⟨sTerm.raw⟩) $(hyp "hr" 0)
        ⟨$((Array.range n).map fun v ↦ hyp "hq" v),*⟩ =>
          $(← combination (univariateAt sTerm) tauTerms))
      -- The real roots of the eliminant.
      let eliminantSyntax ← eliminantAt sTerm
      let poly : Verified.Expr.Alg.MvPoly 1 :=
        (univariateCoefficients size eliminant).zipIdx.filterMap fun (c, j) ↦
          if c == 0 then none else some (c, fun _ ↦ j)
      let expr := Verified.Expr.Alg.mvPolyExpr poly
      let data ← match Reduce.rootData poly with
        | .ok data => pure data
        | .error message => throwErrorAt input "solve: {message}"
      let k := data.locs.length
      let conditionS ← conditionAt sTerm
      let proof ← liftTermElabM <| withProofBudget do
        let elabProof (statement proof : TSyntax `term) : TermElabM Lean.Expr := do
          let type ← elabType statement
          synthesizeSyntheticMVarsNoPostponing
          let type ← instantiateMVars type
          let value ← withoutErrToSorry <| elabTermEnsuringType proof type
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars value
        let hideal ← elabProof idealStatement idealProof
        let htau ← elabProof tauStatement tauProof
        -- `∀ s, expr.eval ![s] = R s`, by the cleaning simp set and `ring`.
        let exprTerm ← exprToSyntax (← quoteVerifiedExpr expr)
        let bridgeStatement ← `(∀ $(⟨sTerm.raw⟩) : ℝ,
          CAS.Verified.Expr.eval ![$sTerm] $exprTerm = $eliminantSyntax)
        let bridgeType ← elabType bridgeStatement
        synthesizeSyntheticMVarsNoPostponing
        let bridgeType ← instantiateMVars bridgeType
        let context ← Simp.mkContext {}
          (simpTheorems := #[← Digits.cleanSimpTheorems (ratCastLemmas ++
            [``Matrix.cons_val_zero, ``Matrix.cons_val_fin_one, ``Rat.cast_pow])])
          (congrTheorems := ← getSimpCongrTheorems)
        let (simplified, _) ← simp bridgeType context #[← Simp.getSimprocs]
        let ringProof ← `(by intro $(⟨sTerm.raw⟩):ident; ring)
        let simplifiedProof ← if simplified.expr.isTrue then pure (Lean.mkConst ``True.intro)
          else withoutErrToSorry (elabTermEnsuringType ringProof simplified.expr)
        let hbridge ← match simplified.proof? with
          | none => pure simplifiedProof
          | some equality => mkEqMPR equality simplifiedProof
        let hsol ← mkAppM' (← Reduce.applyChecked ``solve_of_reduceCheck expr data) #[hbridge]
        let hsolTerm ← exprToSyntax hsol
        let hidealTerm ← exprToSyntax hideal
        let htauTerm ← exprToSyntax htau
        let locsTerm ← exprToSyntax (← Reduce.quoteLocs data.locs)
        let finalStatement ← `(∃ ρ : ℕ → ℝ, BoundsAll ρ 0 $locsTerm ∧ ∀ $unknowns* : ℝ,
          ($system) ↔ PointsFormula (rootVal ρ $locsTerm)
            (fun $(⟨sTerm.raw⟩):ident : ℝ ↦ $conditionS) 0 ($locsTerm).length)
        let finalProof ← `(by
          obtain ⟨ρ, hb, hp⟩ := $hsolTerm
          exact ⟨ρ, hb, fun $unknowns* ↦ ($hidealTerm $unknowns*).trans
            (hp $tTerm (fun $(⟨sTerm.raw⟩):ident : ℝ ↦ $conditionS) ($htauTerm $unknowns*))⟩)
        let proof ← elabProof finalStatement finalProof
        Digits.cleanProof proof (ratCastLemmas ++ [``Rat.cast_pow, ``true_and, ``and_true,
          ``false_or, ``or_false, ``iff_false, ``List.length_cons, ``List.length_nil,
          ``List.getD_cons_zero, ``List.getD_cons_succ, ``exists_const])
          [``BoundsAll, ``RootLoc.Bounds, ``PointsFormula, ``rootVal, ``RootLoc.value]
          (simprocs := true)
      -- One kernel check of the whole proof; the report then inspects a single theorem
      -- instead of every lemma the proof mentions.
      let proof ← liftTermElabM <| withProofBudget do
        let proof ← Digits.evaluateNumerals proof
        CAS.Tactic.Explanation.kernelCheckedProof "solve" (← inferType proof) proof
      let report ← liftTermElabM <| withProofBudget do
        evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            "Complete list of real solutions" proof]
      -- The report: the points, exact or in decimals.
      let coefficientsOf (g : Poly) : List ℚ := univariateCoefficients size g
      let points := (List.range k).map fun j ↦
        let loc := data.locs.getD j default
        let coordinates := (List.range n).map fun v ↦
          let name := renderName names[v]!
          match loc, gOf v with
          | .exact q, none => s!"{name} = {q}"
          | .exact q, some g => s!"{name} = {FullSimplify.evalCoefficients (coefficientsOf g) q}"
          | .interval lo hi, none => s!"{name} = {renderRoot 20 (lo, hi)}…"
          | .interval lo hi, some g =>
              let (a, b) := evalOn (coefficientsOf g) lo hi
              s!"{name} ≈ {approx ((a + b) / 2)}"
        "{" ++ ", ".intercalate coordinates ++ "}"
      let output := if points.isEmpty then "False" else ", ".intercalate points
      let tName := match attempt.form with
        | none => renderName names[attempt.order.getD last 0]!
        | some form => s!"the separating form {formText names form}"
      logReport ref {
        domain
        input := surfaceText input
        inputType := "polynomial system"
        output
        outputType := "complete list of real solutions"
      } #[computationNode "Gröbner basis" #[
          m!"lexicographic basis in shape position with respect to {tName}; eliminant of \
            degree {(coefficientsOf eliminant).length - 1}, {k} real roots, \
            {(result.closure targets).length} polynomials in the derivation"],
        report]

end CAS.Command.PolySystems

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [solve $x:ident, $xs:ident,*] $system:term) =>
      PolySystems.logPolySystem system (#[x] ++ xs.getElems) system

end CAS.Command
