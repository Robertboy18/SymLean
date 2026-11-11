/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.LinearAlgebra.RowReduce
public import CAS.Command.RootSplit
public import CAS.Analysis.Matrix.Spectrum
public meta import CAS.Calculus.LinearODERoots
public meta import CAS.Analysis.Matrix.Spectrum
public meta import CAS.Tactic.RouteRegistry

/-!
# Characteristic polynomials, eigenvalues and eigenvectors

The modes `#cas [characteristicPolynomial]`, `#cas [eigenvalues]` and `#cas [eigenvectors]`, for
a square matrix `A` with rational entries:

* `characteristicPolynomial` proves `A.charpoly = p` in `ℚ[X]` (Mathlib's convention
  `det (X I - A)`, Mathematica's `CharacteristicPolynomial[A, x]` is `det (A - x I)`, which differs
  by `(-1) ^ n`): by evaluation (`Polynomial.funext`), `Matrix.eval_charpoly`, the characteristic
  matrix at `t` as a literal and `norm_det`;
* `eigenvalues` proves `A.charpoly = (X - λ₁) ^ m₁ ⋯ (X - λₖ) ^ mₖ` when every eigenvalue is
  rational, and otherwise the whole spectrum of the matrix `M` with the entries of `A` over
  `K = ℝ` (every eigenvalue real) or `K = ℂ`: `spectrum K M = {μ₁, …, μₛ}`, each eigenvalue once,
  and `M.charpoly.roots = {μ₁, …}` with algebraic multiplicities;
* `eigenvectors` proves a basis of the eigenspace of every eigenvalue: for a rational eigenvalue
  `λ`, the null space statement of `#cas [nullSpace]` (membership, linear independence,
  spanning) for `A - λ • 1`; for each of the remaining factors `q` of the characteristic
  polynomial, left after the rational roots that the search finds, the same statement for
  `M - α • 1` and every root `α` of `q` in `K`, where `M` is the matrix with the entries of `A`
  over `K` and the vectors have entries that are polynomials in `α` with rational coefficients.
  Here `K = ℝ` when a certificate shows that every root of `q` is real, and then the statement
  also says that `q` splits over `ℝ`; otherwise `K = ℂ`. It adds the factorization of the
  characteristic polynomial into the factors `X - λ` and `q`.

## Implementation notes

The coefficients of the characteristic polynomial come from the Faddeev-LeVerrier recursion
`QMatrix.charpoly` of `CAS/Command/LinearAlgebra/Basic.lean`; the proof by evaluation checks
them, so the recursion is never trusted. `CAS.Command.RootSplit.split` of
`CAS/Command/RootSplit.lean` splits the characteristic polynomial into rational roots, the roots
`α ± c √m` of quadratic factors, and squarefree factors (from the squarefree decomposition
`squareFreeFactors?` of `CAS/Polynomial/Sparse/Euclidean.lean`, or from the registered factor
provider) whose roots `RootSplit.enclose` encloses: the real roots in rational intervals and the
complex roots in discs. The statement names these `let r₁ := AlgRoot.real R lo hi` and
`let z₁ := AlgRoot.complex R u v ρ` and states their enclosures and `R r₁ = 0`. The kernel decides
`CAS.Analysis.Matrix.eigenCheck` (every factor checks and their product is the characteristic
polynomial), and `spectrum_real_of` or `spectrum_complex_of` of
`CAS/Analysis/Matrix/Spectrum.lean` gives the statement.

With `CASHex` we ask Hex whether the enclosed factors of `eigenvalues` and the factors `q` of
`eigenvectors` are irreducible over `ℚ`. The statement says so for each factor whose
irreducibility Hex certifies, and the report lists the other factors that we asked about; we do
not ask about the quadratic factors of `eigenvalues`. Without `CASHex` the statement has no
`Irreducible` conjunct and the report lists no factor. The planner metadata of the report names
the route that answered.

For a rational eigenvalue `λ` the eigenspace is the null space of `A - λ • 1`, from `rowReduce`
and `nullSpaceProof` of `CAS/Command/LinearAlgebra/RowReduce.lean`.

We find the eigenvectors for the roots of a factor `q` by Gauss-Jordan elimination of `A - X I`
over `ℚ[X]/(q)` (`eliminateModulo`), with the inverse of a pivot from its extended gcd with `q`.
When `q` is irreducible, as with `CASHex`, this ring is a field. Otherwise a nonzero entry `p` may
fail to be a unit; then `gcd(p, q)` is a proper factor of `q`, and we start again on it and on its
cofactor (`eigenbases`). The elimination is untrusted search. Its result (`Eigenbasis`) is a
certificate of identities in `ℚ[X]`: `(A - X I) V i = q W i` for the vectors `V i`, and
`E r (A - X I) = T r + q S r` for the rows `E r` of the elimination, with rational vectors `W i`
and `S r`. At a root `α` of `q` they are the hypotheses of
`CAS.Analysis.Matrix.eigenspace_basis`, polynomial identities in `α` that `ring1` proves
coordinate by coordinate, so that one proof covers every root of `q`. We check the dimensions of
the certificate and its pivot columns before its identities.

The statement for `q` is over `ℝ` when `realCertificate?` finds a certificate that every root of
`q` is real: the roots `α ± √Δ` of a quadratic with `Δ > 0`, or enclosures from
`RootSplit.enclose` without a complex disc. The kernel decides
`CAS.Analysis.Matrix.EigFactor.realCheck` of the certificate, and
`EigFactor.splits_of_realCheck` turns it into the statement that `q` splits over `ℝ`, so that
the real roots of `q` are all its roots. Without a certificate the statement is over `ℂ`.

The search for rational roots has a bisection budget, and when it runs out a remaining factor
may still have rational roots. A part of degree one that the elimination splits off is then a
rational eigenvalue, which joins the others with the null space statement over `ℚ`.
-/

public meta section

namespace CAS.Command.LinearAlgebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (natTerm ratText proveStatement qPolyTerm denseText Dense
  polynomialIdentityTactic)
open CAS.Command.RootSplit (enclosureParts ratQ natLit rootSyntax listSyntax boundQ decimal
  letRoots certified)
open CAS.Analysis.Matrix (EigFactor)

/-- The characteristic matrix `t I - A` as a literal in the variable `t`. -/
def characteristicMatrixTerm (A : QMatrix) (t : TSyntax `ident) : TermElabM (TSyntax `term) := do
  let n := A.rows
  let rows ← (List.range n).toArray.mapM fun i ↦ do
    let entries ← (List.range n).toArray.mapM fun j ↦ do
      let a := A.get i j
      if i = j then
        if a = 0 then `(($t : ℚ)) else `(($t : ℚ) - $(← ratTerm a))
      else ratTerm (-a)
    `(![$entries,*])
  `((Matrix.of ![$rows,*] : Matrix (Fin $(natTerm n)) (Fin $(natTerm n)) ℚ))

/-- The tactic proving `At.charpoly = P` for a term `At` denoting the literal `A` (by default the
literal itself) and any `P` equal to the characteristic polynomial; with `ofCoeffList`, also for
`P = Polynomial.ofCoeffList [a₀, …, aₙ]`. -/
def charpolyTactic (A : QMatrix) (At? : Option (TSyntax `term) := none)
    (ofCoeffList : Bool := false) : TermElabM (TSyntax `tactic) := do
  let n := A.rows
  let t := mkIdent `t
  let At ← match At? with
    | some At => pure At
    | none => matrixTerm A n n
  let Ct ← characteristicMatrixTerm A t
  let expand ← if ofCoeffList then
      `(tactic| simp only [norm_det, Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_zero])
    else `(tactic| simp only [norm_det])
  `(tactic| (
    apply Polynomial.funext
    intro $t:ident
    rw [Matrix.eval_charpoly, show Matrix.scalar (Fin $(natTerm n)) $t - $At = $Ct by
      ext i j; fin_cases i <;> fin_cases j <;> simp]
    $expand:tactic
    first | ring1 | (simp; ring1)))

/-- Run `#cas [characteristicPolynomial] A`. -/
def logCharpoly (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do
    throwErrorAt input "characteristicPolynomial: the matrix must be square"
  let p := A.charpoly
  let (proposition, proof) ← liftTermElabM do
    proveStatement "characteristicPolynomial"
      (← `(Matrix.charpoly $(← matrixTerm A A.rows A.rows) = $(← qPolyTerm p)))
      (← charpolyTactic A)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := denseText "x" p
    outputType := "det (x I - A)"
  } #[← evidence "characteristicPolynomial" "Characteristic polynomial in ℚ[X]" proposition
      proof]

/-- The factorization `∏ (X - λ) ^ m * ∏ q ^ k` as a term of `ℚ[X]`, for the rational roots `λ`
and the other `factors` `q`, with their multiplicities. -/
def factoredTerm (roots : List (ℚ × Nat)) (factors : List (Dense × Nat)) :
    TermElabM (TSyntax `term) := do
  let mut parts : Array (TSyntax `term) := #[]
  for (r, m) in roots do
    let linear ← qPolyTerm #[-r, 1]
    parts := parts.push (← if m = 1 then `(($linear)) else `(($linear) ^ $(natTerm m)))
  for (q, k) in factors do
    let factor ← qPolyTerm q
    parts := parts.push (← if k = 1 then `(($factor)) else `(($factor) ^ $(natTerm k)))
  if parts.isEmpty then return ← `((1 : Polynomial ℚ))
  let mut out := parts[0]!
  for p in parts[1:] do
    out ← `($out * $p)
  return out

/-- Text of the rational eigenvalues with multiplicities. -/
def eigenvaluesText (roots : List (ℚ × Nat)) : String :=
  "[" ++ ", ".intercalate (roots.flatMap fun (r, m) ↦ List.replicate m (ratText r)) ++ "]"

/-- `|c| √m` as text: `√5/2`, `3√2`, `2/3`. -/
def surdText (c : ℚ) (m : Nat) : String :=
  let p := c.num.natAbs
  let root := if m = 1 then "" else s!"√{m}"
  let body := if m = 1 then toString p else if p = 1 then root else s!"{p}{root}"
  if c.den = 1 then body else s!"{body}/{c.den}"

/-- `|c| √m i` as text: `i`, `2i`, `i√3/2`. -/
def imaginaryText (c : ℚ) (m : Nat) : String :=
  let p := c.num.natAbs
  let root := if m = 1 then "" else s!"√{m}"
  let body := if p = 1 then s!"i{root}" else s!"{p}i{root}"
  if c.den = 1 then body else s!"{body}/{c.den}"

/-- `α + t` (`plus`) or `α - t` as text, `t` or `-t` when `α = 0`. -/
def offsetText (α : ℚ) (plus : Bool) (t : String) : String :=
  if α = 0 then (if plus then t else "-" ++ t)
  else s!"{ratText α} {if plus then "+" else "-"} {t}"

/-- The term `(q : ℝ)`. -/
def realTerm (q : ℚ) : TermElabM (TSyntax `term) := do `(($(← ratSyntax q) : ℝ))

/-- `a + b √n` as a term of `ℝ`, `a`, `b` or `√n` alone where they can be. -/
def surdTerm (a b : ℚ) (n : Nat) : TermElabM (TSyntax `term) := do
  if n = 1 then return ← realTerm (a + b)
  let root ← `(Real.sqrt $(⟨Syntax.mkNumLit (toString n)⟩))
  let magnitude := if b < 0 then -b else b
  let scaled ← if magnitude = 1 then pure root else `($(← realTerm magnitude) * $root)
  if a = 0 then
    if b < 0 then `(-$scaled) else pure scaled
  else if b < 0 then `($(← realTerm a) - $scaled) else `($(← realTerm a) + $scaled)

/-- `α + c √n i` (`plus`) or `α - c √n i` as a term of `ℂ`, for `c > 0`. -/
def complexTerm (α c : ℚ) (n : Nat) (plus : Bool) : TermElabM (TSyntax `term) := do
  let root ← `(((Real.sqrt $(⟨Syntax.mkNumLit (toString n)⟩) : ℝ) : ℂ))
  let cT ← ratSyntax c
  let magnitude ← do
    if n = 1 then
      if c = 1 then `(Complex.I) else `(($cT : ℂ) * Complex.I)
    else if c = 1 then `($root * Complex.I)
    else `(($cT : ℂ) * $root * Complex.I)
  if α = 0 then
    if plus then pure magnitude else `(-$magnitude)
  else if plus then `(($(← ratSyntax α) : ℂ) + $magnitude)
  else `(($(← ratSyntax α) : ℂ) - $magnitude)

/-- The coefficient list `R` as a term of `List ℚ`. -/
def coeffsTerm (R : List ℚ) : TermElabM (TSyntax `term) := do
  `(($(← listSyntax (← R.toArray.mapM ratQ)) : List ℚ))

/-- The factor as a term of `CAS.Analysis.Matrix.EigFactor`. -/
def factorSyntax : EigFactor → TermElabM (TSyntax `term)
  | .char ρ => do `(CAS.Analysis.Matrix.EigFactor.char $(← rootSyntax ρ))
  | .enclosed R D => do
    let realsT ← listSyntax (← D.reals.toArray.mapM fun (lo, hi) ↦ do
      `(($(← boundQ lo), $(← boundQ hi))))
    let discsT ← listSyntax (← D.discs.toArray.mapM fun (u, v, ρ, κ, Rb, L) ↦ do
      `(($(← boundQ u), $(← boundQ v), $(← boundQ ρ), $(← ratQ κ), $(← ratQ Rb), $(← ratQ L))))
    `(CAS.Analysis.Matrix.EigFactor.enclosed $(← coeffsTerm R)
      (⟨$realsT, $discsT⟩ : CAS.LinearODE.Enclosures))

/-- An eigenvalue: the term that `rootList` or `realRootList` unfolds to, the term of the
statement, the tactic proving the two equal, and its text. -/
abbrev Member := TSyntax `term × TSyntax `term × TSyntax `tactic × String

/-- The roots of the factor `f`, each once, over `ℝ` (`real`) or `ℂ`. The enclosed roots are
named `r₍ᵢ₎` and `z₍ⱼ₎` after the `reals` real roots and `discs` discs of the earlier factors, as
`RootSplit.letRoots` names them. -/
def memberTerms (real : Bool) (reals discs : Nat) (f : EigFactor) :
    TermElabM (Array Member) := do
  let tac ← `(tactic| ((push_cast [CAS.LinearODE.CharRoot.width, Real.sqrt_one]) <;> ring_nf))
  let toC (t : TSyntax `term) : TermElabM (TSyntax `term) := `((($t : ℝ) : ℂ))
  match f with
  | .char (.real r) =>
    let raw ← `(($(← ratQ r) : ℝ))
    if real then return #[(raw, ← realTerm r, tac, ratText r)]
    return #[(← toC raw, ← `(($(← ratSyntax r) : ℂ)), tac, ratText r)]
  | .char (.realPair α c m) =>
    let n := m.num.toNat
    let αT ← `(($(← ratQ α) : ℝ))
    let w ← `(CAS.LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m))
    let members : Array Member := #[
      (← `($αT + $w), ← surdTerm α c n, tac, offsetText α (c > 0) (surdText c n)),
      (← `($αT - $w), ← surdTerm α (-c) n, tac, offsetText α (c < 0) (surdText c n))]
    if real then return members
    members.mapM fun (raw, nice, t, text) ↦ do return (← toC raw, ← toC nice, t, text)
  | .char (.pair α c m) =>
    let n := m.num.toNat
    let αT ← `((($(← ratQ α) : ℝ) : ℂ))
    let w ← `(((CAS.LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m) : ℝ) : ℂ))
    let im := imaginaryText c n
    return #[(← `($αT + $w * Complex.I), ← complexTerm α c n true, tac, offsetText α true im),
      (← `($αT - $w * Complex.I), ← complexTerm α c n false, tac, offsetText α false im)]
  | .enclosed R D =>
    let RT ← coeffsTerm R
    let refl ← `(tactic| rfl)
    let mut out : Array Member := #[]
    for ((lo, hi), i) in D.reals.zipIdx do
      let r ← `(CAS.AlgRoot.real $RT $(← boundQ lo) $(← boundQ hi))
      let t ← if real then pure r else toC r
      out := out.push (t, t, refl, s!"r{Nat.toSubscriptString (reals + i + 1)}")
    for ((u, v, ρ, _), j) in D.discs.zipIdx do
      let z ← `(CAS.AlgRoot.complex $RT $(← boundQ u) $(← boundQ v) $(← boundQ ρ))
      let conj ← `((starRingEnd ℂ) $z)
      let name := s!"z{Nat.toSubscriptString (discs + j + 1)}"
      out := (out.push (z, z, refl, name)).push (conj, conj, refl, "conj " ++ name)
    return out

/-- The proof of `fn fs = [nice₁, …]` over `K`: the kernel unfolds `fn fs` to the raw terms of
the `members` (`Eq.refl`, not run by the elaborator), and their tactics prove each raw term equal
to its term in the statement. -/
def listEq (K fn fsT : TSyntax `term) (members : Array Member) : TermElabM (TSyntax `term) := do
  let raws := members.map (·.1)
  let nices := members.map (·.2.1)
  let rawList ← `(([$raws,*] : List $K))
  let niceList ← `(([$nices,*] : List $K))
  let l ← elabTerm (← `($fn $fsT)) none
  let r ← elabTerm rawList none
  synthesizeSyntheticMVarsNoPostponing
  let l ← instantiateMVars l
  let r ← instantiateMVars r
  let unfolded ← exprToSyntax (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r))
  let mut proof ← `(rfl)
  for m in members.reverse do
    let tac := m.2.2.1
    proof ← `(congrArg₂ List.cons (by $tac:tactic) $proof)
  `(($unfolded).trans (show $rawList = $niceList from $proof))

/-- The finite set or multiset `{x₁, …, xₖ}` of type `S`, for `k ≥ 1`. -/
def finiteTerm (xs : Array (TSyntax `term)) (S : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut acc ← `((Singleton.singleton $(xs.back!) : $S))
  for x in xs.pop.reverse do
    acc ← `(Insert.insert $x $acc)
  return acc

/-- The spectrum statement of `A` from the factors `fs` of its characteristic polynomial, after
the enclosures of the enclosed eigenvalues and the theorems `facts` (proposition and proof), with
its proof, the texts of the eigenvalues with multiplicities and the texts of the enclosures. -/
def spectrumProof (A : QMatrix) (fs : List (EigFactor × Nat))
    (facts : Array (Lean.Expr × Lean.Expr)) :
    TermElabM (Lean.Expr × Lean.Expr × Array String × Array String) := do
  let n := A.rows
  let real := fs.all (·.1.isReal)
  let At ← matrixTerm A n n
  let aT ← coeffsTerm A.charpoly.toList
  let factorTerms ← fs.toArray.mapM fun (f, k) ↦ do `(($(← factorSyntax f), $(← natLit k)))
  let fsT ← `(($(← listSyntax factorTerms) : List (CAS.Analysis.Matrix.EigFactor × ℕ)))
  let hcheck ← certified (← if real then `(CAS.Analysis.Matrix.eigenCheckReal $aT $fsT = true)
    else `(CAS.Analysis.Matrix.eigenCheck $aT $fsT = true))
  let K ← if real then `(ℝ) else `(ℂ)
  let MK ← matrixTermOver A K
  let castRows ← A.mapM fun row ↦ do
    let entries ← row.mapM fun a ↦ do `((($(← ratSyntax a) : ℚ) : $K))
    `(![$entries,*])
  let castM ← `(![$castRows,*])
  let mut distinct : Array Member := #[]
  let mut members : Array Member := #[]
  let mut statements : Array (TSyntax `term) := #[]
  let mut proofs : Array (TSyntax `term) := #[]
  let mut notes : Array String := #[]
  let mut reals := 0
  let mut discs := 0
  for (f, k) in fs do
    let ms ← memberTerms real reals discs f
    distinct := distinct ++ ms
    for m in ms do
      for _ in [0:k] do
        members := members.push m
    let .enclosed R D := f | continue
    let (s, p) ← enclosureParts R.toArray D (← coeffsTerm R)
    statements := statements ++ s
    proofs := proofs ++ p
    for ((lo, hi), i) in D.reals.zipIdx do
      notes := notes.push
        s!"r{Nat.toSubscriptString (reals + i + 1)} ∈ ({decimal lo}, {decimal hi})"
    for ((u, v, ρ, _), j) in D.discs.zipIdx do
      let z := s!"z{Nat.toSubscriptString (discs + j + 1)}"
      notes := notes.push s!"{z}, conj {z} = α ± iβ, α ∈ [{decimal (u - ρ)}, \
        {decimal (u + ρ)}], β ∈ [{decimal (v - ρ)}, {decimal (v + ρ)}]"
    reals := reals + D.reals.length
    discs := discs + D.discs.length
  let listFn ← if real then `(CAS.Analysis.Matrix.realRootList)
    else `(CAS.Analysis.Matrix.rootList)
  let distinctFn ← if real then `(CAS.Analysis.Matrix.factorRealRoots)
    else `(CAS.Analysis.Matrix.factorRoots)
  let hL ← listEq K listFn fsT members
  let hD ← listEq K distinctFn fsT distinct
  let specT ← `(spectrum $K $MK = $(← finiteTerm (distinct.map (·.2.1)) (← `(Set $K))))
  let rootsT ← `((Matrix.charpoly $MK).roots =
    $(← finiteTerm (members.map (·.2.1)) (← `(Multiset $K))))
  let factsT ← facts.mapM fun (p, _) ↦ exprToSyntax p
  let factProofs ← facts.mapM fun (_, q) ↦ exprToSyntax q
  let statement ← (statements ++ factsT).foldrM (fun e acc ↦ `($e ∧ $acc))
    (← `($specT ∧ $rootsT))
  let thm := mkIdent (if real then ``CAS.Analysis.Matrix.spectrum_real_of
    else ``CAS.Analysis.Matrix.spectrum_complex_of)
  -- The characteristic polynomial and the cast matrix are proved first, as closed terms. As
  -- `have`s of the main proof, their proofs would stay in the local context of each later `by`
  -- block, and every one of those would instantiate them again.
  let hA ← exprToSyntax (← proveStatement "eigenvalues"
    (← `(Matrix.charpoly $At = Polynomial.ofCoeffList $aT)) (← charpolyTactic A none true)).2
  let hM ← exprToSyntax (← proveStatement "eigenvalues"
    (← `(Matrix.map $At ((↑) : ℚ → $K) = $MK)) (← `(tactic| (
      rw [CAS.Analysis.Matrix.map_of_eq]
      change Matrix.of $castM = _
      norm_num)))).2
  let setTac ← if distinct.size = 1 then
      `(tactic| simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_singleton_iff])
    else `(tactic| simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff])
  let parts := proofs ++ factProofs ++ #[← `(?_), ← `(hr)]
  let proofT ← `(by
    obtain ⟨hs, hr⟩ := $thm $hA $hM $hcheck $hL $hD
    refine ⟨$parts,*⟩
    rw [hs]
    ext μ
    $setTac:tactic)
  let proof ← CAS.Command.elabCheckedProof "eigenvalues" statement proofT
  let type ← letRoots (← inferType proof)
  return (type, ← mkExpectedTypeHint proof type, members.map (·.2.2.2), notes)

/-- The coprime integer coefficients of the nonzero polynomial `R`, lowest degree first, with a
positive leading coefficient. -/
def integerCoefficients (R : Dense) : List Int :=
  (Dense.ofSparse (Algebra.primitivePart (Dense.toSparse R)).2).toList.map (·.num)

/-- Run `x` under a budget of at least one million heartbeats, for the elaborator and for the
kernel checks that `x` runs; `maxHeartbeats 0`, no limit, stays unlimited. The `ring1` and
`linear_combination` steps of a spectrum proof grow with the size of the matrix. -/
def withSpectrumBudget {α : Type} (x : TermElabM α) : TermElabM α := do
  let option := maxHeartbeats.get (← getOptions)
  let budget := if option == 0 then 0 else max option 1000000
  withOptions (fun options ↦ maxHeartbeats.set options budget) <|
    withTheReader Core.Context (fun context ↦ { context with maxHeartbeats := budget * 1000 }) <|
      withCurrHeartbeats x

/-- The report line that lists the factors without a Hex irreducibility certificate, if there are
any. -/
def uncertifiedLine (factors : Array String) : Array (String × String) :=
  if factors.isEmpty then #[]
  else #[("Factors without a Hex irreducibility certificate", ", ".intercalate factors.toList)]

/-- Kernel-check a proved proposition and build the report's evidence, with the route that
answered as planner metadata: the `CASHex` backend (`backend`) or the core route. -/
def eigenEvidence (operation label : String) (backend : Bool) (proposition proof : Lean.Expr) :
    TermElabM MessageData := do
  let checked ← CAS.Tactic.Explanation.kernelCheckedProof operation proposition proof
  evidenceReportMessage #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof label checked]
    (plannerMetadata := #[{
      label := if backend then s!"CASHex backend of {operation}" else s!"core route of {operation}"
      status := .selected }])

/-- Report the spectrum of `A` from the split `s` of its characteristic polynomial, whose rational
roots are `roots`: the roots of the quadratic factors in closed form and the roots of each
enclosed factor named by their enclosures. With `irreducible?` (from the `CASHex` backend), we ask
it about each enclosed factor, from its integer coefficients, and not about the quadratic
factors: the statement says that each factor it proves irreducible over `ℚ` is irreducible, and
the report lists the other enclosed factors. Without `irreducible?`, as on the core route, the
statement has no `Irreducible` conjunct and the report lists no factor. The proof and its kernel
check run under `withSpectrumBudget`. -/
def logSpectrum (ref input : Syntax) (A : QMatrix) (s : RootSplit.Split)
    (roots : List (ℚ × Nat))
    (irreducible? : Option (List Int → CommandElabM (Option (Lean.Expr × Lean.Expr)))) :
    CommandElabM Unit := do
  let mut fs : List (EigFactor × Nat) := roots.map fun (r, k) ↦ (EigFactor.char (.real r), k)
  for (ρ, k) in s.exact do
    match ρ with
    | .realPair α γ m => fs := fs ++ [(EigFactor.char (.realPair α (-γ) m), k)]
    | .pair .. => fs := fs ++ [(EigFactor.char ρ, k)]
    | .real _ => pure ()
  let mut facts : Array (Lean.Expr × Lean.Expr) := #[]
  let mut uncertified : Array String := #[]
  for (R, k) in s.enclosed do
    let D ← match RootSplit.enclose R with
      | .ok D => pure D
      | .error msg => throwErrorAt input "eigenvalues: {msg}"
    fs := fs ++ [(EigFactor.enclosed R.toList D, k)]
    if let some irreducible := irreducible? then
      match ← irreducible (integerCoefficients R) with
      | some fact => facts := facts.push fact
      | none => uncertified := uncertified.push (denseText "X" R)
  let (type, proof, texts, notes) ← liftTermElabM <| withSpectrumBudget <|
    spectrumProof A fs facts
  let report ← liftTermElabM <| withSpectrumBudget <|
    eigenEvidence "eigenvalues" "The spectrum with algebraic multiplicities" irreducible?.isSome
      type proof
  let enclosures := if notes.isEmpty then "" else "; " ++ ", ".intercalate notes.toList
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := "[" ++ ", ".intercalate texts.toList ++ "]" ++ enclosures
    outputType := "eigenvalues with multiplicity"
    furtherResults := uncertifiedLine uncertified
  } #[report]

/-- A matrix with entries in `ℚ[X]`, by rows. -/
abbrev PolyMatrix := Array (Array Dense)

/-- The remainder of `p` modulo `q`. -/
def reduceModulo (q p : Dense) : Dense := (Dense.divMod p q).2

/-- The matrix `A - X I` with entries in `ℚ[X]`. -/
def shiftedMatrix (A : QMatrix) : PolyMatrix :=
  A.mapIdx fun i row ↦ row.mapIdx fun j a ↦ Dense.trim (if i = j then #[a, -1] else #[a])

/-- The outcome of Gauss-Jordan elimination over `ℚ[X]/(q)`. -/
inductive Elimination where
  /-- The reduced rows `R`, the rows `E` with `E B = R` modulo `q`, and the pivot columns. -/
  | reduced (R E : PolyMatrix) (pivots : Array Nat)
  /-- A proper monic factor of `q`: the gcd of `q` and an entry that is not a unit. -/
  | split (g : Dense)

/-- Gauss-Jordan elimination of `B` over `ℚ[X]/(q)`, with the first nonzero entry of each column
as its pivot and the inverse of the pivot from its extended gcd with `q`. A nonzero pivot that is
not a unit stops it with the proper factor `gcd(pivot, q)` of `q`. -/
def eliminateModulo (q : Dense) (B : PolyMatrix) : Elimination := Id.run do
  let n := B.size
  let cols := (B.getD 0 #[]).size
  let mut R := B.map (·.map (reduceModulo q))
  let mut E : PolyMatrix := Array.ofFn fun (i : Fin n) ↦ Array.ofFn fun (j : Fin n) ↦
    if i = j then #[1] else #[]
  let mut pivots : Array Nat := #[]
  let mut row := 0
  for col in [0:cols] do
    if row ≥ n then break
    let some p := (List.range (n - row)).map (· + row) |>.find? fun i ↦
        !(R[i]!.getD col #[]).isEmpty
      | continue
    let (g, s, _) := Dense.xgcd (R[p]!.getD col #[]) q
    if g != #[1] then return .split g
    let inverse := reduceModulo q s
    let rp := R[p]!
    let rr := R[row]!
    R := (R.set! p rr).set! row rp
    let ep := E[p]!
    let er := E[row]!
    E := (E.set! p er).set! row ep
    R := R.set! row (R[row]!.map fun e ↦ reduceModulo q (Dense.mul inverse e))
    E := E.set! row (E[row]!.map fun e ↦ reduceModulo q (Dense.mul inverse e))
    for i in [0:n] do
      if i = row then continue
      let f := R[i]!.getD col #[]
      if f.isEmpty then continue
      R := R.set! i ((R[i]!.zip R[row]!).map fun (a, b) ↦
        reduceModulo q (Dense.sub a (Dense.mul f b)))
      E := E.set! i ((E[i]!.zip E[row]!).map fun (a, b) ↦
        reduceModulo q (Dense.sub a (Dense.mul f b)))
    pivots := pivots.push col
    row := row + 1
  return .reduced R E pivots

/-- `B v` in `ℚ[X]`. -/
def polyMulVec (B : PolyMatrix) (v : Array Dense) : Array Dense :=
  B.map fun row ↦ (row.zip v).foldl (fun s (a, b) ↦ Dense.add s (Dense.mul a b)) #[]

/-- `v B` in `ℚ[X]`, for a row vector `v`. -/
def polyVecMul (v : Array Dense) (B : PolyMatrix) : Array Dense :=
  (Array.range (B.getD 0 #[]).size).map fun j ↦
    (v.zip B).foldl (fun s (a, row) ↦ Dense.add s (Dense.mul a (row.getD j #[]))) #[]

/-- The rational `c` with `p = c q`, if there is one. -/
def constantQuotient? (q p : Dense) : Option ℚ :=
  let (s, r) := Dense.divMod p q
  if r.isEmpty && s.size ≤ 1 then some (s.getD 0 0) else none

/-- A basis of the eigenspace of `A` for every root of a monic factor `q` of its characteristic
polynomial, with the certificate of `CAS.Analysis.Matrix.eigenspace_basis`. -/
structure Eigenbasis where
  /-- The monic factor `q`. -/
  factor : Dense
  /-- Its multiplicity in the characteristic polynomial. -/
  multiplicity : Nat
  /-- A certificate that every root of `q` is real (`realCertificate?`), if there is one. -/
  certificate : Option EigFactor
  /-- The vectors `V i`, with entries of degree less than that of `q`. -/
  basis : PolyMatrix
  /-- The rational vectors `W i` with `(A - X I) V i = q W i`. -/
  defect : Array (Array ℚ)
  /-- The rows `E r` of the elimination, one for each pivot. -/
  rows : PolyMatrix
  /-- The reduced rows `T r`. -/
  reduced : PolyMatrix
  /-- The rational vectors `S r` with `E r (A - X I) = T r + q S r`. -/
  remainder : Array (Array ℚ)
  /-- The free columns: `V i` is `1` at the `i`-th one and `0` at the others. -/
  free : Array Nat
  /-- The pivot columns: `T r` is `1` at the `r`-th one and `0` at the others. -/
  pivots : Array Nat

/-- Whether the statement for `b` is over `ℝ`: whether there is a certificate that every root of
its factor is real. -/
def Eigenbasis.real (b : Eigenbasis) : Bool := b.certificate.isSome

/-- The certificate that every root of the monic squarefree polynomial `q` of degree at least two
is real, if there is one: the roots `α ± √Δ` of a quadratic with `Δ > 0`, or the enclosures of
`RootSplit.enclose` when they have no complex disc. The kernel checks it with
`CAS.Analysis.Matrix.EigFactor.realCheck`. -/
def realCertificate? (q : Dense) : Option EigFactor :=
  match Dense.degree q with
  | 0 | 1 => none
  | 2 =>
    let α := -(q.getD 1 0) / 2
    let Δ := α * α - q.getD 0 0
    if q.size = 3 ∧ q.getD 2 0 = 1 ∧ 0 < Δ then some (.char (.realPair α 1 Δ)) else none
  | _ => match RootSplit.enclose q with
    | .ok D => if D.discs.isEmpty then some (.enclosed q.toList D) else none
    | .error _ => none

/-- The basis for the roots of `q` (of multiplicity `k`) and its certificate, from the
elimination of `A - X I` over `ℚ[X]/(q)` with reduced rows `R`, rows `E` and pivot columns
`pivots`. We check that `R` and `E` are `n × n` for `A` of size `n` and that the pivot columns
increase and are below `n`, then the identities of the certificate, in exact arithmetic over `ℚ`,
and the dimensions of its parts. -/
def eigenbasisOf (A : QMatrix) (q : Dense) (k : Nat) (R E : PolyMatrix) (pivots : Array Nat) :
    Except String Eigenbasis := do
  let n := A.rows
  unless A.all (·.size == n) && R.size == n && R.all (·.size == n) && E.size == n &&
      E.all (·.size == n) do
    throw "the elimination has the wrong dimensions"
  let B := shiftedMatrix A
  let m := pivots.size
  unless m ≤ n && pivots.all (· < n) &&
      (List.range (m - 1)).all fun r ↦ pivots[r]! < pivots[r + 1]! do
    throw "the pivot columns are not increasing columns of the matrix"
  let free := (List.range n).toArray.filter (!pivots.contains ·)
  if free.isEmpty then throw "the matrix has no eigenvector for the roots of a factor"
  let basis := free.map fun f ↦ (Array.range n).map fun j ↦
    if j = f then #[1]
    else match pivots.findIdx? (· == j) with
      | some r => Dense.scale (-1) (R[r]!.getD f #[])
      | none => #[]
  let defect ← basis.mapM fun v ↦ (polyMulVec B v).mapM fun p ↦
    match constantQuotient? q p with
    | some c => pure c
    | none => throw "an eigenvector identity failed"
  let rows := E.extract 0 m
  let reduced := R.extract 0 m
  let remainder ← (rows.zip reduced).mapM fun (e, t) ↦
    ((polyVecMul e B).zip t).mapM fun (p, u) ↦
      match constantQuotient? q (Dense.sub p u) with
      | some c => pure c
      | none => throw "an elimination identity failed"
  for r in [0:m] do
    for s in [0:m] do
      unless (reduced[r]!.getD pivots[s]! #[]) == (if r = s then #[1] else #[]) do
        throw "the reduced rows are not the identity at the pivots"
  unless free.size + m == n && basis.all (·.size == n) && defect.all (·.size == n) &&
      rows.size == m && reduced.size == m && remainder.size == m &&
      remainder.all (·.size == n) do
    throw "the certificate has the wrong dimensions"
  return {
    factor := q
    multiplicity := k
    certificate := realCertificate? q
    basis := basis
    defect := defect
    rows := rows
    reduced := reduced
    remainder := remainder
    free := free
    pivots := pivots }

/-- The bases for the roots of the monic factor `q` of multiplicity `k`, and the rational roots
that its parts of degree one give: one basis for all the roots of `q` or, when the elimination
finds a proper factor `g` of `q`, the bases and the roots of `g` and of `q / g`. A part `X - r`
of degree one gives the rational root `r` with multiplicity `k`. Each split lowers the degree, so
a fuel of the degree of `q` plus one is enough. -/
def eigenbases (A : QMatrix) :
    Nat → Dense × Nat → Except String (List Eigenbasis × List (ℚ × Nat))
  | 0, _ => throw "the elimination did not finish"
  | fuel + 1, (q, k) =>
    match Dense.degree q with
    | 0 => return ([], [])
    | 1 => return ([], [(-(q.getD 0 0) / q.getD 1 1, k)])
    | _ =>
      match eliminateModulo q (shiftedMatrix A) with
      | .split g => do
        let h := Dense.monic (Dense.divMod q g).1
        let (bases, roots) ← eigenbases A fuel (g, k)
        let (bases', roots') ← eigenbases A fuel (h, k)
        return (bases ++ bases', roots ++ roots')
      | .reduced R E pivots => do return ([← eigenbasisOf A q k R E pivots], [])

/-- The rational roots `roots` and `extra` with their multiplicities, in increasing order. The
roots in `roots` must be distinct, as those of the rational root search are. A root of `extra`
that is in `roots`, or earlier in `extra`, adds its multiplicity to that root. -/
def mergeRoots (roots extra : List (ℚ × Nat)) : List (ℚ × Nat) :=
  (extra.foldl (fun acc (r, k) ↦
    if acc.any (·.1 == r) then acc.map fun (s, j) ↦ if s == r then (s, j + k) else (s, j)
    else acc ++ [(r, k)]) roots).mergeSort (·.1 ≤ ·.1)

/-- The remaining monic factors of the split `s`, after its rational roots, with their
multiplicities: the quadratics of the roots `α ± c √m` and `α ± c √m i`, then the enclosed
factors. -/
def irrationalFactors (s : RootSplit.Split) : List (Dense × Nat) :=
  (s.exact.filterMap fun (ρ, k) ↦ match ρ with
    | .real _ => none
    | .realPair α γ m => some (#[α * α - γ * γ * m, -2 * α, 1], k)
    | .pair α γ m => some (#[α * α + γ * γ * m, -2 * α, 1], k)) ++
    s.enclosed.map fun (q, k) ↦ (Dense.monic q, k)

/-- The tactic proving `q(α) = 0`, with `q(α)` written as a polynomial in `α`, from
`hα : Polynomial.aeval α q = 0`. -/
def rootTactic (hα : TSyntax `ident) : TermElabM (TSyntax `tactic) :=
  `(tactic| (
    have h := $hα:ident
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, map_one, map_zero, map_ofNat, map_natCast, map_intCast, eq_ratCast,
      eq_intCast] at h
    try push_cast at h
    linear_combination h))

/-- The tactic proving `q = Polynomial.ofCoeffList a` for a polynomial `q` written in
`Polynomial.X` and the list `a` of its coefficients: by evaluation at every point. -/
def coeffListTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| (
    apply Polynomial.funext
    intro t
    simp only [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero,
      Polynomial.eval_ofNat]
    ring1))

/-- The statement that the vectors of `b` are a basis of the eigenspace of `A` for every root `α`
of its factor `q`, over `ℝ` or `ℂ`, and its proof by `CAS.Analysis.Matrix.eigenspace_basis`: the
identities of the certificate at `α` by `ring1`, coordinate by coordinate, and the positions of
the free and pivot columns by evaluation. Over `ℝ` the statement begins with
`(q.map (algebraMap ℚ ℝ)).Splits`, from the kernel's check of the certificate of `b` by
`CAS.Analysis.Matrix.EigFactor.splits_of_realCheck`. -/
def eigenbasisStatement (A : QMatrix) (b : Eigenbasis) :
    TermElabM (TSyntax `term × TSyntax `term) := do
  let n := A.rows
  let k := b.basis.size
  let m := b.pivots.size
  let qT ← qPolyTerm b.factor
  let K ← if b.real then `(ℝ) else `(ℂ)
  let α := mkIdent `α
  let hα := mkIdent `hα
  let family (rows : Array (Array (TSyntax `term))) : TermElabM (TSyntax `term) := do
    let rowTerms ← rows.mapM fun (r : Array (TSyntax `term)) ↦ `(![$r,*])
    `((![$rowTerms,*] : Fin $(natTerm rows.size) → Fin $(natTerm n) → $K))
  let polyFamily (rows : PolyMatrix) : TermElabM (TSyntax `term) := do
    family (← rows.mapM (·.mapM fun p ↦ RootSplit.polySyntax p.toList α K))
  let ratFamily (rows : Array (Array ℚ)) : TermElabM (TSyntax `term) := do
    family (← rows.mapM (·.mapM fun a ↦ do `(($(← ratSyntax a) : $K))))
  let Vt ← polyFamily b.basis
  let MK ← matrixTermOver A K
  let one ← `((1 : Matrix (Fin $(natTerm n)) (Fin $(natTerm n)) $K))
  let shifted ← `(($MK - $α • $one))
  let statement ← `(∀ $α:ident : $K, Polynomial.aeval $α $qT = 0 →
    (∀ i : Fin $(natTerm k), Matrix.mulVec $shifted ($Vt i) = 0) ∧ LinearIndependent $K $Vt ∧
    ∀ x : Fin $(natTerm n) → $K, Matrix.mulVec $shifted x = 0 →
      ∃ c : Fin $(natTerm k) → $K, x = ∑ i, c i • $Vt i)
  let vectorTac ← `(tactic| (
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_mulVec, Matrix.empty_mulVec, Matrix.cons_dotProduct,
      Matrix.dotProduct_of_isEmpty, Matrix.head_cons, Matrix.tail_cons, Matrix.smul_cons,
      Matrix.smul_empty, Matrix.cons_add_cons, Matrix.empty_add_empty, Matrix.vecCons_inj,
      smul_eq_mul, add_zero]
    all_goals (and_intros <;> ring1)))
  let rowTac ← if m = 0 then `(tactic| (intro r; exact r.elim0)) else `(tactic| (
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_vecMul, Matrix.empty_vecMul, Matrix.head_cons,
      Matrix.tail_cons, Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_add_cons,
      Matrix.empty_add_empty, Matrix.vecCons_inj, smul_eq_mul, add_zero]
    all_goals (and_intros <;> ring1)))
  let deltaTac ← `(tactic| (intro i j; fin_cases i <;> fin_cases j <;> rfl))
  let pivotTac ← if m = 0 then `(tactic| (intro r; exact r.elim0)) else pure deltaTac
  let proof ← `(fun $α:ident $hα:ident ↦ CAS.Analysis.Matrix.eigenspace_basis
    (c := $(← RootSplit.polySyntax b.factor.toList α K)) (W := $(← ratFamily b.defect))
    (E := $(← polyFamily b.rows)) (T := $(← polyFamily b.reduced))
    (S := $(← ratFamily b.remainder)) (free := $(← indexMapTerm b.free n))
    (pivot := $(← indexMapTerm b.pivots n))
    (by $(← rootTactic hα):tactic) (by $vectorTac:tactic) (by $rowTac:tactic)
    (by $deltaTac:tactic) (by $pivotTac:tactic) (by decide))
  let some f := b.certificate | return (statement, proof)
  let hcheck ← certified (← `(CAS.Analysis.Matrix.EigFactor.realCheck $(← factorSyntax f)
    $(← coeffsTerm b.factor.toList) = true))
  return (← `((Polynomial.map (algebraMap ℚ ℝ) $qT).Splits ∧ $statement),
    ← `(⟨CAS.Analysis.Matrix.EigFactor.splits_of_realCheck (q := $qT)
      (by $(← coeffListTactic):tactic) $hcheck, $proof⟩))

/-- A vector with entries in `ℚ[a]` as text, in the variable `a`. -/
def polyVectorText (a : String) (v : Array Dense) : String :=
  "![" ++ ", ".intercalate (v.toList.map (denseText a)) ++ "]"

/-- Run `#cas [eigenvalues] A` or `#cas [eigenvectors] A`. The eigenvalues are the factorization
of the characteristic polynomial when they are all rational and the spectrum (`logSpectrum`)
otherwise. The eigenvectors are a basis of the null space of `A - λ • 1` for each rational
eigenvalue `λ` and, for each remaining factor `q` of the characteristic polynomial, a basis of
the eigenspace of every root of `q` (`eigenbases`, `eigenbasisStatement`), with the factorization
into the factors `X - λ` and `q`. A part of degree one that `eigenbases` splits off is a rational
eigenvalue. With `irreducible?` (from the `CASHex` backend), we ask it about the enclosed factors
of the spectrum (`logSpectrum`) or about the factor `q` of each basis from `eigenbases`: the
statement says that each factor it proves irreducible over `ℚ` is irreducible, and the report
lists the other factors that we asked about. Without `irreducible?`, as on the core route, the
statement has no `Irreducible` conjunct and the report lists no factor. The planner metadata of
the report names the route that answered. The proofs and their kernel checks run under
`withSpectrumBudget`. -/
def logEigen (ref : Syntax) (vectors : Bool) (input : Syntax)
    (irreducible? : Option (List Int → CommandElabM (Option (Lean.Expr × Lean.Expr))) := none) :
    CommandElabM Unit := do
  let operation := if vectors then "eigenvectors" else "eigenvalues"
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "{operation}: the matrix must be square"
  let n := A.rows
  let s := RootSplit.split (← liftCoreM Tactic.RouteRegistry.factorProvider?) A.charpoly
  let found : List (ℚ × Nat) := (s.exact.filterMap fun (ρ, k) ↦ match ρ with
    | .real r => some (r, k)
    | _ => none).mergeSort (·.1 ≤ ·.1)
  let linear := found.foldl (fun acc (r, k) ↦ Dense.mul acc (Dense.pow #[-r, 1] k)) #[1]
  let rest := Dense.monic (Dense.divMod s.poly linear).1
  if !vectors && rest.size > 1 then
    logSpectrum ref input A s found irreducible?
    return
  let (bases, extra) ← if vectors then
      match (irrationalFactors s).mapM fun (q, k) ↦ eigenbases A (Dense.degree q + 1) (q, k) with
      | .ok parts => pure ((parts.map (·.1)).flatten, (parts.map (·.2)).flatten)
      | .error msg => throwErrorAt input "{operation}: {msg}"
    else pure ([], [])
  let roots := mergeRoots found extra
  let mut facts : Array (Lean.Expr × Lean.Expr) := #[]
  let mut uncertified : Array String := #[]
  if let some irreducible := irreducible? then
    for b in bases do
      match ← irreducible (integerCoefficients b.factor) with
      | some fact => facts := facts.push fact
      | none => uncertified := uncertified.push (denseText "X" b.factor)
  let (proposition, proof, spaces) ← liftTermElabM <| withSpectrumBudget do
    let At ← matrixTerm A n n
    let factors := bases.map fun b ↦ (b.factor, b.multiplicity)
    let factorization ← `(Matrix.charpoly $At = $(← factoredTerm roots factors))
    let charpoly ← charpolyTactic A
    let identity ← polynomialIdentityTactic
    let P ← qPolyTerm A.charpoly
    let factorProof ← `(term| by
      have hP : Matrix.charpoly $At = $P := by $charpoly:tactic
      first | (rw [hP]; done) | (rw [hP]; $identity:tactic))
    let mut statement := factorization
    let mut proofs : Array (TSyntax `term) := #[]
    for (p, q) in facts.reverse do
      statement ← `($(← exprToSyntax p) ∧ $statement)
      proofs := #[← exprToSyntax q] ++ proofs
    for b in bases.reverse do
      let (space, proof) ← eigenbasisStatement A b
      statement ← `($space ∧ $statement)
      proofs := #[proof] ++ proofs
    let mut spaces : List (ℚ × Array (Array ℚ)) := []
    if vectors then
      for (r, _) in roots.reverse do
        -- The eigenspace of `r`: the null space of `A - r I`, with basis, independence and
        -- spanning certified.
        let B := A.subScalar r
        let (R, _, pivots) := B.rowReduce
        let one ← `((1 : Matrix (Fin $(natTerm n)) (Fin $(natTerm n)) ℚ))
        let display ← `(($At - ($(← ratTerm r)) • $one))
        let (V, space, script) ← nullSpaceProof B R pivots (some display)
        statement ← `($space ∧ $statement)
        proofs := #[← `(term| by $script:tactic)] ++ proofs
        spaces := (r, V) :: spaces
    proofs := proofs.push factorProof
    let (a, b) ← if proofs.size = 1 then
        proveStatement operation statement (← `(tactic| exact $(proofs[0]!)))
      else
        proveStatement operation statement (← `(tactic| exact ⟨$proofs,*⟩))
    pure (a, b, spaces)
  -- The roots of the factors `q` are named `α`, or `α₁`, `α₂`, … for several factors.
  let names : List String := if bases.length = 1 then ["α"]
    else (List.range bases.length).map fun j ↦ s!"α{Nat.toSubscriptString (j + 1)}"
  let entries := spaces.map (fun (r, V) ↦
      s!"{ratText r} ↦ [" ++ ", ".intercalate (V.toList.map vectorText) ++ "]") ++
    (bases.zip names).map fun (b, a) ↦
      s!"{a} ↦ [" ++ ", ".intercalate (b.basis.toList.map (polyVectorText a)) ++ "]"
  let domains := (bases.zip names).map fun (b, a) ↦
    s!"each {a} ∈ {if b.real then "ℝ" else "ℂ"} with {denseText a b.factor} = 0"
  let shown := if vectors then
      "[" ++ ", ".intercalate entries ++ "]" ++
        (if domains.isEmpty then "" else " for " ++ " and ".intercalate domains)
    else eigenvaluesText roots
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := shown
    outputType := if vectors then "eigenvalue ↦ basis of its eigenspace"
      else "eigenvalues with multiplicity"
    furtherResults := uncertifiedLine uncertified
  } #[← liftTermElabM <| withSpectrumBudget <| eigenEvidence operation
      "Characteristic polynomial factored over ℚ, eigenspaces" irreducible?.isSome proposition
      proof]

end CAS.Command.LinearAlgebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [characteristicPolynomial] A` computes the characteristic polynomial `det (x I - A)` of a
square matrix `A` with rational entries and proves it.

## Theorem
The report proves `A.charpoly = p` in `ℚ[X]`, for Mathlib's `Matrix.charpoly` and the printed
polynomial `p` written in `Polynomial.X`. The proof compares both sides at every point `t`
(`Polynomial.funext`): `Matrix.eval_charpoly` turns the value of `A.charpoly` at `t` into the
determinant of the literal `t I - A`, which `norm_det` evaluates.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`. The polynomial is
monic, Mathlib's convention `det (X I - A)`.

## Options
None.

## Examples
```lean
#cas [characteristicPolynomial] !![1, 2; 3, 4]
```
```output
Output (det (x I - A)): x^2 - 5*x - 2
```
```lean
#cas [characteristicPolynomial] !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]
```
```output
Output (det (x I - A)): x^4 - 8*x^3 + 21*x^2 - 20*x + 5
```

## In a proof
```lean
theorem charpoly_two :
    Matrix.charpoly !![(1 : ℚ), 2; 3, 4] = Polynomial.X ^ 2 - 5 * Polynomial.X - 2 := by
  cas
```

## See also
Mathematica `CharacteristicPolynomial`, whose `det (A - x I)` is `(-1) ^ n` times this
polynomial, and SymPy `Matrix.charpoly`. The modes `eigenvalues`, `det` and `trace`.

## Possible issues
```lean
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6]
```
```output
characteristicPolynomial: the matrix must be square
```
The characteristic polynomial is defined for square matrices only.
-/
syntax (name := casCharacteristicPolynomialCommand)
  "#cas" "[" &"characteristicPolynomial" "]" term : command

/-- `#cas [eigenvalues] A` computes the eigenvalues of a square matrix `A` with rational entries,
with their algebraic multiplicities, and proves that they are the whole spectrum.

## Theorem
When every eigenvalue is rational, the report proves the factorization
`A.charpoly = (X - λ₁) ^ m₁ * ⋯ * (X - λₖ) ^ mₖ` in `ℚ[X]`. Otherwise let `M` be the matrix with
the entries of `A` over `K = ℝ` when every eigenvalue is real, and over `K = ℂ` otherwise. The
report then proves `spectrum K M = {μ₁, …, μₛ}`, each eigenvalue once, and
`M.charpoly.roots = {μ₁, …}`, the multiset of the eigenvalues with their multiplicities.

The eigenvalues are rational numbers, quadratic surds `α ± c √m` and `α ± c √m i`, or the roots
of a factor `R` of higher degree, named in the theorem by `let r₁ := CAS.AlgRoot.real R lo hi`
with `r₁ ∈ Set.Ioo lo hi` and `R r₁ = 0`, or by `let z₁ := CAS.AlgRoot.complex R u v ρ` with
intervals for its real and imaginary parts. The kernel checks that the factors multiply to the
characteristic polynomial (`CAS.Analysis.Matrix.eigenCheck`).

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`. Without Hex, a factor
of higher degree comes from the squarefree decomposition of the characteristic polynomial and
need not be irreducible; each of its roots gets its own enclosure.

There is no limit on the size of `A`. The search for the eigenvalues (the rational roots, the
squarefree decomposition, the factor provider and the enclosures) runs before the proof without a
heartbeat limit, and the proof and its kernel check run with `maxHeartbeats` raised to at least one
million (`maxHeartbeats 0`, no limit, stays unlimited), so a large matrix can take long or run out
of heartbeats.

## Options
None.

## Examples
```lean
#cas [eigenvalues] !![2, 0, 0; 0, 3, 4; 0, 4, 9]
```
```output
Output (eigenvalues with multiplicity): [1, 2, 11]
```
```lean
#cas [eigenvalues] !![0, 1; 1, 1]
```
```output
Output (eigenvalues with multiplicity): [1/2 - √5/2, 1/2 + √5/2]
```
```lean
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```
```output
Output (eigenvalues with multiplicity): [r₁, z₁, conj z₁]; r₁ ∈ (1.25992104, 1.25992106), z₁,
conj z₁ = α ± iβ, α ∈ [-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]
```

## In a proof
```lean
theorem golden_ratio_mem_spectrum
    (h : spectrum ℝ !![(0 : ℝ), 1; 1, 1] = {1 / 2 - 1 / 2 * √5, 1 / 2 + 1 / 2 * √5}) :
    1 / 2 + 1 / 2 * √5 ∈ spectrum ℝ !![(0 : ℝ), 1; 1, 1] := by
  rw [h]
  exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
```
A proof can take the first part of the printed theorem as a hypothesis and read an eigenvalue off
it, as here the golden ratio.

## See also
Mathematica `Eigenvalues`, SymPy `Matrix.eigenvals`, Hex `Hex.ZPoly.factorize` (through
`CASHex.Factor`, which splits the characteristic polynomial into irreducible factors, adds
`Irreducible R` for each factor `R` of higher degree whose irreducibility Hex certifies, and lists
the other factors of higher degree in the report; without `CASHex` the theorem has no
`Irreducible` conjunct and the report lists no factor). The modes `characteristicPolynomial`,
`eigenvectors`, `eigenvalueBounds` and `roots`. Oracle route:
`#cas [eigenvalues, oracle := sympy] A` (in `CASOracle`), which proves for each real eigenvalue
`c` that the oracle reports that `spectrum ℝ A` meets `[c - 10⁻ᵈ, c + 10⁻ᵈ]`; that the list is
complete is the oracle's claim.

## Possible issues
```lean
#cas [eigenvalues] !![1, 2, 3; 4, 5, 6]
```
```output
eigenvalues: the matrix must be square
```
Eigenvalues are defined for square matrices only. `#cas [matrixRank] A` and `#cas [nullSpace] A`
describe a matrix of any shape.
-/
syntax (name := casEigenvaluesCommand) "#cas" "[" &"eigenvalues" "]" term : command

/-- `#cas [eigenvectors] A` computes a basis of the eigenspace of every eigenvalue of a square
matrix `A` with rational entries and proves it.

## Theorem
For each rational eigenvalue `λ` with printed vectors `V i`, the report proves the null space
statement of `#cas [nullSpace]` for `A - λ • 1` over `ℚ`: `(A - λ • 1).mulVec (V i) = 0` for each
`i`, `LinearIndependent ℚ V`, and `∀ x, (A - λ • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`.

The other eigenvalues are the roots of the remaining monic factors `q` of `A.charpoly`, the
factors left after the rational roots that the root search finds. For each such `q`, let `K = ℝ`
when a certificate shows that every root of `q` is real and `K = ℂ` otherwise, and let `M` be the
matrix with the entries of `A` over `K`. The printed vectors `V i` have entries that are
polynomials in `α` with rational coefficients, and the report proves the same statement for
`M - α • 1` and every root `α` of `q` at once: `∀ α : K, Polynomial.aeval α q = 0 →
(∀ i, (M - α • 1).mulVec (V i) = 0) ∧ LinearIndependent K V ∧
∀ x, (M - α • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`. For `K = ℝ` it also proves
`(q.map (algebraMap ℚ ℝ)).Splits`, so that these real roots are all the roots of `q`. The
certificate is the discriminant of a quadratic or enclosures of the roots in disjoint rational
intervals, which the kernel checks; `CAS.Analysis.Matrix.EigFactor.splits_of_realCheck` turns it
into the statement.

It adds the factorization of `A.charpoly` in `ℚ[X]` into the factors `X - λ` and `q`, with their
multiplicities.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`. Without Hex, a factor
`q` of degree three or more comes from the squarefree decomposition of the characteristic
polynomial and need not be irreducible. The elimination over `ℚ[X]/(q)` may then split `q` into
factors, each with its own statement; every statement holds for every root of its factor. The
search for rational roots has a bisection budget, so a remaining factor may still have rational
roots; a part of degree one that the elimination splits off is then a rational eigenvalue, with
the statement over `ℚ`.

There is no limit on the size of `A`. The search (the rational roots, the squarefree
decomposition, the factor provider, the enclosures and the elimination over `ℚ[X]/(q)`) runs
before the proof without a heartbeat limit, and the proof and its kernel check run with
`maxHeartbeats` raised to at least one million (`maxHeartbeats 0`, no limit, stays unlimited), so
a large matrix can take long or run out of heartbeats.

## Options
None.

## Examples
```lean
#cas [eigenvectors] !![4, 1; 2, 3]
```
```output
Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![-1/2, 1]], 5 ↦ [![1, 1]]]
```
```lean
#cas [eigenvectors] !![1, 1; 0, 1]
```
```output
Output (eigenvalue ↦ basis of its eigenspace): [1 ↦ [![1, 0]]]
```
```lean
#cas [eigenvectors] !![1, 1; 1, 0]
```
```output
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0
```
```lean
#cas [eigenvectors] !![0, -1; 1, 0]
```
```output
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℂ with α^2 + 1 = 0
```

## In a proof
```lean
theorem eigenvector_five : !![(4 : ℚ), 1; 2, 3].mulVec ![1, 1] = (5 : ℚ) • ![1, 1] := by
  cas
```

## See also
Mathematica `Eigenvectors`, SymPy `Matrix.eigenvects`, Hex `Hex.ZPoly.factorize` (through
`CASHex.Factor`, which splits the characteristic polynomial into irreducible factors, adds
`Irreducible q`, for `q` scaled to coprime integer coefficients, for each factor `q` whose
irreducibility Hex certifies, and lists the other factors `q` in the report; without `CASHex` the
theorem has no `Irreducible` conjunct and the report lists no factor). The modes `eigenvalues`,
`nullSpace` and `characteristicPolynomial`.

## Possible issues
```lean
#cas [eigenvectors] !![1, 2, 3; 4, 5, 6]
```
```output
eigenvectors: the matrix must be square
```
Eigenvectors are defined for square matrices only. `#cas [nullSpace] A` gives the null space of a
matrix of any shape.
-/
syntax (name := casEigenvectorsCommand) "#cas" "[" &"eigenvectors" "]" term : command

elab_rules : command
  | `(#cas [characteristicPolynomial] $A:term) => LinearAlgebra.logCharpoly A A
  | `(#cas [eigenvalues] $A:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `eigenvalues (← getRef) do
        LinearAlgebra.logEigen A false A
  | `(#cas [eigenvectors] $A:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `eigenvectors (← getRef) do
        LinearAlgebra.logEigen A true A

end CAS.Command
