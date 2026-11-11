/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Representation
public meta import CAS.Polynomial.Sparse.Representation

/-!
# Gröbner bases over ℚ with derivations

Buchberger's algorithm (`groebner`) for the lexicographic order on `ℚ[v₀, …, v_{n-1}]`, with
`v₀` the largest variable, as used by `#cas [solve x, y, …]` for nonlinear systems
(`CAS/Command/PolySystems.lean`) and by `#cas [groebner]`, `#cas [member]` and the ideal route of
`cas` (`CAS/Command/Ideal.lean`). Every polynomial the algorithm produces is recorded with its
derivation, a combination `∑ c_k g_k` of earlier polynomials with polynomial coefficients.
`shape?` recognizes a reduced basis in shape position, `v_i - g_i(v_{n-1})` for `i < n - 1`
together with one polynomial `R(v_{n-1})`: the zero-dimensional ideals whose points have
distinct last coordinates.

## Implementation notes

Nothing computed here is trusted. The solve command turns the derivations into
`linear_combination` steps, and the ideal commands turn them into ring identities and check the
Gröbner property with a certificate of their own. So we run the classical algorithm in meta code
on lists of terms with rational coefficients: the S-polynomial of a pair of basis elements is
divided by the current basis, and a nonzero remainder joins the basis, monic. The pair whose
leading monomials have the least common multiple of smallest total degree goes first, and we
skip a pair whose leading monomials are coprime (criterion S2 of Buchberger's 1970 article); we
use no other criterion. A nonzero constant, among the inputs or as a remainder, ends the run: the
ideal is the whole ring. Otherwise a minimal basis and interreduction give the reduced basis. The
derivations are our bookkeeping for the proofs, so that the commands can replay each step in the
kernel. A run that exceeds its budgets (`maxNodes`, `maxPairs` and the fuel of `reduce`) fails
with a message.

## References

* Bruno Buchberger, "Ein algorithmisches Kriterium für die Lösbarkeit eines algebraischen
  Gleichungssystems", *Aequationes Mathematicae* 4 (1970), pp. 374-383,
  <https://doi.org/10.1007/BF01844169>. Section 2.3 defines the S-polynomials, and Section 2.4
  gives the algorithm with criterion S2, which skips a pair whose least common multiple is the
  product of the two leading power products: the coprime criterion of `groebner`.
* Bruno Buchberger, "An Algorithmic Criterion for the Solvability of a System of Algebraic
  Equations", translated by Michael Abramson and Robert Lumbert, in Bruno Buchberger and Franz
  Winkler (eds.), *Gröbner Bases and Applications*, London Mathematical Society Lecture Note
  Series 251, Cambridge University Press, Cambridge, 1998,
  <https://doi.org/10.1017/CBO9780511565847.034>. The English translation of the 1970 article.
* Bruno Buchberger, "Bruno Buchberger's PhD thesis 1965: An algorithm for finding the basis
  elements of the residue class ring of a zero dimensional polynomial ideal", *Journal of
  Symbolic Computation* 41 (2006), pp. 475-511, <https://doi.org/10.1016/j.jsc.2005.09.007>.
  The English translation of the 1965 thesis in which the algorithm first appeared.
* David A. Cox, John Little and Donal O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed.,
  Undergraduate Texts in Mathematics, Springer, Cham, 2015,
  <https://doi.org/10.1007/978-3-319-16721-3>. Chapter 2, "Gröbner Bases", pp. 49-119.
-/

public meta section

namespace CAS.Command.Groebner

/-- Exponents of the variables, the first variable the largest. -/
abbrev Mono := Array Nat

/-- Terms with nonzero coefficients, strictly decreasing in the lexicographic order. -/
abbrev Poly := List (Mono × ℚ)

/-- The lexicographic order. -/
def monoCmp (a b : Mono) : Ordering := Id.run do
  for i in [0:max a.size b.size] do
    let x := a.getD i 0
    let y := b.getD i 0
    if x < y then return .lt
    if y < x then return .gt
  return .eq

/-- The sum of two polynomials. -/
partial def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | (m, c) :: p, (n, d) :: q =>
      match monoCmp m n with
      | .gt => (m, c) :: add p ((n, d) :: q)
      | .lt => (n, d) :: add ((m, c) :: p) q
      | .eq => if c + d == 0 then add p q else (m, c + d) :: add p q

/-- `c p`. -/
def scale (c : ℚ) (p : Poly) : Poly :=
  if c == 0 then [] else p.map fun (m, d) ↦ (m, c * d)

/-- The difference of two polynomials. -/
def sub (p q : Poly) : Poly := add p (scale (-1) q)

/-- The product of two monomials. -/
def monoMul (a b : Mono) : Mono :=
  (Array.range (max a.size b.size)).map fun i ↦ a.getD i 0 + b.getD i 0

/-- `c m p` for a monomial `m`. -/
def mulTerm (m : Mono) (c : ℚ) (p : Poly) : Poly :=
  if c == 0 then [] else p.map fun (n, d) ↦ (monoMul m n, c * d)

/-- `a` divides `b`. -/
def divides (a b : Mono) : Bool :=
  (List.range (max a.size b.size)).all fun i ↦ a.getD i 0 ≤ b.getD i 0

/-- `b / a` for `a` dividing `b`. -/
def monoDiv (b a : Mono) : Mono :=
  (Array.range (max a.size b.size)).map fun i ↦ b.getD i 0 - a.getD i 0

/-- The least common multiple of two monomials. -/
def monoLcm (a b : Mono) : Mono :=
  (Array.range (max a.size b.size)).map fun i ↦ max (a.getD i 0) (b.getD i 0)

/-- No variable divides both monomials. -/
def coprime (a b : Mono) : Bool :=
  (List.range (max a.size b.size)).all fun i ↦ a.getD i 0 == 0 || b.getD i 0 == 0

/-- The total degree. -/
def degree (m : Mono) : Nat := m.foldl (· + ·) 0

/-- The constant `c` in `n` variables. -/
def constant (n : Nat) (c : ℚ) : Poly := if c == 0 then [] else [(Array.replicate n 0, c)]

/-- The variable `v_i` in `n` variables. -/
def var (n i : Nat) : Poly := [((Array.replicate n 0).set! i 1, 1)]

/-- The polynomial from an exponent-vector polynomial, with variable `i` of the result taken
from variable `order[i]` of the input. -/
def ofMvPoly {k : Nat} (n : Nat) (order : Array Nat)
    (p : CAS.Verified.Expr.Alg.MvPoly k) : Poly :=
  p.foldl (fun total (c, mono) ↦
    let exponents := (Array.range n).map fun i ↦
      match order[i]? with
      | some j => if h : j < k then mono ⟨j, h⟩ else 0
      | none => 0
    add total (if c == 0 then [] else [(exponents, c)])) []

/-- Every term lies in the last variable only. -/
def isUnivariate (n : Nat) (p : Poly) : Bool :=
  p.all fun (m, _) ↦ (List.range (n - 1)).all fun i ↦ m.getD i 0 == 0

/-- The coefficients `c₀, c₁, …` of a polynomial in the last variable only. -/
def univariateCoefficients (n : Nat) (p : Poly) : List ℚ :=
  let top := p.foldl (fun d (m, _) ↦ max d (m.getD (n - 1) 0)) 0
  (List.range (top + 1)).map fun j ↦
    p.foldl (fun total (m, c) ↦ if m.getD (n - 1) 0 == j then total + c else total) 0

/-- A combination `∑ c_k g_k`: node indices with polynomial coefficients. -/
abbrev Combo := List (Nat × Poly)

/-- The sum of two combinations. -/
def comboAdd (a b : Combo) : Combo :=
  b.foldl (fun total (k, p) ↦
    match total.find? (·.1 == k) with
    | some (_, q) =>
        let s := add q p
        total.filter (·.1 != k) ++ (if s.isEmpty then [] else [(k, s)])
    | none => if p.isEmpty then total else total ++ [(k, p)]) a

/-- `c ∑ c_k g_k`. -/
def comboScale (c : ℚ) (a : Combo) : Combo :=
  if c == 0 then [] else a.map fun (k, p) ↦ (k, scale c p)

/-- A polynomial of the computation with its derivation: `poly = ∑ c_k (node k)`, or an input
when `combo` is empty and `input` holds. -/
structure Node where
  /-- The polynomial. -/
  poly : Poly
  /-- Its derivation `∑ c_k (node k)` from earlier nodes; empty for an input. -/
  combo : Combo
  /-- Whether the node is one of the input polynomials. -/
  input : Bool
  deriving Inhabited

/-- The leading monomial and coefficient. -/
def lead (p : Poly) : Mono × ℚ := p.headD (#[], 0)

/-- Division of `p` by the nodes `basis`: the remainder, no term of which is divisible by a
leading monomial of the basis, and the quotients, with `p = remainder + ∑ q_k g_k`. -/
def reduce (nodes : Array Node) (basis : List Nat) (p : Poly) (fuel : Nat := 20000) :
    Option (Poly × Combo) := Id.run do
  let mut current := p
  let mut remainder : Array (Mono × ℚ) := #[]
  let mut quotients : Combo := []
  for _ in [0:fuel] do
    match current with
    | [] => return some (remainder.toList, quotients)
    | (m, c) :: rest =>
        let divisor? := basis.find? fun k ↦
          match (nodes.getD k default).poly with
          | (lm, _) :: _ => divides lm m
          | [] => false
        match divisor? with
        | some k =>
            let g := (nodes.getD k default).poly
            let (lm, lc) := lead g
            let qm := monoDiv m lm
            let qc := c / lc
            current := sub current (mulTerm qm qc g)
            quotients := comboAdd quotients [(k, [(qm, qc)])]
        | none =>
            remainder := remainder.push (m, c)
            current := rest
  return none

/-- A reduced Gröbner basis with the derivations of its elements. -/
structure Result where
  /-- Every polynomial of the computation with its derivation, the inputs first and in
  their order. -/
  nodes : Array Node
  /-- The reduced basis, monic, by node index. -/
  basis : List Nat

/-- Buchberger's algorithm on the inputs, with the coprime-leading-monomial criterion and first
the pair whose leading monomials have the least common multiple of smallest total degree (ties go
to the pair created first), followed by interreduction.

The degree of a pair's least common multiple depends only on the leading monomials of its two
nodes, which never change once created, so it is computed once, when the pair is created, and
kept with the pair; each selection is then one scan of the pending pairs. -/
def groebner (inputs : List Poly) (maxNodes : Nat := 400) (maxPairs : Nat := 4000) :
    Except String Result := do
  let mut nodes : Array Node := #[]
  let mut basis : List Nat := []
  for f in inputs do
    nodes := nodes.push { poly := f, combo := [], input := true }
    if !f.isEmpty then basis := basis ++ [nodes.size - 1]
  let polyOf (nodes : Array Node) (k : Nat) : Poly := (nodes.getD k default).poly
  -- A pending pair `(i, j)` with the degree of the least common multiple of its leading
  -- monomials.
  let pairOf (nodes : Array Node) (i j : Nat) : Nat × Nat × Nat :=
    (i, j, degree (monoLcm (lead (polyOf nodes i)).1 (lead (polyOf nodes j)).1))
  let mut pairs : List (Nat × Nat × Nat) := []
  for i in basis do
    for j in basis do
      if i < j then pairs := pairs ++ [pairOf nodes i j]
  let mut unit := basis.find? fun k ↦ match polyOf nodes k with
    | [(m, _)] => degree m == 0
    | _ => false
  for _ in [0:maxPairs] do
    if unit.isSome then break
    match pairs with
    | [] => break
    | first :: _ =>
      let best := pairs.foldl (fun b q ↦ if q.2.2 < b.2.2 then q else b) first
      pairs := pairs.erase best
      let (i, j, _) := best
      let gi := polyOf nodes i
      let gj := polyOf nodes j
      let (mi, ci) := lead gi
      let (mj, cj) := lead gj
      if coprime mi mj then continue
      let common := monoLcm mi mj
      let ai := monoDiv common mi
      let aj := monoDiv common mj
      let s := sub (mulTerm ai (1 / ci) gi) (mulTerm aj (1 / cj) gj)
      let some (r, quotients) := reduce nodes basis s
        | throw "the division of an S-polynomial exceeded its budget"
      if r.isEmpty then continue
      let lc := (lead r).2
      let combo := comboScale (1 / lc)
        (comboAdd [(i, [(ai, 1 / ci)]), (j, [(aj, -1 / cj)])] (comboScale (-1) quotients))
      nodes := nodes.push { poly := scale (1 / lc) r, combo, input := false }
      let new := nodes.size - 1
      if nodes.size > maxNodes then throw "the Gröbner basis exceeded its budget"
      pairs := pairs ++ basis.map (pairOf nodes · new)
      basis := basis ++ [new]
      if degree (lead r).1 == 0 then unit := some new
  if let some k := unit then return { nodes, basis := [k] }
  if !pairs.isEmpty then throw "the Gröbner basis exceeded its pair budget"
  -- A minimal basis: no leading monomial divides another.
  let leadOf (k : Nat) : Mono := (lead (polyOf nodes k)).1
  let minimal := basis.filter fun k ↦ !basis.any fun k' ↦
    k' != k && divides (leadOf k') (leadOf k) &&
      (monoCmp (leadOf k') (leadOf k) != .eq || k' < k)
  -- Interreduction.
  let mut reduced : List Nat := []
  for k in minimal do
    let others := minimal.filter (· != k)
    let g := polyOf nodes k
    let some (r, quotients) := reduce nodes others g
      | throw "interreduction exceeded its budget"
    let lc := (lead r).2
    if quotients.isEmpty && lc == 1 then
      reduced := reduced ++ [k]
    else
      let combo := comboScale (1 / lc)
        (comboAdd [(k, constant (lead g).1.size 1)] (comboScale (-1) quotients))
      nodes := nodes.push { poly := scale (1 / lc) r, combo, input := false }
      reduced := reduced ++ [nodes.size - 1]
  return { nodes, basis := reduced }

/-- The polynomial of node `k`. -/
def Result.poly (result : Result) (k : Nat) : Poly := (result.nodes.getD k default).poly

/-- Whether the basis is `{1}`. -/
def Result.isUnit (result : Result) : Bool :=
  match result.basis with
  | [k] => match (result.nodes.getD k default).poly with
    | [(m, _)] => degree m == 0
    | _ => false
  | _ => false

/-- Every variable has a pure power among the leading monomials: finitely many complex
points. -/
def Result.isZeroDimensional (n : Nat) (result : Result) : Bool :=
  (List.range n).all fun i ↦ result.basis.any fun k ↦
    let m := (lead (result.nodes.getD k default).poly).1
    m.getD i 0 > 0 && (List.range n).all fun j ↦ j == i || m.getD j 0 == 0

/-- A basis in shape position: the node of `R(v_{n-1})` and, for `i < n - 1`, the node of
`v_i - g_i(v_{n-1})`. -/
def Result.shape? (n : Nat) (result : Result) : Option (Nat × Array Nat) := Id.run do
  if result.basis.length != n then return none
  let mut eliminant : Option Nat := none
  let mut solved : Array (Option Nat) := Array.replicate (n - 1) none
  for k in result.basis do
    let p := (result.nodes.getD k default).poly
    if isUnivariate n p then
      if eliminant.isSome then return none
      eliminant := some k
    else
      match p with
      | (m, _) :: rest =>
          let some i := (List.range (n - 1)).find? fun i ↦ m.getD i 0 == 1
            | return none
          unless degree m == 1 && isUnivariate n rest do return none
          if (solved.getD i none).isSome then return none
          solved := solved.set! i (some k)
      | [] => return none
  let some r := eliminant | return none
  let mut nodes : Array Nat := #[]
  for entry in solved do
    let some k := entry | return none
    nodes := nodes.push k
  return some (r, nodes)

/-- The nodes needed to derive `targets`, in increasing order. -/
def Result.closure (result : Result) (targets : List Nat) : List Nat := Id.run do
  let mut needed : Array Bool := Array.replicate result.nodes.size false
  for k in targets do needed := needed.set! k true
  for offset in [0:result.nodes.size] do
    let k := result.nodes.size - 1 - offset
    if needed.getD k false then
      for (j, _) in (result.nodes.getD k default).combo do
        needed := needed.set! j true
  return (List.range result.nodes.size).filter (needed.getD · false)

end CAS.Command.Groebner
