/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS.Command.FullSimplify
import CASOracle.Integrate

/-!
# Factorizations proposed by an oracle

`#cas [factor, oracle := o] p`, for a polynomial `p` with rational coefficients in any number of
real variables, asks the oracle for `p = c * ∏ gᵢ ^ mᵢ` and proves exactly that identity between
real functions, `∀ x y …, p = c * ∏ gᵢ ^ mᵢ`. The identity is the theorem. That each
`gᵢ` is irreducible over `ℚ`, that the `gᵢ` are pairwise distinct, and that `mᵢ` is the full
multiplicity are the oracle's claims and are shown as hints.

The oracles with a `factor` task are `sympy`, `sage`, `flint` and `maxima` (any number of
variables) and `pari` (one variable).

## Implementation notes

We build the candidate from the oracle's factors ourselves and prove it with the closers of
`#cas [factor]` (`FullSimplify.proveCandidate`: `rfl`, `ring1`, `cas`, `field_simp; ring1`), so
the oracle contributes no condition and no closer. Irreducibility is certified separately, in
one variable and through Hex, by `CASHex.Factor`.
-/

namespace CASOracle.Factor

open Lean Elab Command Meta Term
open CAS CAS.Command CAS.Command.InfoView CAS.Command.FullSimplify
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-- Ask `oracle` for `p = c * ∏ gᵢ ^ mᵢ`: the constant `c` and the factors `gᵢ` with their
multiplicities `mᵢ`, as proposed (nothing is checked here). -/
def proposeFactorization (oracle : Oracle) {n : Nat} (p : Verified.Expr (Fin n)) :
    TermElabM (ℚ × Array (Verified.Expr (Fin n) × Nat)) := do
  let text ← Translate.write (Translate.requestLanguage oracle) wireName p
  let names := wireNames n
  if oracle == .maxima then
    let answer ← askMaxima "factor" "product" s!"factor({text})"
    match Translate.productFactors (← Translate.readAnswer oracle wireName answer) with
    | .ok (constant, factors) => return (constant, factors.toArray)
    | .error why => throwError m!"the oracle's factorization is refused: {why}{indentD answer}"
  let arguments ← if oracle == .pari then do
      unless n = 1 do fail oracle (.unsupported "pari factors polynomials in one variable here")
      let sympy ← Translate.write `sympyOut wireName p
      pure s!"{pyRead sympy names}, {py text}, {pyVariables names}[0]"
    else pure s!"{pyRead text names}, {pyVariables names}"
  let found ← askPython oracle "factor" ["constant", "factor"] arguments
  let constantText ← payload oracle found "constant"
  let some constant := parseRat? constantText
    | throwError "the oracle's constant {constantText} is not a rational"
  let factors ← (← payloads oracle found "factor" 200).mapM fun record ↦ do
    let multiplicity :: factor := record.splitOn " "
      | throwError "the oracle's factor record {record} is malformed"
    let some m := smallNat? multiplicity
      | throwError "the oracle's multiplicity {multiplicity} is not a small natural number"
    return (← Translate.readAnswer oracle wireName (" ".intercalate factor), m)
  return (constant, factors)

/-- `#cas [factor, oracle := o] p`. -/
syntax (name := casFactorOracleCommand)
  "#cas" "[" &"factor" ", " &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [factor, oracle := o] p`: the oracle's factorization, checked in Lean before
it is reported. -/
@[command_elab casFactorOracleCommand]
def elabFactor : CommandElab := fun stx ↦ do
  let `(#cas [factor, oracle := $o:ident] $input:term) := stx | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let reified ← parseInferred input
  let n := reified.names.length
  if (Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify reified.expr)).isNone then
    throwErrorAt input "factor: the input is not a polynomial with rational coefficients"
  let (constant, factors) ← liftTermElabM <| proposeFactorization oracle reified.expr
  if factors.size > 200 then throwError "the oracle's answer has {factors.size} factors, over 200"
  let mut decoded : Array (Verified.Expr (Fin n) × Nat) := #[]
  for (g, m) in factors do
    unless 1 ≤ m ∧ m ≤ 1000 do throwError "the oracle's multiplicity {m} is out of range"
    if (Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify g)).isNone then
      throwError "the oracle's factor {renderExpr reified g} is not a polynomial"
    decoded := decoded.push (g, m)
  -- The factorization as a whole is admitted too: each factor was, but not with its multiplicity.
  let assembled : Verified.Expr (Fin n) := decoded.foldl
    (fun acc (g, m) ↦ .mul acc (.pow g m)) (ratExprIn constant)
  if let some why := Translate.admit assembled n then
    throwError "the oracle's factorization is refused: {why}"
  let factorForm (g : Verified.Expr (Fin n)) (m : Nat) : Form :=
    let base := Form.ofExpr reified.names g
    if m = 1 then base else .pow base m
  let product := match decoded.toList with
    | [] => Form.num 1
    | (g, m) :: rest =>
        rest.foldl (fun acc (h, k) ↦ .mul acc (factorForm h k)) (factorForm g m)
  let form := if constant = 1 then product else .mul (.num constant) product
  let lhs := Form.ofExpr reified.names reified.expr
  let candidate : Candidate := { form, origin := s!"factorization proposed by {oracle.name}" }
  let some (proposition, proof) ← proveCandidate reified.names lhs candidate
    | throwErrorAt input "factor: the factorization proposed by {oracle.name}, \
        {form.tidy.render}, is refused: the identity with the input does not hold or could not \
        be proved"
  withAuditedEvidence "factor" do
    let report ← liftTermElabM <| evidence
      #[(s!"Identity with the factorization proposed by {oracle.name}", proposition, proof)]
    let hints := decoded.map fun (g, m) ↦
      m!"{(Form.ofExpr reified.names g).tidy.render} is irreducible over ℚ\
        {if m = 1 then "" else s!", with multiplicity {m}"}"
    logReport input {
      domain := renderRealDomain reified.names
      input := reified.render
      inputType := "scalar ℝ"
      output := form.tidy.render
      outputType := "scalar ℝ; the identity is checked, irreducibility is not"
    } #[hintsNode oracle (hints.push m!"the factors are pairwise distinct"), report]

end CASOracle.Factor
