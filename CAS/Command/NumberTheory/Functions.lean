/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NumberTheory.Modular
public import CAS.Command.NumberTheory.Factoring
public import CAS.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatFactorial
public meta import CAS.Tactic.RouteRegistry

/-!
# Number-theoretic functions: divisors, divisor sums, the totient, binomial coefficients,
factorials, Fibonacci numbers, digits and continued fractions

The mode `#cas [divisors] n` and the calls `divisorSigma k n`, `eulerPhi n`, `binomial n k`,
`factorial n` and `fibonacci n` prove `Nat.divisors n = {…}`, `ArithmeticFunction.sigma k n = s`,
`Nat.totient n = t`, `Nat.choose n k = c`, `Nat.factorial n = f` and `Nat.fib n = F` for
Mathlib's functions at numerals. The modes `integerDigits`, `continuedFraction` and
`fromContinuedFraction` follow Mathematica's `IntegerDigits`, `ContinuedFraction` and
`FromContinuedFraction`. They prove `Nat.digits b n = […]` (Mathlib lists digits least
significant first, and the digits of `0` are `[]`; the report prints them in Mathematica's order)
and, for a continued fraction `[a₀; a₁, …, aₖ]` of a rational `q`, the identity
`q = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ))` together with `aᵢ ≥ 1` for `i ≥ 1` and `aₖ ≥ 2` when
`k ≥ 1`, which determine the expansion.

## Main definitions

* `CAS.Command.NumberTheory.divisorsEvidence`: `Nat.divisors n = {…}` with its proof by the
  divisor certificate of `CAS.NumberTheory.divisors_eq_of_cert`.
* `CAS.Command.NumberTheory.logDivisorSigma`, `CAS.Command.NumberTheory.logTotient`,
  `CAS.Command.NumberTheory.logBinomial`, `CAS.Command.NumberTheory.logFactorial`,
  `CAS.Command.NumberTheory.logFibonacci`: the reports of the calls, which
  `CAS.Command.Calls` runs on evaluated arguments.

## Implementation notes

The divisors come with the counting certificate of `CAS/NumberTheory/Divisors.lean`, which costs
the kernel `⌊√n⌋` divisions where `decide +kernel` on Mathlib's definitions filters all of
`[0, n]`, so they reach `n < 10^12`; the Finset literal of the statement, with up to `6720`
elements there, is matched with the certified list in pieces of `512`. The totient has no such
certificate without the prime factors, so without Hex it is a count of the `d < n` coprime to
`n`, up to `10^5`; with `CASHex.NumberTheory` it comes from Hex's factorization. Factorials
and Fibonacci numbers use Mathlib's `norm_num` extensions. So do binomial coefficients, written
as `n (n - 1) ⋯ (n - j + 1) / j!` for the smaller `j` of `k` and `n - k`, so that no proof
computes `n!`. Before any proof, we compute the factorials `i!`, the Fibonacci numbers `F_i`, the
binomial coefficients `C(n, i)` for `i ≤ j` and the powers and partial sums of a divisor sum one
step at a time, by `Arguments.mulBelow?`, `Arguments.addBelow?` and `Arguments.powBelow?`, which
compare each product, sum and power with `10 ^ 10000` before they form it. A binomial step is
`C(n, i + 1) = (C(n, i) / g) ((n - i) / ((i + 1) / g))` for `g = gcd (C(n, i)) (i + 1)`, with
both divisions exact, so that its product is `C(n, i + 1)` itself. Each partial value is at most
the value, so this computation refuses a call exactly when its value has more than `10000`
digits and forms no partial value with more digits. After this check, the proof of a binomial
coefficient still forms the product `n (n - 1) ⋯ (n - j + 1)`, which is `j!` times the value,
when `norm_num` evaluates `Nat.descFactorial n j`; its partial products, `j!` and the quotient
are smaller. Since `C(n, j) ≥ C(2 j, j)` and `C(33228, 16614) ≥ 10 ^ 10000`, an accepted call has
`j ≤ 16613`, so the product is below `10 ^ 10000 · 16613!` and has at most `72902` digits
(`16613!` has `62902`); `binomial (10 ^ 5000 + 1) 2` forms `10 ^ 10000 + 10 ^ 5000`. A proof
along `C(n, i + 1) (i + 1) = C(n, i) (n - i)` would stay within a factor `j` of the bound, but
it would state `j` numerals of up to `10000` digits and have the kernel check `j` products, so
we keep the one product.
-/

public meta section

namespace CAS.Command.NumberTheory

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (natTerm ratText proveStatement checkedEvidence)

/-- The divisors of `n` are certified for `n` below this bound, `10^12`. -/
def divisorBound : Nat := 10 ^ 12

/-- The totient of `n` is counted without a factorization for `n` up to this bound. -/
def totientCountBound : Nat := 100000

/-- The number of halvings after which each piece of a `rangeSum` over `m` terms has at most `512`
terms. -/
def scanDepth (m : Nat) : Nat := Id.run do
  let mut depth := 0
  while 512 * 2 ^ depth < m do depth := depth + 1
  return depth

/-- The divisors of `n`, in increasing order, by trial division up to `⌊√n⌋`. -/
def divisorsOf (n : Nat) : List Nat := Id.run do
  let mut small : Array Nat := #[]
  let mut large : List Nat := []
  let mut d := 1
  while d * d ≤ n do
    if n % d = 0 then
      small := small.push d
      if d * d ≠ n then large := (n / d) :: large
    d := d + 1
  return small.toList ++ large

/-- The literal `[d₁, …, dₖ] : List ℕ`. -/
def natListExpr (ds : List Nat) : Lean.Expr :=
  ds.foldr (fun d acc ↦ mkApp3 (Lean.mkConst ``List.cons [Level.zero]) (Lean.mkConst ``Nat)
    (mkNatLit d) acc) (mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Nat))

/-- `Eq.refl true`, the proof of a Boolean certificate that the kernel evaluates to `true`. -/
def trueRefl : Lean.Expr :=
  mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)

/-- For a nonempty array `ds`: the list literal `l` of its entries, the Finset literal
`S = {d₁, …, dₖ}` and a proof of `l.toFinset = S`, assembled from pieces of `512` entries by
`CAS.NumberTheory.toFinset_append_eq_insertAll`. -/
def finsetProof (ds : Array Nat) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let piece := 512
  let nat := Lean.mkConst ``Nat
  let finset := mkApp (Lean.mkConst ``Finset [Level.zero]) nat
  let ins ← synthInstance (mkApp2 (Lean.mkConst ``Insert [Level.zero, Level.zero]) nat finset)
  let sg ← synthInstance (mkApp2 (Lean.mkConst ``Singleton [Level.zero, Level.zero]) nat finset)
  let k := ds.size
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) nat
  -- `lists[i]` is the list literal of `ds[i:]`, and `sets[i]` the Finset literal of its entries.
  let mut lists : Array Lean.Expr := Array.replicate (k + 1) nil
  let mut sets : Array Lean.Expr := Array.replicate k nil
  for j in [0:k] do
    let i := k - 1 - j
    lists := lists.set! i
      (mkApp3 (Lean.mkConst ``List.cons [Level.zero]) nat (mkNatLit ds[i]!) lists[i + 1]!)
    sets := sets.set! i <| if i + 1 = k then
        mkApp4 (Lean.mkConst ``Singleton.singleton [Level.zero, Level.zero]) nat finset sg
          (mkNatLit ds[i]!)
      else
        mkApp5 (Lean.mkConst ``Insert.insert [Level.zero, Level.zero]) nat finset ins
          (mkNatLit ds[i]!) sets[i + 1]!
  let last := piece * ((k - 1) / piece)
  let mut proof := mkApp2 (Lean.mkConst ``CAS.NumberTheory.toFinset_eq_insertChain)
    (mkNatLit ds[last]!) lists[last + 1]!
  let mut start := last
  while start > 0 do
    let s := start - piece
    proof := mkApp4 (Lean.mkConst ``CAS.NumberTheory.toFinset_append_eq_insertAll)
      (natListExpr (ds.extract s start).toList) lists[start]! sets[start]! proof
    start := s
  return (lists[0]!, sets[0]!, proof)

/-- The proposition `Nat.divisors n = {d₁, …, dₖ}` for `0 < n`, its proof by the divisor
certificate, and the divisors. -/
def divisorsEvidence (n : Nat) : MetaM (Lean.Expr × Lean.Expr × List Nat) := do
  let ds := divisorsOf n
  let (l, S, toFinset) ← finsetProof ds.toArray
  let m := Nat.sqrt n
  let cert := mkApp5 (Lean.mkConst ``CAS.NumberTheory.divisors_eq_of_cert) (mkNatLit n)
    (mkNatLit m) (mkNatLit (scanDepth m)) l trueRefl
  return (← mkEq (mkApp (Lean.mkConst ``Nat.divisors) (mkNatLit n)) S,
    ← mkEqTrans cert toFinset, ds)

/-- Refuse an `n` outside `[1, 10^12)` for the divisor certificate of `operation`, at the
argument `argument` that denotes `n`, which the refusal quotes as written. -/
def checkDivisorRange (operation : String) (n : Nat) (argument : Syntax) :
    CommandElabM Unit := do
  if n = 0 then throwErrorAt argument "{operation}: expected a positive natural number"
  if n ≥ divisorBound then
    throwErrorAt argument "{operation}: the divisors are certified for n < 10^12; \
      `{Arguments.argumentText argument}` is beyond that bound"

/-- Run `x` with the options that print a Finset literal of thousands of elements in full. -/
def withLongLiterals {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun scope ↦ { scope with
    opts := pp.maxSteps.set (maxRecDepth.set (scope.opts.setBool `pp.deepTerms true) 100000)
      1000000 }) x

/-- Run `#cas [divisors] n`. -/
def logDivisors (ref input : Syntax) : CommandElabM Unit := do
  let n ← parseNat "divisors" input
  checkDivisorRange "divisors" n input
  withLongLiterals do
    let (proposition, proof, ds) ← liftTermElabM <| divisorsEvidence n
    logNumber ref "divisors" s!"{n}" s!"{ds}" "divisors" proposition proof

/-- `∑ d ∈ ds, d ^ k` when it is below `Arguments.resultLimit`, and `none` otherwise; for the
divisors `ds` of `n` this is `σₖ(n)`. Each power `d ^ k` and each partial sum is at most the sum
and is compared with the limit before it is formed, so the first one at or above the limit shows
that the sum is too. -/
def sigmaBelow? (k : Nat) (ds : List Nat) : Option Nat :=
  ds.foldlM (init := 0) fun acc d ↦ do Arguments.addBelow? acc (← Arguments.powBelow? d k)

/-- Run the call `divisorSigma k n` on its evaluated arguments; `argument` is the argument `n` as
written and `input` is the call. -/
def logDivisorSigma (ref : Syntax) (k n : Nat) (argument input : Syntax) :
    CommandElabM Unit := do
  checkDivisorRange "divisorSigma" n argument
  -- `σₖ(n) ≥ n ^ k`, so a power `n ^ k` above the limit refuses before any divisor is listed.
  if (Arguments.powBelow? n k).isNone then Arguments.refuseValueSize "divisorSigma" input
  -- The kernel evaluates `d ^ k` for exponents below `2 ^ 32`; only `n = 1` gets this far with
  -- a larger `k`.
  if k ≥ 2 ^ 32 then
    throwErrorAt input "divisorSigma: the kernel evaluates the powers d ^ k of the certificate \
      for k < 2^32 only"
  let ds := divisorsOf n
  let some s := sigmaBelow? k ds | Arguments.refuseValueSize "divisorSigma" input
  let m := Nat.sqrt n
  let proof := mkAppN (Lean.mkConst ``CAS.NumberTheory.sigma_eq_of_cert)
    #[mkNatLit k, mkNatLit n, mkNatLit m, mkNatLit (scanDepth m), mkNatLit s, natListExpr ds,
      trueRefl, trueRefl]
  let proposition ← liftTermElabM <| inferType proof
  logNumber ref s!"divisorSigma {k}" s!"{n}" s!"{s}" s!"divisorSigma {k}" proposition proof

/-- The proposition `Nat.totient n = t`, its proof by the count of
`CAS.NumberTheory.totient_eq_rangeSum`, and `t`. -/
def totientEvidence (n : Nat) : MetaM (Lean.Expr × Lean.Expr × Nat) := do
  let t := (List.range n).foldl (fun acc d ↦ if Nat.gcd n d = 1 then acc + 1 else acc) 0
  let proof := mkApp2 (Lean.mkConst ``CAS.NumberTheory.totient_eq_rangeSum) (mkNatLit n)
    (mkNatLit (scanDepth n))
  return (← mkEq (mkApp (Lean.mkConst ``Nat.totient) (mkNatLit n)) (mkNatLit t), proof, t)

/-- Run the call `eulerPhi n` on its evaluated argument; `input` is the argument. For `n ≥ 2` the
backend of `CASHex.NumberTheory`, when it is imported, computes `φ(n)` from Hex's factorization.
Otherwise the kernel counts for `n ≤ totientCountBound`, and the call refuses beyond. -/
def logTotient (ref : Syntax) (n : Nat) (input : Syntax) : CommandElabM Unit := do
  if 2 ≤ n then
    if ← Tactic.RouteRegistry.runCommandBackends `eulerPhi input then return
  unless n ≤ totientCountBound do
    throwErrorAt input "eulerPhi counts the residues coprime to n ≤ {totientCountBound} without \
      Hex; for `{Arguments.argumentText input}`, `import CASHex.NumberTheory` computes φ from the \
      factorization"
  let (proposition, proof, t) ← liftTermElabM <| totientEvidence n
  logNumber ref "eulerPhi" s!"{n}" s!"{t}" "eulerPhi" proposition proof

/-- `C(n, j)` for `2 j ≤ n` when it is below `Arguments.resultLimit`, and `none` otherwise, by
`C(n, i + 1) = (C(n, i) / g) ((n - i) / ((i + 1) / g))` for `g = gcd (C(n, i)) (i + 1)`, where
both divisions are exact. The values `C(n, i)` for `i ≤ j` never exceed `C(n, j)`, and
`Arguments.mulBelow?` compares each with the limit before it is formed, so the first one at or
above the limit shows that `C(n, j)` is too. -/
def chooseBelow? (n j : Nat) : Option Nat := Id.run do
  let mut c := 1
  for i in [0:j] do
    let g := Nat.gcd c (i + 1)
    let some next := Arguments.mulBelow? (c / g) ((n - i) / ((i + 1) / g)) | return none
    c := next
  return some c

/-- Run the call `binomial n k` on its evaluated arguments; `input` is the call. -/
def logBinomial (ref : Syntax) (n k : Nat) (input : Syntax) : CommandElabM Unit := do
  -- `C(n, k) = C(n, j)` for the smaller `j` of `k` and `n - k`, and `0` for `k > n`.
  let j := min k (n - k)
  let some c := (if k ≤ n then chooseBelow? n j else some 0)
    | Arguments.refuseValueSize "binomial" input
  -- The proof writes `C(n, j)` as `n (n - 1) ⋯ (n - j + 1) / j!`, a product of at most `72902`
  -- digits (see the module note).
  let tactic ← if k ≤ n then
      if j = k then
        `(tactic| (rw [Nat.choose_eq_descFactorial_div_factorial] <;> norm_num))
      else
        `(tactic| (rw [← Nat.choose_symm (by norm_num : $(natTerm k) ≤ $(natTerm n)),
          Nat.choose_eq_descFactorial_div_factorial] <;> norm_num))
    else `(tactic| exact Nat.choose_eq_zero_of_lt (by norm_num))
  let (proposition, proof) ← liftTermElabM <| proveStatement "binomial"
    (← `(Nat.choose $(natTerm n) $(natTerm k) = $(natTerm c))) tactic
  logNumber ref "binomial" s!"({n}, {k})" s!"{c}" "binomial" proposition proof

/-- `n!` when it is below `Arguments.resultLimit`, and `none` otherwise, by multiplying
`2, 3, …, n` in turn. Every partial product `i!` is at most `n!`, so the first one at or above
the limit shows that `n!` is too. -/
def factorialBelow? (n : Nat) : Option Nat := Id.run do
  let mut f := 1
  for i in [2:n + 1] do
    match Arguments.mulBelow? f i with
    | some p => f := p
    | none => return none
  return some f

/-- `F_n` when it is below `Arguments.resultLimit`, and `none` otherwise, by
`F_{i+2} = F_{i+1} + F_i`, which forms `F_2, …, F_n`. Every `F_i` for `i ≤ n` is at most `F_n`,
and `Arguments.addBelow?` compares each sum with the limit before it is formed, so the first one
at or above the limit shows that `F_n` is too. -/
def fibonacciBelow? (n : Nat) : Option Nat := Id.run do
  if n = 0 then return some 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let some s := Arguments.addBelow? a b | return none
    a := b
    b := s
  return some b

/-- Run the call `factorial n` on its evaluated argument; `input` is the call. -/
def logFactorial (ref : Syntax) (n : Nat) (input : Syntax) : CommandElabM Unit := do
  let some f := factorialBelow? n | Arguments.refuseValueSize "factorial" input
  let (proposition, proof) ← liftTermElabM <| proveStatement "factorial"
    (← `(Nat.factorial $(natTerm n) = $(natTerm f)))
    (← `(tactic| first | norm_num [Nat.factorial] | decide +kernel))
  logNumber ref "factorial" s!"{n}" s!"{f}" "factorial" proposition proof

/-- Run the call `fibonacci n` on its evaluated argument; `input` is the call. -/
def logFibonacci (ref : Syntax) (n : Nat) (input : Syntax) : CommandElabM Unit := do
  let some F := fibonacciBelow? n | Arguments.refuseValueSize "fibonacci" input
  let (proposition, proof) ← liftTermElabM <| proveStatement "fibonacci"
    (← `(Nat.fib $(natTerm n) = $(natTerm F))) (← `(tactic| norm_num))
  logNumber ref "fibonacci" s!"{n}" s!"{F}" "fibonacci" proposition proof

/-- Run `#cas [integerDigits] (n, b)`. -/
def logDigits (ref input : Syntax) : CommandElabM Unit := do
  let args ← parseNatTuple "integerDigits" input
  let (n, b) ← match args with
    | #[n] => pure (n, 10)
    | #[n, b] => pure (n, b)
    | _ => throwErrorAt input "integerDigits: expected `n` or `(n, b)`"
  if b < 2 then throwErrorAt input "integerDigits: the base must be at least 2"
  let digits := Nat.digits b n
  let (proposition, proof) ← liftTermElabM <| proveStatement "integerDigits"
    (← `(Nat.digits $(natTerm b) $(natTerm n) = ([$(digits.toArray.map natTerm),*] : List ℕ)))
    (← `(tactic| first | norm_num | decide +kernel | simp))
  logNumber ref "integerDigits" s!"{n} in base {b}" s!"{digits.reverse}"
    "digits, most significant first (Mathlib's Nat.digits lists them in reverse)" proposition proof

/-- The continued fraction `[a₀; a₁, …]` of a rational, by Euclid's algorithm. -/
partial def continuedFractionOf (q : ℚ) : List Int :=
  let a := q.floor
  let r := q - a
  if r = 0 then [a] else a :: continuedFractionOf (1 / r)

/-- The value `a₀ + 1 / (a₁ + 1 / (⋯))`. -/
def continuedFractionValue : List Int → ℚ
  | [] => 0
  | [a] => a
  | a :: rest => a + 1 / continuedFractionValue rest

/-- The nested fraction as term syntax. -/
def continuedFractionTerm : List Int → TermElabM (TSyntax `term)
  | [] => `(0)
  | [a] => intTerm a
  | a :: rest => do `($(← intTerm a) + 1 / ($(← continuedFractionTerm rest)))

/-- Run `#cas [continuedFraction] q` or `#cas [fromContinuedFraction] [a₀, a₁, …]`. -/
def logContinuedFraction (ref : Syntax) (forward : Bool) (input : Syntax) : CommandElabM Unit := do
  let operation := if forward then "continuedFraction" else "fromContinuedFraction"
  let (q, terms) ← if forward then do
      let q ← parseRationalLiteralFor operation
        "expected an exact rational literal, such as 415/93, -7/3 or 3.14159" input
      pure (q, continuedFractionOf q)
    else do
      let terms ← match input with
        | `([$entries,*]) => entries.getElems.mapM fun e ↦ do
            let v ← parseRationalLiteralFor operation "expected integers" e
            unless v.den = 1 do throwErrorAt e "{operation}: expected integers"
            pure v.num
        | _ => throwErrorAt input "{operation}: expected a list `[a₀, a₁, …]`"
      let terms := terms.toList
      if terms.isEmpty then throwErrorAt input "{operation}: the list is empty"
      unless terms.drop 1 |>.all (· ≥ 1) do
        throwErrorAt input "{operation}: the terms after the first must be positive"
      pure (continuedFractionValue terms, terms)
  -- The identity, with the conditions that make the expansion the canonical one: the terms
  -- after the first are positive, and the last is at least `2` when there are two or more.
  let tail := terms.drop 1
  let (proposition, proof) ← liftTermElabM do
    let identity ← `((($(← ratSyntax q)) : ℚ) = $(← continuedFractionTerm terms))
    if tail.isEmpty || !forward then
      proveStatement operation identity (← `(tactic| norm_num))
    else
      let tailT ← `(([$(← tail.toArray.mapM intTerm),*] : List ℤ))
      proveStatement operation
        (← `($identity ∧ (∀ a ∈ $tailT, 1 ≤ a) ∧ 2 ≤ $(← intTerm tail.getLast!)))
        (← `(tactic| exact ⟨by norm_num, by decide, by decide⟩))
  let shown := if terms.length = 1 then s!"[{terms.head!}]"
    else s!"[{terms.head!}; " ++ ", ".intercalate ((terms.drop 1).map toString) ++ "]"
  logReport ref {
    domain := "ℚ"
    input := if forward then ratText q else s!"{terms}"
    inputType := if forward then "rational number" else "continued fraction"
    output := if forward then shown else ratText q
    outputType := if forward then "continued fraction" else "rational number"
  } #[← liftTermElabM <| checkedEvidence operation "Value of the continued fraction" proposition
      proof]

end CAS.Command.NumberTheory

namespace CAS.Command

open Lean Elab Command

/-- `#cas [divisors] n` lists the divisors of a positive natural number `n` and proves that the list
is complete.

## Theorem
The report proves `Nat.divisors n = {d₁, …, dₖ}`, an equation of `Finset ℕ` for Mathlib's
`Nat.divisors`, by `CAS.NumberTheory.divisors_eq_of_cert`. The kernel checks a counting
certificate with `⌊√n⌋` divisions and no factorization: the listed divisors up to `⌊√n⌋` divide
`n` and are as many as the `d ≤ ⌊√n⌋` with `d ∣ n`, and the others are their cofactors `n / d`.
The report prints the divisors in increasing order.

## Conditions and limits
`n` is a natural number, a literal or a closed integer expression, with `1 ≤ n < 10^12`, so the
kernel performs at most a million divisions.

## Options
None.

## Examples
```lean
#cas [divisors] 360
```
```output
Output (divisors): [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90,
120, 180, 360]
```
```lean
#cas [divisors] 12
```
```output
Output (divisors): [1, 2, 3, 4, 6, 12]
```

## In a proof
```lean
theorem divisors_twelve : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by
  cas
```

## See also
Mathematica `Divisors`, SymPy `divisors`. The calls `divisorSigma k n` and `eulerPhi n`, and the
mode `factorInteger`.

## Possible issues
```lean
#cas [divisors] (10^12)
```
```output
divisors: the divisors are certified for n < 10^12; `10^12` is beyond that bound
```
With Hex, `#cas [factorInteger] n` factors larger numbers, and the divisors are the products of
the prime powers it lists.
```lean
#cas [divisors] 0
```
```output
divisors: expected a positive natural number
```
Every natural number divides `0`; Mathlib sets `Nat.divisors 0 = ∅`.
-/
syntax (name := casDivisorsCommand) "#cas" "[" &"divisors" "]" term : command

/-- `#cas [integerDigits] (n, b)` lists the digits of a natural number `n` in base `b`, most
significant first, and proves them.

## Theorem
The report proves `Nat.digits b n = [d₀, d₁, …, dₖ]` for Mathlib's `Nat.digits`, which lists
the digits least significant first; the report prints the reverse `[dₖ, …, d₁, d₀]`. `norm_num`
proves the equation, with `decide +kernel` and `simp` as fallbacks.

## Conditions and limits
`n` and `b` are natural numbers, literals or closed integer expressions, with `b ≥ 2`, and
`#cas [integerDigits] n` uses base `10`. The digits of `0` form the empty list, as
`Nat.digits b 0 = []`.

## Options
None.

## Examples
```lean
#cas [integerDigits] (1234, 2)
```
```output
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)):
[1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0]
```
```lean
#cas [integerDigits] 2026
```
```output
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)):
[2, 0, 2, 6]
```
```lean
#cas [integerDigits] (0, 10)
```
```output
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)): []
```

## In a proof
```lean
theorem digits_1234 : Nat.digits 2 1234 = [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] := by
  cas
```

## See also
Mathematica `IntegerDigits`, SymPy `digits`, Mathlib `Nat.ofDigits`. The call `powerMod a b m`,
for the last digits `a ^ b % 10 ^ k` of a large power.

## Possible issues
```lean
#cas [integerDigits] (1234, 1)
```
```output
integerDigits: the base must be at least 2
```
Base `1` has no positional digits; Mathlib's `Nat.digits 1 n` is the list of `n` ones.
-/
syntax (name := casIntegerDigitsCommand) "#cas" "[" &"integerDigits" "]" term : command
/-- `#cas [continuedFraction] q` computes the finite continued fraction `[a₀; a₁, …, aₖ]` of a
rational number `q` and proves it.

## Theorem
The report proves `q = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ))` in `ℚ`, and for `k ≥ 1` also
`(∀ a ∈ [a₁, …, aₖ], 1 ≤ a) ∧ 2 ≤ aₖ`, the conditions that make the expansion unique. The terms
come from Euclid's algorithm with `a₀ = ⌊q⌋`; `norm_num` proves the identity and `decide` the
conditions.

## Conditions and limits
`q` is a rational literal, built from natural and decimal literals with `-` and `/`, such as
`415/93`, `-7/3` or `0.25`. A decimal is read as the exact rational it denotes, so `3.14159` is
`314159/100000`. An integer `n` gives `[n]`, and an irrational number, whose continued fraction
is infinite, is refused.

## Options
None.

## Examples
```lean
#cas [continuedFraction] (415/93)
```
```output
Output (continued fraction): [4; 2, 6, 7]
```
```lean
#cas [continuedFraction] (3.14159)
```
```output
Output (continued fraction): [3; 7, 15, 1, 25, 1, 7, 4]
```
```lean
#cas [continuedFraction] (-7/3)
```
```output
Output (continued fraction): [-3; 1, 2]
```

## In a proof
```lean
theorem continued_fraction_415_93 : (415 / 93 : ℚ) = 4 + 1 / (2 + 1 / (6 + 1 / 7)) := by
  cas
```

## See also
Mathematica `ContinuedFraction`, SymPy `continued_fraction`. The modes `fromContinuedFraction`
and `extendedGCD`, whose Euclidean algorithm computes the same quotients.

## Possible issues
```lean
#cas [continuedFraction] (sqrt 2)
```
```output
continuedFraction: expected an exact rational literal, such as 415/93, -7/3 or 3.14159
```
The mode expands rational literals only, since the continued fraction of an irrational number
such as `sqrt 2` is infinite. A decimal approximation from `#cas [N d] e` is a rational literal
and has a finite continued fraction.
-/
syntax (name := casContinuedFractionCommand) "#cas" "[" &"continuedFraction" "]" term : command
/-- `#cas [fromContinuedFraction] [a₀, a₁, …, aₖ]` computes the rational value of a finite continued
fraction and proves it.

## Theorem
The report proves `q = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ))` in `ℚ` by `norm_num`, for the printed
rational `q` in lowest terms.

## Conditions and limits
The list is nonempty and holds integer literals. `a₀` may be zero or negative, and the later
terms are positive. The last term may be `1`, so `[1, 1, 1]` and `[1, 2]` have the same value.

## Options
None.

## Examples
```lean
#cas [fromContinuedFraction] [4, 2, 6, 7]
```
```output
Output (rational number): 415/93
```
```lean
#cas [fromContinuedFraction] [1, 1, 1]
```
```output
Output (rational number): 3/2
```

## In a proof
```lean
theorem from_continued_fraction_ones : (3 / 2 : ℚ) = 1 + 1 / (1 + 1 / 1) := by
  cas
```

## See also
Mathematica `FromContinuedFraction`, SymPy `continued_fraction_reduce`. The mode
`continuedFraction`.

## Possible issues
```lean
#cas [fromContinuedFraction] []
```
```output
fromContinuedFraction: the list is empty
```
A continued fraction has at least the term `a₀`.
```lean
#cas [fromContinuedFraction] [1, 0, 2]
```
```output
fromContinuedFraction: the terms after the first must be positive
```
Only `a₀` may be zero or negative.
-/
syntax (name := casFromContinuedFractionCommand)
  "#cas" "[" &"fromContinuedFraction" "]" term : command

elab_rules : command
  | `(#cas [divisors] $e:term) => NumberTheory.logDivisors e e
  | `(#cas [integerDigits] $e:term) => NumberTheory.logDigits e e
  | `(#cas [continuedFraction] $e:term) => NumberTheory.logContinuedFraction e true e
  | `(#cas [fromContinuedFraction] $e:term) => NumberTheory.logContinuedFraction e false e

end CAS.Command
