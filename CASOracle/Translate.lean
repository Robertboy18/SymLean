/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS.Elaboration.RealExpression
import DSLean.Gappa.Input
import CASOracle.Oracle
import CASOracle.Syntax
import CASOracle.Wire

/-!
# Requests and answers in the oracles' languages

A request is a checked expression written in an oracle's language, and an answer is text read
back into a checked expression or refused; nothing read is trusted. Cofactors become terms of
any commutative ring through `ringTerm`, which accepts polynomials only.

## Implementation notes

Both directions run DSLean's translations, credited in `CASOracle.Oracle`, on the grammars of
`CASOracle.Syntax`; Gappa's problems are written with DSLean's own grammar `Gappa_input`.

A request is a checked expression written by DSLean (`toExternal'`) from the real term that
`Wire.toTerm` gives it, in a local context that holds only the request's variables. An answer is
read by DSLean (`fromExternal'`) as a real term in a local context that holds only the
variables the task permits, and reflected into a checked expression by CAS's reifier
(`CAS.Elaboration.RealExpression.reify`), which refuses anything outside the checked language.
Before parsing, the text is bounded in length, in digits and in bracket depth; before reflection,
the size of the reflected expression is bounded, since the reifier lowers `tan`, `sinh`, `cosh` and
`tanh` by repeating their argument.
-/

namespace CASOracle.Translate

open Lean Meta Elab Term
open CAS CASOracle.Wire

/-- The language an oracle's requests are written in. -/
def requestLanguage : Oracle → Name
  | .maxima => `maximaOut
  | .pari => `gpOut
  | .gappa => `Gappa_input
  | _ => `sympyOut

/-- The language an oracle's answers are read in. -/
def answerLanguage : Oracle → Name
  | .maxima => `maximaIn
  | _ => `sympyIn

/-- Run `k` in a local context holding exactly the real variables `names`. -/
def withVariables {α : Type} [Inhabited α] (names : List String)
    (k : Array Lean.Expr → TermElabM α) : TermElabM α :=
  withLCtx {} {} <| withLocalDeclsD
    (names.toArray.map fun name ↦ (Name.mkSimple name, fun _ ↦ pure (mkConst ``Real))) k

/-- The innermost reason of a DSLean failure, without its chain of "Type mismatch when filling
in blank" prefixes, on one line, shortened. -/
def reason (error : Exception) : MetaM String := do
  let mut message := (← error.toMessageData.toString).trimAscii.toString
  repeat
    match message.splitOn ": " with
    | first :: rest@(_ :: _) =>
        if first.startsWith "Type mismatch when filling in blank" then
          message := ": ".intercalate rest
        else break
    | _ => break
  let line := (message.splitOn "\n").headD ""
  let line := if line.length > 200 then (line.take 200).toString ++ "…" else line
  if line.startsWith "Syntax error in input" then
    return s!"it is outside the checked language (DSLean: {line})"
  if line.startsWith "Unknown identifier '" then
    let name := ((line.drop "Unknown identifier '".length).toString.splitOn "'").headD ""
    return s!"it uses {name}, which is not a variable of the request"
  if line.startsWith "TODO: scientific syntax elaboration" then
    return "it has a decimal number, outside the checked language"
  if line.startsWith "Elaboration failed: exceeded maximum recursion depth" then
    return "it is nested or chained more than 1000 deep, DSLean's bound"
  return line

/-- Write `expression` in the language `language`, coordinate `i` as the variable `names i`. -/
def write {n : Nat} (language : Name) (names : Fin n → String)
    (expression : Verified.Expr (Fin n)) : TermElabM String := do
  withVariables ((List.finRange n).map names) fun _ ↦ do
    let term ← liftMacroM <| toTerm (fun i ↦ mkIdent (Name.mkSimple (names i))) expression
    let value ← elabTerm term (some (mkConst ``Real))
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar then throwError "the request does not elaborate completely"
    try toExternal' language value
    catch error => throwError "the request cannot be written for the oracle: {← reason error}"

/-! ## Reading answers -/

/-- Refuse a text longer than `limits.text`, with a run of more than `limits.digits` digits, or
with brackets nested deeper than `limits.depth`, before DSLean parses it. -/
def checkText (text : String) (limits : Limits := {}) : Except String Unit := do
  if text.length > limits.text then throw s!"it has over {limits.text} characters"
  let mut digits := 0
  let mut depth := 0
  for c in text.toList do
    if c.isDigit then
      digits := digits + 1
      if digits > limits.digits then throw "a number in it is too long"
    else digits := 0
    if c == '(' || c == '[' || c == '{' then
      depth := depth + 1
      if depth > limits.depth then throw s!"it nests deeper than {limits.depth}"
    if c == ')' || c == ']' || c == '}' then depth := depth - 1

/-- DSLean reads a number `n` as the cast `((n : ℕ) : ℝ)`; write it as the numeral, the form
CAS's reifier reads. Nothing else is rewritten. -/
def numerals (e : Lean.Expr) : MetaM Lean.Expr := do
  Meta.transform (← instantiateMVars e) (post := fun e ↦ do
    if e.isAppOfArity ``NatCast.natCast 3 && (e.getArg! 0).isConstOf ``Real then
      if let some n := (e.getArg! 2).rawNatLit? <|> (e.getArg! 2).nat? then
        return .done (← mkNumeral (mkConst ``Real) n)
    return .continue)

/-- An upper bound for the number of nodes of the reflection of `e`, a term built by the
answer grammars of `CASOracle.Syntax` (applications of constants to such terms, local variables
and literals; no binders, no `let`), saturated at `cap`. Every node of `e` counts, its type and
instance arguments too, and the lowerings of the reifier count
as it builds them: `|a|` as `√(a ^ 2)` (two more nodes), `tan a` as `sin a / cos a`
(`2 s + 3` for an argument of size `s`), `sinh a` and `cosh a` through `exp a` and `exp (-a)`
(`2 s + 6`), and `tanh a` as their quotient (`4 s + 13`). -/
partial def loweredSize (cap : Nat) (e : Lean.Expr) : Nat :=
  let e := e.consumeMData
  let inner := e.getAppArgs.foldl (init := 0) fun total argument ↦
    if total ≥ cap then total else total + loweredSize cap argument
  let size := match e.getAppFn.constName? with
    | some ``abs => inner + 2
    | some ``Real.tan => 2 * inner + 3
    | some ``Real.sinh | some ``Real.cosh => 2 * inner + 6
    | some ``Real.tanh => 4 * inner + 13
    | _ => inner + 1
  min cap size

/-- The number of bits of a natural number (one for zero). -/
def bitLength (k : Nat) : Nat := Nat.log2 k + 1

/-- For an expression built from literals by `+ - * /`, negation and natural powers, upper
bounds for the bits of the numerator and of the denominator of its value, and of every value
computed on the way, before any reduction, each saturated at `limits.bits + 1`; `none` for any
other expression. -/
def numeralBits? {ι : Type} (limits : Limits := {}) : Verified.Expr ι → Option (Nat × Nat)
  | .nat k => some (bitLength k, 1)
  | .int z => some (bitLength z.natAbs, 1)
  | .rat p q => some (bitLength p.natAbs, bitLength q)
  | .add a b | .sub a b => do
      let (n, d) ← numeralBits? limits a
      let (m, e) ← numeralBits? limits b
      return (cap (max (n + e) (m + d) + 1), cap (d + e))
  | .mul a b => do
      let (n, d) ← numeralBits? limits a
      let (m, e) ← numeralBits? limits b
      return (cap (n + m), cap (d + e))
  | .div a b => do
      let (n, d) ← numeralBits? limits a
      let (m, e) ← numeralBits? limits b
      return (cap (n + e), cap (d + m))
  | .neg a => numeralBits? limits a
  | .pow a k => do
      -- `a ^ 0` is one, but the value of `a` is still computed.
      let (n, d) ← numeralBits? limits a
      return if k = 0 then (max n 1, max d 1) else (cap (n * k), cap (d * k))
  | _ => none
where
  /-- A bit count capped just above the budget. -/
  cap (bits : Nat) : Nat := min (limits.bits + 1) bits

/-- The value of an expression built from literals by `+ - * /`, negation and natural powers,
computed only when its numerator and denominator have at most 64 bits by `numeralBits?`. -/
def smallValue? {ι : Type} (expression : Verified.Expr ι) : Option ℚ := do
  let (n, d) ← numeralBits? {} expression
  if n > 64 || d > 64 then none
  value expression
where
  /-- The exact value, or `none` outside the literal fragment or on a zero denominator. -/
  value : Verified.Expr ι → Option ℚ
  | .nat k => some k
  | .int z => some z
  | .rat p q => if q = 0 then none else some ((p : ℚ) / q)
  | .add a b => return (← value a) + (← value b)
  | .sub a b => return (← value a) - (← value b)
  | .mul a b => return (← value a) * (← value b)
  | .div a b => do
      let b ← value b
      if b = 0 then none else return (← value a) / b
  | .neg a => return -(← value a)
  | .pow a k => return (← value a) ^ k
  | _ => none

/-- Real powers whose exponent is an integer, written with literals of at most 64 bits, as
powers; powers of `e` as exponentials; and quotients of literals as rationals. -/
def normalize {ι : Type} : Verified.Expr ι → Verified.Expr ι
  | .rpow a b =>
      match normalize a, normalize b with
      | .exp (.nat 1), b => .exp b
      | a, b =>
          match smallValue? b with
          | some q =>
              if q.den = 1 then
                if 0 ≤ q.num then .pow a q.num.toNat else .div (.nat 1) (.pow a q.num.natAbs)
              else .rpow a b
          | none => .rpow a b
  | .div a b =>
      match normalize a, normalize b with
      | .nat p, .nat q => if q = 0 then .div (.nat p) (.nat q) else ratExprIn ((p : ℚ) / q)
      | a, b => .div a b
  | .add a b => .add (normalize a) (normalize b)
  | .mul a b => .mul (normalize a) (normalize b)
  | .sub a b => .sub (normalize a) (normalize b)
  | .neg a => .neg (normalize a)
  | .pow a k => .pow (normalize a) k
  | .sin a => .sin (normalize a)
  | .cos a => .cos (normalize a)
  | .atan a => .atan (normalize a)
  | .asin a => .asin (normalize a)
  | .acos a => .acos (normalize a)
  | .exp a => .exp (normalize a)
  | .log a => .log (normalize a)
  | .sqrt a => .sqrt (normalize a)
  | other => other

/-- The number of nodes of a checked expression, and its largest natural exponent. -/
def measure {ι : Type} : Verified.Expr ι → Nat × Nat
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b =>
      let (m, k) := measure a
      let (n, l) := measure b
      (m + n + 1, max k l)
  | .neg a | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      let (m, k) := measure a
      (m + 1, k)
  | .pow a j =>
      let (m, k) := measure a
      (m + 1, max k j)
  | _ => (1, 0)

/-- `n + k - 1` choose `k`, the number of monomials of degree `k` in `n` variables, saturated at
`cap`. -/
def multichoose (cap n k : Nat) : Nat := Id.run do
  if n = 0 then return (if k = 0 then 1 else 0)
  let r := min k (n - 1)
  let mut c := 1
  for i in [0:r] do
    c := c * (n + k - 1 - i) / (i + 1)
    if c > cap then return cap
  return min cap c

/-- Heuristic estimates, each saturated, of what simplification, polynomial conversion and
normalization, and interval evaluation can make of an expression. A function counts both as an
atom (of degree one) and as its argument, since a pass may keep it or remove it (`log (exp a)`
becomes `a`), and a real power's exponent may become a number. Expressions that a checker
derives from an answer (derivatives, residuals) are not covered unless the checker admits them
too: the integration command admits the derivative of the proposed primitive (not of its
simplified form, nor the residual), and the differential-equation command each derivative of
the family before simplifying it. -/
structure Bounds where
  /-- The degree of a polynomial built from it. -/
  degree : Nat
  /-- The terms of its expansion, collected. -/
  terms : Nat
  /-- The steps of its expansion: every term of a product or a sum inserted into the collected
  result counts as many steps as that result has terms. -/
  work : Nat := 0
  /-- The bits of the coefficients of an expansion: each literal by its bits and each variable,
  constant or function by one, multiplied by the powers around them. -/
  weight : Nat
  /-- The bits of its largest absolute value with variables of absolute value at most 16. -/
  magnitude : Nat
  /-- A reason to refuse it, if a part is out of every bound. -/
  issue : Option String := none
  deriving Inhabited

/-- The number of subexpressions that a polynomial normalization may take as atoms besides the
variables: functions, real powers, quotients and constants. -/
def atomNodes {ι : Type} : Verified.Expr ι → Nat
  | .add a b | .sub a b | .mul a b => atomNodes a + atomNodes b
  | .div a b | .rpow a b => atomNodes a + atomNodes b + 1
  | .neg a | .pow a _ => atomNodes a
  | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a => atomNodes a + 1
  | .pi | .e => 1
  | _ => 0

/-- The bounds of an expression (`Bounds`) under `limits`, its polynomial normalizations having
at most `atoms` atoms. An expansion forms the product of the terms of two factors before it
collects them, so every such product is bounded too, the powers' repeated products included. An
exponential needs an argument of magnitude at most `2 ^ 16` (its value then has under 100000
bits), and a real power an exponent of magnitude at most `2 ^ 10`. -/
partial def bounds {ι : Type} (limits : Limits) (atoms : Nat) (expression : Verified.Expr ι) :
    Bounds :=
  -- A part whose numbers are over the budget is refused even if what is around it is small
  -- (`log (exp a ^ k)`), since a pass may compute the part itself.
  let result := go expression
  if result.issue.isNone && (result.weight > limits.bits || result.magnitude > limits.bits) then
    { result with issue := some s!"its numbers could need over {limits.bits} bits" }
  else result
where
  /-- The bounds of a subexpression, before the whole-expression budget check. -/
  go : Verified.Expr ι → Bounds
  | expression =>
    let big := limits.bits + 1
    let tcap := limits.terms + 1
    let dcap := limits.exponent + 1
    let wcap := limits.work + 1
    let sat (cap value : Nat) := min cap value
    -- The monomials of degree at most `d` in the atoms.
    let monomials (d : Nat) := multichoose tcap (atoms + 1) d
    let tooMany := s!"its expansion could form products of over {limits.terms} terms"
    -- The terms of the `k`-th power of a polynomial of `t` terms and degree `d`, and the size of
    -- the last product formed on the way.
    let power (t d k : Nat) : Nat × Nat :=
      let result := min (multichoose tcap t k) (monomials (d * k))
      let previous := min (multichoose tcap t (k - 1)) (monomials (d * (k - 1)))
      (result, if k ≤ 1 then t else previous * t)
    match numeralBits? limits expression with
    | some (n, d) =>
        { degree := 0, terms := 1, weight := sat big (n + d), magnitude := sat big n }
    | none =>
      let unary (a : Bounds) (magnitude : Nat) : Bounds :=
        { degree := max a.degree 1, terms := a.terms, work := a.work,
          weight := sat big (a.weight + 1), magnitude, issue := a.issue }
      match expression with
      | .var _ => { degree := 1, terms := 1, weight := 1, magnitude := 4 }
      | .pi | .e => { degree := 0, terms := 1, weight := 1, magnitude := 2 }
      | .add a b | .sub a b =>
          let a := bounds limits atoms a
          let b := bounds limits atoms b
          let degree := sat dcap (max a.degree b.degree)
          let terms := sat tcap (min (a.terms + b.terms) (monomials degree))
          { degree, terms, work := sat wcap (a.work + b.work + (a.terms + b.terms) * terms),
            weight := sat big (a.weight + b.weight),
            magnitude := sat big (max a.magnitude b.magnitude + 1), issue := a.issue <|> b.issue }
      | .mul a b | .div a b =>
          let isDiv := match expression with | .div _ _ => true | _ => false
          let a := bounds limits atoms a
          let b := bounds limits atoms b
          let degree := sat dcap (a.degree + b.degree)
          let product := a.terms * b.terms
          -- A heuristic for the reciprocal of a denominator: its magnitude (`1 / exp a` is
          -- `exp (-a)`) or the bits of the numbers that make it, whichever is larger. A
          -- denominator close to zero for other reasons (`sin (exp (-16))`) is not covered.
          let magnitude := if isDiv then a.magnitude + max b.weight b.magnitude + 4
            else a.magnitude + b.magnitude
          let terms := sat tcap (min product (monomials degree))
          { degree, terms, work := sat wcap (a.work + b.work + product * terms),
            weight := sat big (a.weight + b.weight), magnitude := sat big magnitude,
            issue := a.issue <|> b.issue <|> if product > limits.terms then some tooMany else none }
      | .neg a => bounds limits atoms a
      | .pow a k =>
          let a := bounds limits atoms a
          let (terms, last) := power a.terms a.degree k
          let k' := max k 1
          { degree := sat dcap (a.degree * k), terms := sat tcap terms,
            work := sat wcap (a.work + (k - 1) * last * terms),
            weight := sat big (a.weight * k'), magnitude := sat big (a.magnitude * k'),
            issue := a.issue <|> if last > limits.terms then some tooMany else none }
      | .rpow a b =>
          let a := bounds limits atoms a
          let b := bounds limits atoms b
          -- The exponent may become a number of magnitude up to `2 ^ b.magnitude`.
          let k := 2 ^ min b.magnitude 10
          let (terms, last) := power a.terms a.degree k
          let issue := a.issue <|> b.issue <|>
            if b.magnitude > 10 then
              some "it has a real power with an exponent over 1024 in size"
            else if last > limits.terms then some tooMany else none
          { degree := sat dcap (a.degree * k + b.degree), terms := sat tcap terms,
            work := sat wcap (a.work + b.work + (k - 1) * last * terms),
            weight := sat big (a.weight * k + b.weight),
            magnitude := sat big ((a.magnitude + a.weight) * k), issue }
      | .exp a =>
          let a := bounds limits atoms a
          let issue := a.issue <|>
            if a.magnitude > 16 then
              some "it has an exponential of an argument over 65536 in size"
            else none
          { unary a (sat big (2 * 2 ^ min a.magnitude 16)) with issue }
      | .log a =>
          let a := bounds limits atoms a
          unary a (Nat.log2 (a.magnitude + a.weight + 1) + 2)
      | .sqrt a =>
          let a := bounds limits atoms a
          unary a (a.magnitude / 2 + 1)
      | .sin a | .cos a | .atan a => unary (bounds limits atoms a) 1
      | .asin a | .acos a => unary (bounds limits atoms a) 2
      | _ => { degree := 0, terms := 1, weight := 1, magnitude := 1 }

/-- Refuse an expression in `count` variables, read from an answer or assembled from one,
that some bound of `limits` does not cover: the reason, or `none`. The commands admit each answer
when they read it, and what they assemble or derive from it where the documentation of
`Bounds` says so. -/
def admit {ι : Type} (expression : Verified.Expr ι) (count : Nat) (limits : Limits := {}) :
    Option String :=
  let (size, exponent) := measure expression
  if size > limits.nodes then some s!"it has over {limits.nodes} nodes"
  else if exponent > limits.exponent then some s!"it has an exponent over {limits.exponent}"
  else
    let b := bounds limits (count + atomNodes expression) expression
    if let some issue := b.issue then some issue
    else if b.degree > limits.exponent then some s!"its degree could be over {limits.exponent}"
    else if b.terms > limits.terms then
      some s!"its expansion could form products of over {limits.terms} terms"
    else if b.work > limits.work then some s!"its expansion could take over {limits.work} steps"
    else if b.weight > limits.bits || b.magnitude > limits.bits then
      some s!"its numbers could need over {limits.bits} bits"
    else none

/-- Read `text`, an answer in the language `language`, as a checked expression over the
variables `names`, the only ones the task permits. -/
def read {n : Nat} (language : Name) (names : Fin n → String) (text : String)
    (limits : Limits := {}) : TermElabM (Verified.Expr (Fin n)) := do
  let shown := if text.length > 200 then (text.take 200).toString ++ "…" else text
  let refuse {α : Type} (why : String) : TermElabM α :=
    throwError m!"the oracle's answer is refused: {why}{indentD shown}"
  if let .error why := checkText text limits then refuse why
  withVariables ((List.finRange n).map names) fun coordinates ↦ do
    let term ← try fromExternal' language text (some (mkConst ``Real))
      catch error => refuse (← reason error)
    let term ← numerals term
    if term.hasMVar then refuse "it does not elaborate completely"
    if loweredSize (limits.nodes + 1) term > limits.nodes then
      refuse s!"its reflection would have over {limits.nodes} nodes"
    let reification ← try
        CAS.Elaboration.RealExpression.reify
          { operation := "the oracle's answer", coordinates, unfoldLocal := false } term
      catch error => refuse (← reason error)
    let some expression ← reification.toVerifiedExpr?
      | refuse "an exponent is not a numeral"
    -- The coordinate table only grows, so its size `n` means it is exactly `names`.
    let expression ← if h : reification.dimension = n then pure (h ▸ expression)
      else refuse "it is not an expression in the request's variables"
    let expression := normalize expression
    if let some why := admit expression n limits then refuse why
    return expression

/-- `read` for an oracle's answer language. -/
def readAnswer {n : Nat} (oracle : Oracle) (names : Fin n → String) (text : String) :
    TermElabM (Verified.Expr (Fin n)) :=
  read (answerLanguage oracle) names text

/-- The `;`-separated expressions of a record. -/
def row (payload : String) : List String :=
  (payload.splitOn ";").map (·.trimAscii.toString)

/-! ## Numbers and polynomials -/

/-- The value of an expression built from literals by `+ - * /`, negation and natural powers,
when its numerator and denominator have at most `limits.bits` bits by `numeralBits?` (which
bounds every intermediate value too); `none` otherwise. -/
def constantValue? {ι : Type} (expression : Verified.Expr ι) (limits : Limits := {}) :
    Option ℚ := do
  let (n, d) ← numeralBits? limits expression
  if n + d > limits.bits then none
  smallValue?.value expression

/-- The term of a polynomial answer in any commutative ring, coordinate `i` written as
`atom i` and each rational coefficient as `num q`: rational literals, coordinates, `+ - *`,
negation, natural powers, and division by a nonzero rational literal (as the coefficient of its
inverse). Anything else (a variable denominator, a real power, a function) is refused. -/
partial def ringTerm {n : Nat} (atom : Fin n → Term) (expression : Verified.Expr (Fin n))
    (num : ℚ → MacroM Term := ratTerm) : Except String (MacroM Term) := do
  if let some q := constantValue? expression then return num q
  let rec' := fun sub ↦ ringTerm atom sub num
  match expression with
  | .var i => return pure (atom i)
  | .add a b => let a ← rec' a; let b ← rec' b; return do `($(← a) + $(← b))
  | .sub a b => let a ← rec' a; let b ← rec' b; return do `($(← a) - $(← b))
  | .mul a b => let a ← rec' a; let b ← rec' b; return do `($(← a) * $(← b))
  | .neg a => let a ← rec' a; return do `(-$(← a))
  | .pow a k =>
      if k > ({} : Limits).exponent then throw s!"the exponent {k} is over the limit"
      let a ← rec' a
      return do
        let exponent : Term := ⟨Syntax.mkNumLit (toString k)⟩
        `($(← a) ^ $exponent)
  | .div a b =>
      match constantValue? b with
      | some q =>
          if q = 0 then throw "a cofactor divides by zero"
          let a ← rec' a
          return do `($(← num (1 / q)) * $(← a))
      | none => throw "a cofactor has a variable denominator"
  | _ => throw "a cofactor is not a polynomial"

/-- A product of factors as a rational constant and factors with multiplicities: products,
quotients by constants, negation, and natural powers are split, as in Maxima's `factor`. -/
partial def productFactors {ι : Type} (expression : Verified.Expr ι) :
    Except String (ℚ × List (Verified.Expr ι × Nat)) := do
  if let some q := constantValue? expression then return (q, [])
  match expression with
  | .mul a b =>
      let (c, fs) ← productFactors a
      let (d, gs) ← productFactors b
      return (c * d, fs ++ gs)
  | .div a b =>
      let some q := constantValue? b | throw "the factorization has a denominator"
      if q = 0 then throw "the factorization divides by zero"
      let (c, fs) ← productFactors a
      return (c / q, fs)
  | .neg a =>
      let (c, fs) ← productFactors a
      return (-c, fs)
  | .pow g k => return if k = 0 then (1, []) else (1, [(g, k)])
  | g => return (1, [(g, 1)])

/-! ## Gappa -/

/-- An upper bound for the number of nodes of an expression once its natural powers are written
as products, saturated at `cap`. -/
def expandedSize {ι : Type} (cap : Nat) : Verified.Expr ι → Nat
  | .pow a k => min cap (k * expandedSize cap a + (k - 1) + 1)
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b =>
      min cap (expandedSize cap a + expandedSize cap b + 1)
  | .neg a | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      min cap (expandedSize cap a + 1)
  | _ => 1

/-- Natural powers as products, since Gappa has no power; at most 64. -/
def expandPowers {ι : Type} : Verified.Expr ι → Except String (Verified.Expr ι)
  | .pow a k => do
      if k > 64 then throw "Gappa's powers go up to 64 here"
      if k = 0 then return .nat 1
      let a ← expandPowers a
      return (List.replicate (k - 1) a).foldl (fun acc b ↦ .mul acc b) a
  | .add a b => return .add (← expandPowers a) (← expandPowers b)
  | .mul a b => return .mul (← expandPowers a) (← expandPowers b)
  | .sub a b => return .sub (← expandPowers a) (← expandPowers b)
  | .div a b => return .div (← expandPowers a) (← expandPowers b)
  | .rpow a b => return .rpow (← expandPowers a) (← expandPowers b)
  | .neg a => return .neg (← expandPowers a)
  | .sin a => return .sin (← expandPowers a)
  | .cos a => return .cos (← expandPowers a)
  | .atan a => return .atan (← expandPowers a)
  | .asin a => return .asin (← expandPowers a)
  | .acos a => return .acos (← expandPowers a)
  | .exp a => return .exp (← expandPowers a)
  | .log a => return .log (← expandPowers a)
  | .sqrt a => return .sqrt (← expandPowers a)
  | other => return other

/-- The decimals of a box bound in Gappa's problems. -/
def boxDecimals : Nat := 25

/-- The real term of `q` rounded outward to `boxDecimals` decimals, down for a lower bound and
up for an upper one (Gappa takes only literals in a box, and a wider box is a weaker
hypothesis). -/
def boundTerm (q : ℚ) (lower : Bool) : MacroM Term := do
  let scale : ℚ := 10 ^ boxDecimals
  let m : Int := if lower then ⌊q * scale⌋ else ⌈q * scale⌉
  let digits := toString m.natAbs
  -- At least one digit before the point.
  let digits := String.ofList (List.replicate (boxDecimals + 1 - digits.length) '0') ++ digits
  let whole := digits.take (digits.length - boxDecimals)
  let fraction := digits.drop (digits.length - boxDecimals)
  let literal : Term := ⟨Syntax.mkScientificLit s!"{whole}.{fraction}"⟩
  if m < 0 then `((-($literal : ℝ))) else `(($literal : ℝ))

/-- Gappa's problem `{ v₀ in [a₀, b₀] /\ … -> e in ? }` for the expression on the box, written
by DSLean's `Gappa_input`. -/
def gappaProblem {n : Nat} (names : Fin n → String) (box : Fin n → ℚ × ℚ)
    (expression : Verified.Expr (Fin n)) : TermElabM String := do
  let cap := ({} : Limits).nodes
  if expandedSize (cap + 1) expression > cap then
    throwError "the request cannot be written for gappa: with its powers written as products \
      it has over {cap} nodes"
  let expression ← match expandPowers expression with
    | .ok expression => pure expression
    | .error why => throwError "the request cannot be written for gappa: {why}"
  let body ← write `Gappa_input names expression
  let hypotheses ← withVariables ((List.finRange n).map names) fun _ ↦ do
    let mut terms : Array Term := #[]
    for i in List.finRange n do
      let v := mkIdent (Name.mkSimple (names i))
      let lo ← liftMacroM <| boundTerm (box i).1 true
      let hi ← liftMacroM <| boundTerm (box i).2 false
      terms := terms.push (← `($v ∈ Set.Icc $lo $hi))
    let some last := terms.back? | `(True)
    terms.pop.foldrM (init := last) fun t acc ↦ `($t ∧ $acc)
  let hypothesis ← withVariables ((List.finRange n).map names) fun _ ↦ do
    let value ← elabTerm hypotheses (some (mkSort .zero))
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    try toExternal' `Gappa_input value
    catch error => throwError "the request cannot be written for gappa: {← reason error}"
  return s!"\{ {hypothesis} -> {body} in ? }\n"

/-- A number printed by Gappa: an integer, a decimal, or `m b e` for `m · 2 ^ e`; at most 2000
digits and an exponent of at most 4096 in size. -/
def gappaNumber? (text : String) : Option ℚ := do
  let text := text.trimAscii.toString
  if text.length > 2000 then none
  match text.splitOn "b" with
  | [m, e] =>
      let m ← m.toInt?
      let e ← e.toInt?
      if e.natAbs > 4096 then none
      return if 0 ≤ e then (m * 2 ^ e.toNat : ℚ) else (m : ℚ) / (2 ^ e.natAbs : ℚ)
  | [d] => parseDecimal? d
  | _ => none

/-- The bounds of Gappa's last result line `… in [lo {…}, hi {…}]`, the annotations in braces
(which hold commas) skipped. -/
def gappaBounds? (output : String) : Option (ℚ × ℚ) := do
  let line ← ((output.splitOn "\n").filter (fun l ↦ (l.splitOn " in [").length > 1)).getLast?
  let interval := (line.splitOn " in [").getLast!
  let interval := ("]".intercalate ((interval.splitOn "]").dropLast))
  let mut depth := 0
  let mut current := ""
  let mut parts : Array String := #[]
  for c in interval.toList do
    if c == '{' then depth := depth + 1
    else if c == '}' then depth := depth - 1
    else if depth == 0 then
      if c == ',' then
        parts := parts.push current
        current := ""
      else current := current.push c
  parts := parts.push current
  let #[lo, hi] := parts | none
  return (← gappaNumber? lo, ← gappaNumber? hi)

end CASOracle.Translate
