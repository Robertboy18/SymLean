/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Syntax
public import CAS.Expr.Syntax
public meta import CAS.Command.FunctionTable
public meta import CAS.Expr.Syntax

/-!
# Integer and rational arguments of `#cas` calls

The integer arguments of the calls, such as the `100` of `eulerPhi 100` or the degree of
`ChebyshevT 5 x`, are closed integer expressions like `2 ^ 64 + 1` or `10 / 2`. `evalInteger`
evaluates them before any proof starts, and the theorem of the call states the evaluated
numerals. The rational arguments, such as the `5/2` of `gamma (5/2)`, are closed expressions of
the calculator, which `rationalValue` evaluates. Both evaluations refuse an argument rather than
form a sum, a product, a power or the value of a decimal literal with more than `10000` decimal
digits, in the numerator or the denominator for a rational number.

## Main definitions

* `CAS.Command.Arguments.evalInteger`: the integer that an argument denotes.
* `CAS.Command.Arguments.natArgument`: the same for a natural argument, refusing negative values.
* `CAS.Command.Arguments.Arithmetic`: the arithmetic of a subterm, by its ascription.
* `CAS.Command.Arguments.rationalValue`: the rational value of a closed expression.
* `CAS.Command.Arguments.mulBelow?`, `CAS.Command.Arguments.addBelow?`,
  `CAS.Command.Arguments.powBelow?`: products, sums and powers below `resultLimit = 10 ^ 10000`,
  the size guard; `ratMulBelow?`, `ratAddBelow?` and `ratPowBelow?` are the same for rational
  numbers, and `polyEvalBelow?` evaluates a polynomial with them.
* `CAS.Command.Arguments.decimalRefusal?`, `CAS.Command.Arguments.oversizedDecimal?`: the test of
  a decimal literal before its value is formed.
* `CAS.Command.Arguments.variableName?`: the variable that an argument names, such as the `x` of
  `ChebyshevT 5 x`.

## Implementation notes

We evaluate the arguments in meta code rather than in the kernel, since the numeral in the
theorem is what every later proof step computes with. Without an ascription an argument is read
as the calculator reads its input, as a real number, so it has to be an integer: `a / b` divides
exactly, `a - b` may be negative and a power has no negative exponent. An ascription `(a : ℕ)`
or `(a : ℤ)` evaluates `a` with Lean's arithmetic of that type, so `(1 - 2 : ℕ)` is `0` and
`(7 / 2 : ℤ)` is `3`, as in Lean. We follow the truncated subtraction of `ℕ` rather than refuse
it, since the ascription asks for exactly that arithmetic. Any other ascription is refused:
dropping it would change what the argument means.

The integer guard is exact on each operation once its operands have passed the guard: a sum, a
product or a power of such operands is refused when its value has more than `10000` digits, and
only then, and it is not formed. An argument is evaluated from its leaves, so
`10 ^ 10000 - 10 ^ 10000`, of value `0`, is refused at `10 ^ 10000`. A product `a b` is formed
only once `a ≤ (10 ^ 10000 - 1) / b`, and a sum of two numbers of the same sign only once
`|a| < 10 ^ 10000 - |b|`. A power is computed by squaring, and each partial power, which is at
most the power, passes the test of a product first. A sum of two numbers of opposite signs, a
quotient and a remainder are no larger than their operands. A numeral is refused when it has
more than `10000` digits. A decimal literal `m × 10 ^ (±e)` is refused by `decimalRefusal?` when
its mantissa `m`, the number that its digits form without the point, has more than `10000`
digits, with a refusal of its own since the value may be small: that of `1.` followed by `10000`
zeros is `1`. It is refused as well when the power is positive and `d + e > 10000` for the
number `d` of digits of `m`, which holds exactly when the value has more than `10000` digits.
Neither the value nor the power of ten is formed for these tests.

A rational argument is read by the calculator's parser and evaluated with the arithmetic of
`CAS.Verified.Expr.evalRat?`. Its decimal literals pass the tests of `decimalRefusal?` first
(`oversizedDecimal?`), so the parser, which forms the value of a decimal literal and refuses one
with a power of ten over `1000`, forms no value past the bound. Of what the parser accepts, a
literal is refused exactly when the numerator or the denominator of its value in lowest terms has
more than `10000` digits, and so is a product, a quotient or a power once its operands have passed
the guard. Here too the evaluation starts at the leaves: `(10 ^ 10000) / (10 ^ 10000)`, of value
`1`, is refused at its numerator, and `(10 ^ 10000) ^ 0` before its outer power is taken. As in
`Rat.mul`, a product first cancels `gcd (num a) (den b)` and `gcd (num b) (den a)`, so its numerator
and denominator in lowest terms are two products, each compared before it is formed, and a power of
a fraction in lowest terms is in lowest terms. A sum is formed over the least common denominator, as
in `Rat.add`, and is refused when one of its two cross products, their sum or that denominator has
more than `10000` digits, without forming that number, so a sum may be refused although its value in
lowest terms is below the bound. The values of the polynomial families at a rational point use the
same arithmetic (`polyEvalBelow?`). The handlers of `factorial`, `fibonacci`, `binomial` and
`divisorSigma` build their values with `mulBelow?`, `addBelow?` and `powBelow?`.

Between the arguments and the value, the handlers form no other number past the bound: the
ranges of `gamma` (`Gamma.inRange`), `zeta` and `BernoulliB` are compared without forming a
larger number, and the residues and Bézout coefficients of `modularInverse` are at most its
modulus. The proofs of three calls form larger numbers, bounded in the module notes of
`CAS.Command.NumberTheory.Functions` and `CAS.Command.NumberTheory.Modular`: that of `binomial`
the descending factorial `n (n - 1) ⋯ (n - j + 1)`, with at most `72902` digits, and those of
`powerMod` and `modularInverse` products of two numbers below the modulus or the base, with at
most `20000` digits.

No refusal of `evalInteger`, `natArgument` or `SpecialFunctions.parseRational` prints a number
that they computed. The refusals of `evalInteger` quote the subterm at fault as written and say
why, and for a subterm that is a call of the function table they say instead which commands
evaluate that call; `parseRational` quotes an argument that it refuses for its size, and the
decimal literal whose mantissa it refuses.
-/

public meta section

namespace CAS.Command.Arguments

open Lean Elab Command

/-- The largest number of decimal digits of an argument or a value that a call computes. -/
def maxResultDigits : Nat := 10000

/-- `10 ^ maxResultDigits`, the least number with more than `maxResultDigits` digits. -/
def resultLimit : Nat := 10 ^ maxResultDigits

/-- `a * b` when it is below `resultLimit`, and `none` otherwise. For `b ≠ 0` the comparison
`a ≤ (resultLimit - 1) / b` decides this before the product is formed. -/
def mulBelow? (a b : Nat) : Option Nat :=
  if b = 0 then some 0 else if a ≤ (resultLimit - 1) / b then some (a * b) else none

/-- `a + b` when it is below `resultLimit`, and `none` otherwise, decided by
`a < resultLimit - b` before the sum is formed. -/
def addBelow? (a b : Nat) : Option Nat :=
  if a < resultLimit - b then some (a + b) else none

/-- `x + y` when its absolute value is below `resultLimit`, and `none` otherwise. A sum of two
numbers of the same sign is compared by `addBelow?` before it is formed; a sum of two numbers of
opposite signs is no larger than its operands. -/
def intAddBelow? (x y : Int) : Option Int :=
  if x < 0 ↔ y < 0 then
    (addBelow? x.natAbs y.natAbs).map fun s ↦ if x < 0 then -(s : Int) else (s : Int)
  else
    let s := x + y
    if s.natAbs < resultLimit then some s else none

/-- `x * y` when its absolute value is below `resultLimit`, and `none` otherwise, by
`mulBelow?`. -/
def intMulBelow? (x y : Int) : Option Int :=
  (mulBelow? x.natAbs y.natAbs).map fun p ↦ x.sign * y.sign * p

/-- `a ^ e` when it is below `resultLimit`, and `none` otherwise, by squaring over the bits of `e`
from the most significant one. Every partial power is at most `a ^ e`, so the first one at or
above the limit shows that `a ^ e` is too. -/
def powBelow? (a e : Nat) : Option Nat :=
  if a ≤ 1 then some (if e = 0 then 1 else a)
  else (List.range (Nat.log2 e + 1)).reverse.foldlM (init := 1) fun acc i ↦ do
    let square ← mulBelow? acc acc
    if e.testBit i then mulBelow? square a else pure square

/-- `q` when its numerator and its denominator are below `resultLimit`, and `none` otherwise. -/
def ratBelow? (q : ℚ) : Option ℚ :=
  if q.num.natAbs < resultLimit ∧ q.den < resultLimit then some q else none

/-- `a * b` when the numerator and the denominator of `a * b` are below `resultLimit`, and `none`
otherwise. As in `Rat.mul`, we cancel `gcd (num a) (den b)` and `gcd (num b) (den a)` first, so
that the numerator and the denominator in lowest terms are products that `mulBelow?` compares
before they are formed. -/
def ratMulBelow? (a b : ℚ) : Option ℚ := do
  let g₁ := a.num.natAbs.gcd b.den
  let g₂ := b.num.natAbs.gcd a.den
  let num ← mulBelow? (a.num.natAbs / g₁) (b.num.natAbs / g₂)
  let den ← mulBelow? (a.den / g₂) (b.den / g₁)
  return mkRat (a.num.sign * b.num.sign * num) den

/-- `a + b`, over the least common denominator `l` of `a` and `b` as in `Rat.add`, when the two
cross products, their sum and `l` are below `resultLimit`, and `none` otherwise. Each of them is
formed only if it is below the limit; the sum in lowest terms may be below it when this refuses. -/
def ratAddBelow? (a b : ℚ) : Option ℚ := do
  let g := a.den.gcd b.den
  let a' := a.den / g
  let b' := b.den / g
  let x ← intMulBelow? a.num b'
  let y ← intMulBelow? b.num a'
  let num ← intAddBelow? x y
  let den ← mulBelow? a' b.den
  return mkRat num den

/-- `a ^ e` when its numerator and its denominator, the powers of those of `a`, are below
`resultLimit`, and `none` otherwise, by `powBelow?`. -/
def ratPowBelow? (a : ℚ) (e : Nat) : Option ℚ := do
  let num ← powBelow? a.num.natAbs e
  let den ← powBelow? a.den e
  let sign : Int := if a.num < 0 ∧ e % 2 = 1 then -1 else 1
  return mkRat (sign * num) den

/-- `∑ⱼ cⱼ q ^ j` for `coefficients = [c₀, c₁, …]`, each term formed by `ratPowBelow?` and
`ratMulBelow?` and added to the sum of the earlier terms by `ratAddBelow?`, when none of these
steps refuses, and `none` otherwise. The terms with `cⱼ = 0` are skipped. -/
def polyEvalBelow? (coefficients : List ℚ) (q : ℚ) : Option ℚ :=
  coefficients.zipIdx.foldlM (init := 0) fun total (c, j) ↦
    if c = 0 then some total
    else do ratAddBelow? total (← ratMulBelow? c (← ratPowBelow? q j))

/-- Why a decimal literal is refused before its value is formed. -/
inductive DecimalRefusal where
  /-- The mantissa, the number that the digits of the literal form without the point, has more
  than `maxResultDigits` digits. -/
  | mantissa
  /-- The value, with a positive power of ten, has more than `maxResultDigits` digits. -/
  | value
  deriving DecidableEq, Repr

/-- The refusal of the decimal literal `m × 10 ^ e`, or `m × 10 ^ (-e)` when `negative`, as
`Lean.Syntax.isScientificLit?` decodes it: `mantissa` when `m ≥ resultLimit`, and `value` when
the power is positive and `d + e > maxResultDigits` for the number `d ≥ 1` of digits of `m ≠ 0`.
Since `10 ^ (d - 1) ≤ m < 10 ^ d`, the second holds exactly when `m * 10 ^ e ≥ resultLimit`.
Neither `m * 10 ^ e` nor `10 ^ e` is formed. With a negative power the value is at most `m`; the
callers form `10 ^ e` only for `e` below `d` (`scientificValue`) or up to `1000` (the parser). -/
def decimalRefusal? (m : Nat) (negative : Bool) (e : Nat) : Option DecimalRefusal :=
  if m ≥ resultLimit then some .mantissa
  else if !negative && m ≠ 0 && (toString m).length + e > maxResultDigits then some .value
  else none

/-- The first decimal literal of `stx`, with its refusal, that `decimalRefusal?` refuses. -/
partial def oversizedDecimal? (stx : Syntax) : Option (Syntax × DecimalRefusal) :=
  match stx.isScientificLit? with
  | some (m, negative, e) => (decimalRefusal? m negative e).map (stx, ·)
  | none => stx.getArgs.findSome? oversizedDecimal?

/-- Why a closed expression has no rational value within the size guard. -/
inductive RationalRefusal where
  /-- The expression is not built from rational numbers by `+`, `-`, `*`, `/` and natural powers,
  or it divides by zero. -/
  | notRational
  /-- The numerator or the denominator of a literal, or of a number that the evaluation would
  form, reaches `resultLimit`. -/
  | tooLarge

/-- Whether `e` is built from numerals and rational literals by `+`, `-`, `*`, `/`, negation and
natural powers. -/
def rationalShape : Verified.Expr (Fin 0) → Bool
  | .nat _ | .int _ | .rat _ _ => true
  | .add a b | .sub a b | .mul a b | .div a b => rationalShape a && rationalShape b
  | .neg a | .pow a _ => rationalShape a
  | _ => false

/-- `q` for `some q`, and the refusal `tooLarge` for `none`. -/
def orTooLarge : Option ℚ → Except RationalRefusal ℚ
  | some q => .ok q
  | none => .error .tooLarge

/-- The value of `e` with the arithmetic of `CAS.Verified.Expr.evalRat?`, by `ratBelow?` on the
literals and `ratAddBelow?`, `ratMulBelow?` and `ratPowBelow?` on the operations: `tooLarge` when
one of them refuses, and `notRational` for a division by zero and for any other constructor. -/
def evalRational : Verified.Expr (Fin 0) → Except RationalRefusal ℚ
  | .nat n => orTooLarge (ratBelow? n)
  | .int n => orTooLarge (ratBelow? n)
  | .rat num den =>
      if den = 0 then Except.error .notRational else orTooLarge (ratBelow? (mkRat num den))
  | .add a b => do orTooLarge (ratAddBelow? (← evalRational a) (← evalRational b))
  | .sub a b => do orTooLarge (ratAddBelow? (← evalRational a) (-(← evalRational b)))
  | .mul a b => do orTooLarge (ratMulBelow? (← evalRational a) (← evalRational b))
  | .div a b => do
      let x ← evalRational a
      let y ← evalRational b
      if y = 0 then Except.error .notRational else orTooLarge (ratMulBelow? x y⁻¹)
  | .neg a => do return -(← evalRational a)
  | .pow a n => do orTooLarge (ratPowBelow? (← evalRational a) n)
  | _ => Except.error .notRational

/-- The rational value of the closed expression `t`, the value of `CAS.Verified.Expr.evalRat?`,
when `evalRational` accepts it. An expression that is not built from rational numbers by `+`,
`-`, `*`, `/` and natural powers is refused as `notRational` before it is evaluated. -/
def rationalValue (t : Verified.Expr (Fin 0)) : Except RationalRefusal ℚ :=
  if rationalShape t then evalRational t else Except.error .notRational

/-- `stx` without the parentheses around it. -/
partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(($a)) => stripParens a
  | _ => stx

/-- The text of `stx` as written, without the parentheses around it. -/
def argumentText (stx : Syntax) : String :=
  surfaceText (stripParens ⟨stx⟩)

/-- The variable that the argument `stx` names, up to parentheses: an identifier without dots
other than the constants `pi`, `π`, `Pi`, `e` and `E` of the calculator. -/
def variableName? (stx : Term) : Option Name :=
  match stripParens stx with
  | `($x:ident) =>
      let name := x.getId
      let constants : List Name := [`pi, `π, `Pi, `e, `E]
      if name.isAtomic && !constants.contains name then some name else none
  | _ => none

/-- Refuse the argument `stx` of `function`, for `reason`. -/
def refuseArgument {α : Type} (function : String) (stx : Term) (reason : String) :
    CommandElabM α :=
  throwErrorAt stx "{function} takes integer arguments; `{argumentText stx}` {reason}"

/-- Refuse the subterm `stx` of an argument of `function`, whose value has more than
`maxResultDigits` digits. -/
def refuseSize {α : Type} (function : String) (stx : Term) : CommandElabM α :=
  throwErrorAt stx "{function}: `{argumentText stx}` has more than {maxResultDigits} digits, the \
    most that a call computes"

/-- Refuse the decimal literal `stx` in an argument of `function`, whose mantissa, the number that
its digits form without the point, has more than `maxResultDigits` digits. -/
def refuseMantissa {α : Type} (function : String) (stx : Syntax) : CommandElabM α :=
  throwErrorAt stx "{function}: the mantissa of `{argumentText stx}`, the number that its digits \
    form without the point, has more than {maxResultDigits} digits, the most that a call reads"

/-- Refuse, at `stx`, a value of `function` with more than `maxResultDigits` digits. -/
def refuseValueSize {α : Type} (function : String) (stx : Syntax) : CommandElabM α :=
  throwErrorAt stx "{function}: the value has more than {maxResultDigits} digits, the most that \
    a call computes"

/-- Refuse, at the call `input` of `function`, an evaluation that needs a number with more than
`maxResultDigits` digits. -/
def refuseEvaluationSize {α : Type} (function : String) (input : Syntax) : CommandElabM α :=
  throwErrorAt input "{function}: evaluating `{argumentText input}` needs a number with more than \
    {maxResultDigits} digits, the most that a call computes"

/-- `v`, after refusing it as the value of the subterm `stx` of an argument of `function` when
it has more than `maxResultDigits` digits. -/
def checkBelow (function : String) (stx : Term) (v : Int) : CommandElabM Int := do
  unless v.natAbs < resultLimit do refuseSize function stx
  return v

/-- The arithmetic in which a subterm of an argument is evaluated. -/
inductive Arithmetic where
  /-- The calculator's arithmetic of real numbers, outside every ascription: the value is an
  integer, `a / b` divides exactly, `a % b` is the remainder of `ℤ` for `b ≠ 0`, and the exponent
  of a power is not negative. -/
  | calculator
  /-- Lean's arithmetic of `ℤ`, inside `(a : ℤ)`: `a / b` and `a % b` are `Int.ediv` and
  `Int.emod`, with `a / 0 = 0` and `a % 0 = a`, and an exponent is a natural number. -/
  | int
  /-- Lean's arithmetic of `ℕ`, inside `(a : ℕ)`: `a - b = 0` for `a ≤ b`, `a / b` rounds down,
  `a / 0 = 0`, `a % 0 = a`, and there are no negations and no decimals. -/
  | nat

/-- The arithmetic of the ascription `(a : type)`: `ℕ` and `Nat`, or `ℤ` and `Int`. -/
def ascription? (type : Term) : Option Arithmetic :=
  match surfaceText type with
  | "ℕ" | "Nat" => some .nat
  | "ℤ" | "Int" => some .int
  | _ => none

/-- The integer value of the decimal literal `s`, a subterm of an argument of `function`, once
`decimalRefusal?` has accepted it: a mantissa with more than `maxResultDigits` digits is refused
by `refuseMantissa`, and a value with more by `refuseSize`. -/
def scientificValue (function : String) (stx : Term) (s : TSyntax `scientific) :
    CommandElabM Int := do
  let (m, negative, e) := s.getScientific
  match decimalRefusal? m negative e with
  | some .mantissa => refuseMantissa function stx
  | some .value => refuseSize function stx
  | none => pure ()
  if m = 0 then return 0
  let digits := (toString m).length
  if negative then
    -- `0 < m / 10 ^ e < 1` when `m` has at most `e` digits, and `10 ^ e ≤ m` otherwise.
    if e ≥ digits || m % 10 ^ e ≠ 0 then refuseArgument function stx "is not an integer"
    return Int.ofNat (m / 10 ^ e)
  -- `m * 10 ^ e < 10 ^ (digits + e) ≤ resultLimit`, as `decimalRefusal?` accepted it.
  return Int.ofNat (m * 10 ^ e)

/-- The integer that the subterm `stx` of an argument of `function` denotes in the arithmetic
`ctx`, as `evalInteger` describes. -/
partial def evalIn (function : String) (ctx : Arithmetic) (stx : Term) : CommandElabM Int := do
  match stx with
  | `($n:num) => checkBelow function stx n.getNat
  | `($s:scientific) =>
      match ctx with
      | .calculator => scientificValue function stx s
      | .int => refuseArgument function stx "is a decimal, and `ℤ` has no decimals"
      | .nat => refuseArgument function stx "is a decimal, and `ℕ` has no decimals"
  | `(($a)) => evalIn function ctx a
  | `(($a : $type)) =>
      match ascription? type, ctx with
      | none, _ =>
          refuseArgument function stx s!"has the type `{surfaceText type}`, and the ascriptions \
            of an integer argument are `ℕ` and `ℤ`"
      | some .int, .nat =>
          refuseArgument function stx "has the type `ℤ` inside a natural number, and Lean has no \
            coercion from `ℤ` to `ℕ`"
      | some inner, _ => evalIn function inner a
  | `(-$a) =>
      if ctx matches .nat then
        refuseArgument function stx "negates a natural number, and `ℕ` has no negation"
      return -(← evalIn function ctx a)
  | `($a + $b) =>
      let x ← evalIn function ctx a
      let y ← evalIn function ctx b
      let some s := intAddBelow? x y | refuseSize function stx
      return s
  | `($a - $b) =>
      let x ← evalIn function ctx a
      let y ← evalIn function ctx b
      -- Subtraction on `ℕ` truncates at `0`, as in Lean.
      if ctx matches .nat then return max (x - y) 0
      let some s := intAddBelow? x (-y) | refuseSize function stx
      return s
  | `($a * $b) =>
      let x ← evalIn function ctx a
      let y ← evalIn function ctx b
      let some p := intMulBelow? x y | refuseSize function stx
      return p
  | `($a / $b) =>
      let x ← evalIn function ctx a
      let y ← evalIn function ctx b
      if ctx matches .calculator then
        if y = 0 then refuseArgument function stx "divides by zero"
        if x % y ≠ 0 then refuseArgument function stx "is not an integer"
      -- The division of `ℤ`, which on natural operands is the division of `ℕ`.
      return x / y
  | `($a % $b) =>
      let x ← evalIn function ctx a
      let y ← evalIn function ctx b
      if ctx matches .calculator then
        if y = 0 then refuseArgument function stx "divides by zero"
      return x % y
  | `($a ^ $k) =>
      let x ← evalIn function ctx a
      -- In Lean the exponent of a power in `ℤ` or `ℕ` is a natural number.
      let e ← evalIn function (if ctx matches .calculator then .calculator else .nat) k
      if e < 0 then refuseArgument function stx "has a negative exponent"
      let some p := powBelow? x.natAbs e.toNat | refuseSize function stx
      return if x < 0 && e % 2 = 1 then -(p : Int) else p
  | `($f:ident $_args*) =>
      match FunctionTable.callHint? f.getId.toString with
      | some hint => throwErrorAt stx "{function} takes integer arguments; {hint}"
      | none => refuseArgument function stx "is not an integer expression"
  | `($_:ident) => refuseArgument function stx "is a variable"
  | _ => refuseArgument function stx "is not an integer expression"

/-- The integer that the argument `stx` of `function` denotes. Outside an ascription it is read
as a real number and has to be an integer: numerals, decimals with an integer value, `-a`,
`a + b`, `a - b`, `a * b`, `a / b` when `b` divides `a`, `a % b` for `b ≠ 0`, `a ^ k` with
`k ≥ 0`, and parentheses. Inside `(a : ℕ)` and `(a : ℤ)` the subterm `a` is evaluated with
Lean's arithmetic of that type (`Arithmetic`), and other ascriptions are refused. A subterm with
more than `maxResultDigits` digits is refused, and so is anything else, with the subterm and the
reason; a call of the function table is refused with the commands that evaluate it. -/
def evalInteger (function : String) (stx : Term) : CommandElabM Int :=
  evalIn function .calculator stx

/-- The natural number that the argument `stx` of `function` denotes, by `evalInteger`; `what`
names the argument in the refusal of a negative value, as in `its first argument`. -/
def natArgument (function what : String) (stx : Term) : CommandElabM Nat := do
  let v ← evalInteger function stx
  if v < 0 then
    throwErrorAt stx "{function} takes a natural number as {what}; `{argumentText stx}` is \
      negative"
  return v.toNat

end CAS.Command.Arguments
