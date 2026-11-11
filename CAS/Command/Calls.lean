/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.BesselJ
public import CAS.Command.Erf
public import CAS.Command.FullSimplify
public import CAS.Command.Gamma
public import CAS.Command.NumberTheory.Functions
public import CAS.Command.NumberTheory.Jacobi
public import CAS.Command.OrthogonalPolynomials
public import CAS.Command.Simplification
public meta import Lean.Elab.Command
public meta import CAS.Command.FunctionTable

/-!
# Calls of special and number-theoretic functions: `#cas e`

`#cas (gamma (5/2))`, `#cas (ChebyshevT 5 x)` and `#cas (powerMod 2 100 7)` evaluate a function
of `CAS.Command.FunctionTable` written as an ordinary call, when the call is the whole input, and
print the theorem about Mathlib's function at the evaluated arguments. Every other input of
`#cas e` is simplified, as by `#cas [simplify] e`. `#cas [expand] (f n x)` prints the polynomial
of a family, and `#cas [N d] (f a …)` gives the digits of the functions with a numeric form.

## Main definitions

* `CAS.Command.Calls.notModeBracket`: the parser that keeps `#cas e` off the mode brackets.
* `CAS.Command.Calls.call?`: the name and the arguments of a call of the table.
* `CAS.Command.Calls.logCall`: the report of a call, by the handler of its function.
* `CAS.Command.Calls.logNumericCall`: the report of `#cas [N d]` on a call.
* `CAS.Command.casBareCommand`: the form `#cas e`.

## Implementation notes

`notModeBracket` fails where `[` follows `#cas`, and an option such as `(digits := 4)` is no
term, so the modes, with or without options as in
`#cas (digits := 4) [maximize x in [0, 1]] (x - x^3)`, keep their own parses and errors. The
three forms recognize a call in one way, by `call?`: the head is the unqualified name of an
entry, as the calculator writes it, and the arguments are positional. We read the name as written
and do not resolve it, so a Lean declaration of the same name changes nothing. A variable of the
section with that name is refused wherever it is applied: in a term the name would mean the
variable, and evaluating the function instead would ignore it. The integer arguments are
evaluated first, by `CAS.Command.Arguments`, so the theorem of a call states numerals. Every
function of the table has pinned examples in `CAS/Examples/Reference`, so a function without a
handler here fails the build.
-/

public meta section

namespace CAS.Command.Calls

open Lean Parser PrettyPrinter

/-- Succeed without reading input, with an empty node, unless `[` follows: `#cas e` never reads a
mode bracket. -/
def notModeBracket : Parser :=
  notFollowedBy (symbol "[") "mode bracket" >> pushNone

/-- The formatter of `notModeBracket`, which reads no input: that of `pushNone`. -/
@[combinator_formatter notModeBracket]
def notModeBracket.formatter : Formatter := Formatter.pushNone.formatter

/-- The parenthesizer of `notModeBracket`, which reads no input: that of `pushNone`. -/
@[combinator_parenthesizer notModeBracket]
def notModeBracket.parenthesizer : Parenthesizer := Parenthesizer.pushNone.parenthesizer

end CAS.Command.Calls

namespace CAS.Command.Calls

open Lean Elab Command

/-- Whether `name` is a variable of the current section, which hides a function of the table. -/
def isSectionVariable (name : Name) : CommandElabM Bool := do
  if (← getScope).varDecls.isEmpty then return false
  runTermElabM fun _ ↦ do return (← getLCtx).usesUserName name

/-- The heads of the applications in `stx` that are names of functions of the table. -/
partial def tableHeads (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.foldl (fun heads a ↦ heads ++ tableHeads a) #[]
  if stx.isOfKind ``Lean.Parser.Term.app && stx[0].isIdent &&
      FunctionTable.callableFunctions.any (·.name == stx[0].getId.toString) then
    inner.push stx[0]
  else inner

/-- Refuse `stx` when it applies a variable of the section that has the name of a function of
the table. -/
def checkShadowing (stx : Syntax) : CommandElabM Unit := do
  if (← getScope).varDecls.isEmpty then return
  for head in tableHeads stx do
    if ← isSectionVariable head.getId then
      throwErrorAt head "`{head.getId}` is a variable of the section, which hides the function \
        `{head.getId}` of `#cas`; rename the variable to evaluate the function"

/-- The name and the arguments of `c` when `c` applies a function of the table, by its
unqualified name, to arguments without names. An application of a variable of the section with
the name of a function, anywhere in `c`, is refused. -/
def call? (c : Term) : CommandElabM (Option (String × Array Term)) := do
  checkShadowing c
  unless c.raw.isOfKind ``Lean.Parser.Term.app && c.raw[0].isIdent do return none
  let name := c.raw[0].getId.toString
  unless FunctionTable.callableFunctions.any (·.name == name) do return none
  let args := c.raw[1].getArgs
  if args.any fun a ↦ a.isOfKind ``Lean.Parser.Term.namedArgument ||
      a.isOfKind ``Lean.Parser.Term.ellipsis then
    return none
  return some (name, args.map fun a ↦ (⟨a⟩ : Term))

/-- The refusal of a call of `name` with `count` arguments, a number that no entry takes. -/
def arityMessage (name : String) (count : Nat) : String :=
  let entries := (FunctionTable.callableFunctions.filter (·.name == name)).mergeSort
    fun a b ↦ decide (a.arity ≤ b.arity)
  let arities := FunctionTable.orList (entries.map fun f ↦ toString f.arity)
  let usages := FunctionTable.orList (entries.map fun f ↦ s!"`{f.usage}`")
  let noun := if entries.all (·.arity == 1) then "argument" else "arguments"
  s!"{name} takes {arities} {noun}, as in {usages}; the call has {count}"

/-- The refusal of `#cas (f a)` for a function `f` whose values have digits only. -/
def numericMessage (f : CallableFunction) : String :=
  s!"`#cas` computes no exact value of `{f.usage}`; `#cas [N d] ({f.usage})` gives its digits"

/-- The family of polynomials of the name `name`, for the families other than `LegendreP`. -/
def family? : String → Option OrthogonalPolynomials.Family
  | "ChebyshevT" => some .chebyshevT
  | "ChebyshevU" => some .chebyshevU
  | "HermiteH" => some .hermiteH
  | "HermiteHe" => some .hermiteHe
  | "BernoulliB" => some .bernoulli
  | _ => none

/-- Whether `stx` is a closed rational expression, as `SpecialFunctions.parseRational` reads
one, whether or not its evaluation stays within the size guard. -/
def isRational (stx : Syntax) : CommandElabM Bool := do
  try
    return !((← SpecialFunctions.rationalArgument "" stx) matches .error .notRational)
  catch _ =>
    return false

/-- Run the call `c`, `f n x` for a family of polynomials `f`: the polynomial in the variable
`x`, or its value at a rational number `x`. -/
def logPolynomialCall (f : CallableFunction) (degree argument c : Term) : CommandElabM Unit := do
  let n ← Arguments.natArgument f.name "the degree" degree
  match Arguments.variableName? argument, family? f.name with
  | some var, some family => OrthogonalPolynomials.logFamily c family n var
  | some var, none => SpecialFunctions.logLegendre c n var
  | none, family =>
      unless ← isRational argument do
        throwErrorAt argument "the second argument of `{f.usage}` is a variable, for the \
          polynomial, or a rational number, for its value"
      match family with
      | some family => OrthogonalPolynomials.logFamilyValue c none family n argument c
      | none => SpecialFunctions.logLegendreValue c none n argument c

/-- Run the call `c` of the entry `f` on its arguments `args`, by the handler of `f`. -/
def logCall (f : CallableFunction) (args : Array Term) (c : Term) : CommandElabM Unit := do
  let nat (what : String) (stx : Term) : CommandElabM Nat := Arguments.natArgument f.name what stx
  match f.name, args with
  | "ChebyshevT", #[n, x] | "ChebyshevU", #[n, x] | "HermiteH", #[n, x]
  | "HermiteHe", #[n, x] | "LegendreP", #[n, x] | "BernoulliB", #[n, x] =>
      logPolynomialCall f n x c
  | "BernoulliB", #[n] => Zeta.logBernoulli c n
  | "zeta", #[s] => Zeta.logZeta c s
  | "gamma", #[q] => Gamma.logGamma c q
  | "eulerPhi", #[n] => NumberTheory.logTotient c (← nat "its argument" n) n
  | "divisorSigma", #[k, n] =>
      NumberTheory.logDivisorSigma c (← nat "its first argument" k)
        (← nat "its second argument" n) n c
  | "binomial", #[n, k] =>
      NumberTheory.logBinomial c (← nat "its first argument" n) (← nat "its second argument" k) c
  | "factorial", #[n] => NumberTheory.logFactorial c (← nat "its argument" n) c
  | "fibonacci", #[n] => NumberTheory.logFibonacci c (← nat "its argument" n) c
  | "powerMod", #[a, b, m] =>
      NumberTheory.logPowerMod c (← nat "its first argument" a) (← nat "its second argument" b)
        (← nat "its third argument" m) c
  | "modularInverse", #[a, m] =>
      NumberTheory.logModularInverse c (← Arguments.evalInteger f.name a)
        (← nat "its second argument" m) c
  | "jacobiSymbol", #[a, n] =>
      NumberTheory.logJacobi c (← Arguments.evalInteger f.name a)
        (← nat "its second argument" n) c
  | "primeQ", #[n] => NumberTheory.runHexBackend `primeQ n
  | "moebiusMu", #[n] => NumberTheory.runHexBackend `moebiusMu n
  | _, _ => throwErrorAt c "{f.name}: internal error"

/-- Run `#cas [N d] c` for the call `c` of the entry `f` on its arguments `args`, by the handler
of `f`, with the digit count `d` written at `ref` and the input `input` as written. -/
def logNumericCall (f : CallableFunction) (args : Array Term) (ref : Syntax) (d : Nat)
    (input c : Term) : CommandElabM Unit := do
  match f.name, args with
  | "erf", #[q] => Erf.logErfValue ref d q input
  | "BesselJ", #[n, q] => BesselJ.logBesselValue ref d n q input
  | "ChebyshevT", #[degree, q] | "ChebyshevU", #[degree, q] | "HermiteH", #[degree, q]
  | "HermiteHe", #[degree, q] | "LegendreP", #[degree, q] | "BernoulliB", #[degree, q] =>
      let n ← Arguments.natArgument f.name "the degree" degree
      if (Arguments.variableName? q).isSome then
        throwErrorAt q "`[N d]` evaluates `{f.usage}` at a number; `#cas ({surfaceText c})` \
          gives the polynomial"
      match family? f.name with
      | some family => OrthogonalPolynomials.logFamilyValue ref (some d) family n q input
      | none => SpecialFunctions.logLegendreValue ref (some d) n q input
  | _, _ => throwErrorAt c "{f.name}: internal error"

end CAS.Command.Calls

namespace CAS.Command

open Lean Elab Command

/-- `#cas e` evaluates `e` when it is a call `f a₁ … aₖ` of a special or number-theoretic function
of the call table, such as `#cas (gamma (5/2))`, and otherwise simplifies `e` as
`#cas [simplify] e` does.

## Theorem
For a call, the report proves the value of Mathlib's function at the evaluated arguments, such
as `Real.Gamma (5 / 2) = 3 * √Real.pi / 4` for `gamma (5/2)` and `Nat.choose 10 3 = 120` for
`binomial 10 3`, or for a family of polynomials the expansion of Mathlib's polynomial; the
reference entry of each function states its theorem. For any other input it proves the theorem
of `#cas [simplify] e`, `∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → e = e'`.

## Conditions and limits
The call is the whole input, up to parentheses: in `#cas (2 * gamma (5/2))` the call is not
evaluated. The functions are `ChebyshevT`, `ChebyshevU`, `HermiteH`, `HermiteHe`, `LegendreP`,
`BernoulliB`, `zeta`, `gamma`, `eulerPhi`, `divisorSigma`, `binomial`, `factorial`, `fibonacci`,
`powerMod`, `modularInverse` and `jacobiSymbol`, and `primeQ` and `moebiusMu` with
`import CASHex.NumberTheory`. `erf` and `BesselJ` have digits only, by `#cas [N d]`. Integer
arguments are closed integer expressions such as `2 ^ 10 - 1` and rational arguments closed
rational expressions such as `5/2`. A call is refused when evaluating an argument needs a number
with more than `10000` digits, when its value has more digits than that and, for a polynomial at
a rational point, when evaluating the value needs such a number. A call is recognized by its
calculator spelling, the unqualified name of the table applied to positional arguments; a Lean
declaration of the same name does not change this, and a variable of the section with that name
is refused. A bracket right after `#cas` always opens a mode.

## Options
None.

## Examples
```lean
#cas (gamma (5/2))
```
```output
Output (exact value of Γ): 3√π/4
```
```lean
#cas (binomial 10 3)
```
```output
Output (binomial): 120
```
```lean
#cas ((x ^ 4 - 1) / (x ^ 2 - 1))
```
```output
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0
```

## In a proof
```lean
theorem gamma_five_halves : Real.Gamma (5 / 2) = 3 * √Real.pi / 4 := by
  cas
```

## See also
Mathematica evaluates `Gamma[5/2]` and `Binomial[10, 3]` as they are typed. The reference entries
of the functions of the table, and the modes `simplify` and `expand`.

## Possible issues
```lean
#cas (ChebyshevT 5)
```
```output
ChebyshevT takes 2 arguments, as in `ChebyshevT n x`; the call has 1
```
A family of polynomials takes the degree and the variable.
```lean
#cas (erf 1)
```
```output
`#cas` computes no exact value of `erf x`; `#cas [N d] (erf x)` gives its digits
```
-/
syntax (name := casBareCommand) (priority := low) "#cas" Calls.notModeBracket term : command

elab_rules : command
  | `(casBareCommand| #cas $e:term) => do
      let c := Arguments.stripParens e
      let some (name, args) ← Calls.call? c | logSimplify e (← parseInferred e)
      let some f := FunctionTable.find? name args.size
        | throwErrorAt c m!"{Calls.arityMessage name args.size}"
      unless f.forms.contains .bare do throwErrorAt c m!"{Calls.numericMessage f}"
      Calls.logCall f args c

/-- `#cas [expand] (f n x)` for a family of polynomials `f` prints the polynomial, as
`#cas (f n x)` does; every other input is left to the mode `expand`. -/
elab_rules : command
  | `(#cas [expand] $e:term) => do
      let c := Arguments.stripParens e
      let some (name, args) ← Calls.call? c | throwUnsupportedSyntax
      unless FunctionTable.callableFunctions.any
          (fun f ↦ f.name == name && f.forms.contains .expand) do
        throwUnsupportedSyntax
      let some f := FunctionTable.find? name args.size
        | throwErrorAt c m!"{Calls.arityMessage name args.size}"
      unless f.forms.contains .expand do throwUnsupportedSyntax
      Calls.logCall f args c

/-- `#cas [N d] (f a …)` for a function `f` of the table with a numeric form prints the digits of
the value, by the handler of `f`; every other input is left to the handler of `#cas [N d] e`. -/
elab_rules : command
  | `(#cas [N $digits:num] $e:term) => do
      let c := Arguments.stripParens e
      let some (name, args) ← Calls.call? c | throwUnsupportedSyntax
      unless FunctionTable.callableFunctions.any
          (fun f ↦ f.name == name && f.forms.contains .numeric) do
        throwUnsupportedSyntax
      let some f := FunctionTable.find? name args.size
        | throwErrorAt c m!"{Calls.arityMessage name args.size}"
      unless f.forms.contains .numeric do throwUnsupportedSyntax
      Calls.logNumericCall f args digits digits.getNat e c

end CAS.Command
