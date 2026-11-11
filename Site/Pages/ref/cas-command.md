+++
id = "cas-command"
kind = "command"
title = "#cas"
summary = "The calculator: evaluates a call, simplifies an expression or runs a mode, and proves its answer."
forms = ["CAS.Command.casBareCommand", "CAS.Command.UnknownMode.casUnknownModeCommand"]
see_also = ["simplify", "cas", "derive", "integrate", "N", "options"]
tutorials = ["first-hour"]
+++

::: usage
`#cas ‹e›`
: evaluates ‹e› when it is a call of a special or number-theoretic function, such as `gamma (5/2)`, and otherwise simplifies it as [[simplify|`#cas [simplify]`]] does.
`#cas [‹mode›] ‹e›`
: runs a mode on ‹e›, such as `derive x`, `factor` or `solve x`.
`#cas (‹options›) [‹mode›] ‹e›`
: the same, with the options of the mode, such as `(digits := 30)`.
:::

`#cas` is the calculator, and for me it is where most work with SymLean starts. You type an expression and get the answer, together with the theorem behind it, checked by Lean’s kernel. Nothing needs setting up beyond `import CAS`, and names like `x` and `t` are variables, as they would be on paper.

## Details and Options

- A report gives the output and its kind, the domain of the variables and the conditions under which the output holds, such as $x^2 - 1 \ne 0$.
- The details of a report, in the InfoView, hold the computation and the checked steps. Each step is a proposition, the theorem that proves it, and the check that it passed.
- `#cas ‹e›` evaluates ‹e› when it is a call of [[ChebyshevT]], [[ChebyshevU]], [[HermiteH]], [[HermiteHe]], [[LegendreP]], [[BernoulliB]], [[zeta]], [[gamma]], [[eulerPhi]], [[divisorSigma]], [[binomial]], [[factorial]], [[fibonacci]], [[powerMod]], [[modularInverse]] or [[jacobiSymbol]], and of [[primeQ]] and [[moebiusMu]] with `import CASHex.NumberTheory`. [[erf]] and [[BesselJ]] have digits only, by [[N|`#cas [N d]`]].
- The call is the whole input, up to parentheses. In `#cas (2 * gamma (5/2))` nothing is evaluated.
- Integer arguments are closed integer expressions such as `2 ^ 10 - 1`, and rational arguments closed rational expressions such as `5/2`. A call is refused when an argument or its value needs a number with more than 10000 digits.
- For any other input, the theorem is that of `#cas [simplify] e`: $\forall x_1, \ldots, x_n,\ c_1 \to \cdots \to c_k \to e = e'$, with the conditions $c_i$ of the report.
- A bracket right after `#cas` always opens a mode. A word that is no mode is refused, and the message names the nearest modes, or the commands for a function of the table.
- The modes are listed by area in the guides: [[algebra|Algebra]], [[polynomials|Polynomials]], [[calculus|Calculus]], [[series-limits|Series and Limits]], [[equations|Equations]], [[sums|Sums and Recurrences]], [[number-theory|Number Theory]], [[linear-algebra|Linear Algebra]], [[differential-equations|Differential Equations]] and [[numerics|Numerics]].
- `#cas ‹e›` has no options. The settings that shape a report are on [[options|Options]].

## Examples

### Basic Examples

A call is evaluated exactly:

```lean
#cas (gamma (5/2))
```

---

```lean
#cas (binomial 10 3)
```

---

Any other input is simplified, with the conditions that the answer needs:

```lean
#cas ((x ^ 4 - 1) / (x ^ 2 - 1))
```

### Scope

A family of polynomials takes the degree and the variable:

```lean
#cas (ChebyshevT 5 x)
```

---

An exact value of the zeta function:

```lean
#cas (zeta 4)
```

---

Arguments of any size, and closed expressions as arguments:

```lean
#cas (powerMod 2 123456789123456789123456789 1000000007)
```

```lean
#cas (eulerPhi (2 ^ 10))
```

---

A mode in brackets. Here an antiderivative, which needs the error function:

```lean
#cas [integrate x] (exp (-x ^ 2))
```

### Options

`#cas ‹e›` has no options, and a mode takes its own in parentheses before the bracket:

```lean
#cas (digits := 30) [findRoot x in [1, 2]] (x^2 - 2)
```

---

With [[options|`cas.suggest`]], the report also offers its theorem as an `example` to paste:

```lean
set_option cas.suggest true in
#cas ((x ^ 4 - 1) / (x ^ 2 - 1))
```

### Applications

The report of `#cas (gamma (5/2))` states $\Gamma(5/2) = \tfrac{3}{4}\sqrt{\pi}$, and [[cas]] proves the statement. Only the three standard axioms are used:

```lean
theorem gamma_five_halves : Real.Gamma (5 / 2) = 3 * √Real.pi / 4 := by
  cas

#print axioms gamma_five_halves
```

---

The quotient from Basic Examples, as a theorem with its condition:

```lean
theorem simplify_quotient (x : ℝ) (h : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas
```

### Properties and Relations

`#cas ‹e›` is [[simplify|`#cas [simplify] ‹e›`]] when ‹e› is not a call:

```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```

---

A function with digits only is evaluated by [[N|`#cas [N d]`]]:

```lean
#cas [N 30] (erf 1)
```

### Possible Issues

The call must be the whole input:

```lean error
#cas (2 * gamma (5/2))
```

---

A family of polynomials needs the variable too:

```lean error
#cas (ChebyshevT 5)
```

---

The error function has no exact values, only digits:

```lean error
#cas (erf 1)
```

---

Mode words are case sensitive:

```lean error
#cas [Simplify] (x + x)
```

---

A function in the bracket gets the commands that evaluate it:

```lean error
#cas [LegendreP 5]
```

---

A value with more than 10000 digits is refused:

```lean error
#cas (factorial 5000)
```

### Neat Examples

The hundredth Fibonacci number, with the theorem that proves it:

```lean
#cas (fibonacci 100)
```
