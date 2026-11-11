+++
id = "gamma"
kind = "call"
title = "gamma"
summary = "The exact value of the Gamma function at an integer or a half-integer, with a theorem about Mathlib’s `Real.Gamma`."
calls = ["gamma"]
see_also = ["factorial", "binomial", "zeta", "BernoulliB", "cas"]
guide = "special-functions"
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas (gamma ‹q›)`
: gives the exact value of $\Gamma(q)$ at an integer or a half-integer ‹q› and proves `Real.Gamma ‹q› = ‹v›`.
:::

`gamma` computes the exact special values of $\Gamma$, the ones you would look up in a table. At a positive integer the value is a factorial, and at a half-integer it is a rational multiple of $\sqrt{\pi}$. Each answer comes with a theorem about Mathlib’s `Real.Gamma`, so it means exactly what Mathlib means, down to Mathlib’s value 0 at the poles.

## Details and Options

- ‹q› is a closed rational expression whose value is an integer or a half-integer with $|q| \le \tfrac{1001}{2}$, such as `5`, `(5/2)` or `(-3/2)`. Other rationals, irrational numbers and symbols are refused.
- At a positive integer the theorem is `Real.Gamma q = v` with $v = (q - 1)!$. At a half-integer it is `Real.Gamma q = a * √Real.pi / b` with integers $a$ and $b$.
- The proof is one rewrite with a closed formula and a `norm_num` step. The formulas are `Real.Gamma_nat_eq_factorial`, $\Gamma(n + 1) = n!$, Mathlib’s `Real.Gamma_nat_add_half`, $\Gamma(k + \tfrac{1}{2}) = (2k - 1)!!\,\sqrt{\pi}/2^k$, and `CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat`, $\Gamma(\tfrac{1}{2} - k) = (-2)^k \sqrt{\pi}/(2k - 1)!!$.
- At an integer $q \le 0$, a pole of $\Gamma$, the theorem is `Real.Gamma q = 0`, Mathlib’s value there (`Real.Gamma_neg_nat_eq_zero`), and the Output line says so.
- The call is evaluated when it is the whole input of `#cas`.
- The tactic [[cas]] proves `Real.Gamma q = v` with the same closed formulas.
- There are no options.

## Examples

### Basic Examples

At a half-integer the value is a rational multiple of $\sqrt{\pi}$:

```lean
#cas (gamma (5/2))
```

---

At a positive integer it is a factorial, $\Gamma(5) = 4!$:

```lean
#cas (gamma 5)
```

### Scope

At a negative half-integer the formula is $\Gamma(\tfrac{1}{2} - k) = (-2)^k \sqrt{\pi}/(2k - 1)!!$, here with $k = 2$:

```lean
#cas (gamma (-3/2))
```

---

The value at $\tfrac{1}{2}$ is $\sqrt{\pi}$:

```lean
#cas (gamma (1/2))
```

---

At a pole the report gives Mathlib’s value 0 and says that the point is a pole:

```lean
#cas (gamma (-3))
```

### Applications

The tactic [[cas]] proves the same values inside a proof:

```lean
theorem gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * √Real.pi := by
  cas

#print axioms gamma_seven_halves
```

### Properties and Relations

The recurrence $\Gamma(q + 1) = q\,\Gamma(q)$ takes $\Gamma(\tfrac{5}{2}) = \tfrac{3}{4}\sqrt{\pi}$ to $\tfrac{5}{2} \cdot \tfrac{3}{4}\sqrt{\pi} = \tfrac{15}{8}\sqrt{\pi}$:

```lean
#cas (gamma (7/2))
```

### Possible Issues

The call computes exact values at integers and half-integers only, and $\tfrac{1}{3}$ is neither:

```lean error
#cas (gamma (1/3))
```

---

The argument is a number, not a symbol:

```lean error
#cas (gamma x)
```

---

The call is evaluated as the whole input, not inside a larger expression:

```lean error
#cas (2 * gamma (5/2))
```

---

The argument lies within $|q| \le \tfrac{1001}{2}$:

```lean error
#cas (gamma (1003/2))
```
