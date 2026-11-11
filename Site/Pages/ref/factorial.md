+++
id = "factorial"
kind = "call"
title = "factorial"
summary = "The factorial $n!$ of a natural number, with a theorem about Mathlib’s `Nat.factorial`."
calls = ["factorial"]
see_also = ["binomial", "gamma", "fibonacci", "cas"]
guide = "number-theory"
tutorials = ["proving", "trust"]
+++

::: usage
`#cas (factorial ‹n›)`
: gives the factorial $n! = 1 \cdot 2 \cdots n$ of the natural number ‹n› and proves `Nat.factorial ‹n› = ‹f›`.
:::

`factorial` computes $n!$ and proves the value of Mathlib’s `Nat.factorial`. It’s a small mode, but the number you see is the number Mathlib means, so a proof can use it as it stands. When you need the factorial beyond the natural numbers, [[gamma]] extends it, with $\Gamma(n + 1) = n!$.

## Details and Options

- ‹n› is a natural number, a literal or a closed integer expression, and $0! = 1$.
- The theorem is `Nat.factorial n = f`. `norm_num` proves it with Mathlib’s extension for factorials (`Mathlib.Tactic.NormNum.NatFactorial`), which splits the product in halves, and `decide +kernel` is the fallback.
- An argument is evaluated with Lean’s arithmetic of its ascription, `ℕ` or `ℤ`. Other ascriptions are refused.
- The value has at most 10000 digits, the most that a call computes.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

Ten factorial, with the theorem that the kernel checked:

```lean
#cas (factorial 10)
```

### Scope

A value with 33 digits:

```lean
#cas (factorial 30)
```

---

The empty product, $0! = 1$:

```lean
#cas (factorial 0)
```

---

In `ℕ` the subtraction $1 - 2$ is truncated to 0, so the argument is 3:

```lean
#cas (factorial ((1 - 2 : ℕ) + 3))
```

---

In `ℤ` the subtraction gives $-1$, and the argument is 2:

```lean
#cas (factorial ((1 - 2 : ℤ) + 3))
```

### Applications

In a proof, [[cas]] proves the equation, here without any axioms:

```lean
theorem factorial_ten : Nat.factorial 10 = 3628800 := by
  cas

#print axioms factorial_ten
```

### Properties and Relations

$\Gamma(n + 1) = n!$, so [[gamma]] at 5 gives $4! = 24$:

```lean
#cas (gamma 5)
```

---

$\Gamma$ extends the factorial to the half-integers, with $\Gamma(\tfrac{7}{2}) = \tfrac{5}{2} \cdot \tfrac{3}{2} \cdot \tfrac{1}{2} \cdot \sqrt{\pi}$:

```lean
#cas (gamma (7/2))
```

### Possible Issues

`Nat.factorial` is defined on natural numbers, and a negative argument is refused:

```lean error
#cas (factorial (-1))
```

---

The ascriptions of an integer argument are `ℕ` and `ℤ`, and the ascription `ℝ` is refused even when the value is an integer:

```lean error
#cas (factorial (3 : ℝ))
```

---

The value has at most 10000 digits, and $5000!$ has 16326:

```lean error
#cas (factorial 5000)
```
