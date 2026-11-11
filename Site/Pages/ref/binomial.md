+++
id = "binomial"
kind = "call"
title = "binomial"
summary = "The binomial coefficient $\\binom{n}{k}$ of natural numbers $n$ and $k$, with a theorem about Mathlib’s `Nat.choose`."
calls = ["binomial"]
see_also = ["factorial", "gamma", "integerDigits", "cas"]
guide = "number-theory"
tutorials = ["proving", "trust"]
+++

::: usage
`#cas (binomial ‹n› ‹k›)`
: gives the binomial coefficient $\binom{n}{k}$ of the natural numbers ‹n› and ‹k› and proves `Nat.choose ‹n› ‹k› = ‹c›`.
:::

`binomial` computes a binomial coefficient $\binom{n}{k}$. It is a small thing, but the value comes with a theorem about Mathlib’s `Nat.choose`, so a proof can use the number the report prints instead of a number copied over by hand.

## Details and Options

- ‹n› and ‹k› are natural numbers, literals or closed integer expressions such as `2 ^ 10`. Negative and non-integer arguments are refused, since `Nat.choose` is defined on natural numbers.
- The theorem is `Nat.choose n k = c`. For $k \le n$ the proof rewrites with `Nat.choose_eq_descFactorial_div_factorial`, after `Nat.choose_symm` when $n - k < k$, and `norm_num` evaluates $n (n - 1) \cdots (n - j + 1) / j!$ for the smaller $j$ of $k$ and $n - k$.
- For $k > n$ the proof applies `Nat.choose_eq_zero_of_lt`, and the value is 0.
- The value has at most 10000 digits, the most that a call computes.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

The number of ways to choose 3 of 10 things, with the theorem that the kernel checked:

```lean
#cas (binomial 10 3)
```

### Scope

The largest coefficient for $n = 100$, with 30 digits:

```lean
#cas (binomial 100 50)
```

---

For $k > n$ the coefficient is 0:

```lean
#cas (binomial 3 10)
```

### Applications

In a proof, [[cas]] proves the equation, here without any axioms:

```lean
theorem choose_ten_three : Nat.choose 10 3 = 120 := by
  cas

#print axioms choose_ten_three
```

### Properties and Relations

$\binom{n}{k} = \tfrac{n!}{k!\,(n - k)!}$. With $10! = 3628800$ from [[factorial]], $\binom{10}{3} = \tfrac{3628800}{6 \cdot 5040} = 120$:

```lean
#cas (factorial 10)
```

### Possible Issues

Mathlib’s `Ring.choose` extends $\binom{n}{k}$ to negative $n$, and the call evaluates `Nat.choose`, so a negative argument is refused:

```lean error
#cas (binomial (-3) 2)
```

---

The arguments are numbers, not variables:

```lean error
#cas (binomial x 2)
```

---

The call takes two arguments:

```lean error
#cas (binomial 10)
```

---

The value has at most 10000 digits, and $\binom{100000}{50000}$ has 30101:

```lean error
#cas (binomial 100000 50000)
```
