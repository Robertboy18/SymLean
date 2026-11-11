+++
id = "sum"
kind = "mode"
title = "sum"
summary = "A finite sum in closed form or by its exact value, or the sum of a series, with a theorem."
forms = ["CAS.Command.casSumCommand", "CAS.Command.casInfiniteSumCommand"]
see_also = ["product", "rsolve", "zeta", "series", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [sum ‹k› ‹a› ‹b›] ‹e›`
: sums ‹e› for ‹k› from the natural number ‹a› to ‹b›, in closed form when ‹b› is a variable and by its exact value when ‹b› is a numeral, with a theorem about the sum over `Finset.Icc a b`.
`#cas [sum ‹k› ‹a› ∞] ‹e›`
: sums the series of ‹e› from ‹a›, for polynomials times geometric terms and for even zeta values, with a `HasSum` theorem, which states that the series converges and has that sum.
:::

`sum` gives a finite sum in closed form, including sums with a symbolic upper bound, and the sums of some series. With a variable upper bound $n$, SymLean finds the closed form and proves it for every $n$ by induction. With a numeral upper bound, it adds the terms one by one and gives the exact rational value. And with ∞ as the upper bound, it finds the sum of the series and proves that the series converges to it.

The closed forms come from two places. Sums of terms $c\,k^j r^k$ cover polynomials, geometric terms and their products, and Gosper’s algorithm covers hypergeometric terms, such as the telescoping $1/(k(k+1))$. The series form takes the terms $c\,k^j r^k$ with $|r| < 1$, and $c/k^{2m}$ through the values of the zeta function.

## Details and Options

- For a variable upper bound $n$ and the printed closed form $F$, the theorem is `∀ n : ℕ, ∑ k ∈ Finset.Icc a n, e = F`, and `∀ n : ℕ, a - 1 ≤ n → ∑ k ∈ Finset.Icc a n, e = F` when $a \ge 2$. For a numeral $b$ it is `∑ k ∈ Finset.Icc a b, e = v` with the exact rational $v$.
- A polynomial divided by a geometric term, such as `k ^ 11 / 2 ^ k`, is summed as the polynomial times a geometric term.
- Gosper’s algorithm takes hypergeometric terms `c ^ k * R k` with a rational function `R` and a rational $c > 0$, and the label of the answer then says “(Gosper)”. Its work is bounded where it grows. It needs the shifts between the factors of the ratio of consecutive terms: they are tested one by one up to a bound on the distance of their roots, as for `1 / k ^ 6 - 1 / (k + 1) ^ 6`, when that bound is small, and otherwise found as the integer roots of a resultant of degree at most 100. The polynomials of the closed form have degree at most 100: `1 / (k * (k + 101))` is the last of its family that the command proves, and `1 / (k * (k + 1000))`, which needs degree 999, is refused with that degree. The kernel check grows with the degree, and `1 / (k * (k + 96))` takes about 40 seconds. A summand outside these bounds is refused with what the command would need. The search checks `maxHeartbeats` at each step, except while it finds the integer roots of a resultant: for `1 / ((k ^ 10 + 10 ^ 40) * ((k + 1) ^ 10 + 10 ^ 40))` that step takes about two minutes.
- The summand contains the summation variable and nothing else. A summand with a parameter, such as `a / (k * (k + 1))`, is refused.
- A summand that is undefined in the range is refused. A numeral upper bound sums at most 200 terms, and each term must be an exact rational number.
- For a series the theorem is `HasSum (fun k : ℕ ↦ e (k + a)) S`, with the shift written out: the series converges and its sum is `S`. A term with $|r| \ge 1$ is refused before any proof: its series diverges.
- There are no options. In a proof, [[cas]] proves the closed forms of finite sums, but not the statements about series.

## Examples

### Basic Examples

The sum of the first $n$ squares, with the theorem for every $n$:

```lean
#cas [sum k 1 n] (k^2)
```

---

A telescoping sum, by Gosper’s algorithm:

```lean
#cas [sum k 1 n] (1 / (k * (k + 1)))
```

---

A geometric series:

```lean
#cas [sum k 0 ∞] ((1/2)^k)
```

### Scope

A finite geometric sum, and a polynomial times a geometric term:

```lean
#cas [sum k 0 n] (2^k)
```

```lean
#cas [sum k 1 n] (k * 2^k)
```

---

A sum from 3. The theorem holds for $n \ge 2$, and at $n = 2$ the sum is empty:

```lean
#cas [sum k 3 n] (2*k + 1)
```

---

A numeral upper bound gives the exact value:

```lean
#cas [sum k 1 10] (k^2)
```

---

Gosper’s algorithm on a sum that starts at 2, where the summand is defined:

```lean
#cas [sum k 2 n] (1 / (k ^ 2 - 1))
```

---

Series of polynomials times geometric terms, with a positive and with a negative ratio:

```lean
#cas [sum k 1 ∞] (k / 2^k)
```

```lean
#cas [sum k 0 ∞] ((k + 1) * (-1/2)^k)
```

---

The Basel problem, with a `HasSum` statement:

```lean
#cas [sum k 1 ∞] (1/k^2)
```

---

A zeta value with the first terms left out:

```lean
#cas [sum k 3 ∞] (6/k^2)
```

### Applications

A closed form in a proof. `cas` proves it by induction, and only the three standard axioms are used:

```lean
theorem sum_squares :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  cas

#print axioms sum_squares
```

### Properties and Relations

The partial sums $2 - (1/2)^n$ of the geometric series tend to its sum 2:

```lean
#cas [sum k 0 n] ((1/2)^k)
```

### Possible Issues

The harmonic numbers have no closed form in hypergeometric terms:

```lean error
#cas [sum k 1 n] (1 / k)
```

A numeral upper bound gives the exact value:

```lean
#cas [sum k 1 10] (1/k)
```

---

The closed forms cover polynomial, geometric and hypergeometric terms:

```lean error
#cas [sum k 1 n] (sin k)
```

---

A series with ratio $|r| \ge 1$ diverges, and the message says why it matters in Mathlib:

```lean error
#cas [sum k 0 ∞] (2^k)
```

---

Odd zeta values, such as $\zeta(3)$, are refused:

```lean error
#cas [sum k 1 ∞] (1/k^3)
```

---

The summand must be defined in the whole range. Start the sum at 1:

```lean error
#cas [sum k 0 ∞] (1/k^2)
```

### Neat Examples

The sum of the first $n$ cubes is the square of the sum of the first $n$ integers:

```lean
#cas [sum k 1 n] (k^3)
```

---

The value $\zeta(4) = \pi^4/90$:

```lean
#cas [sum k 1 ∞] (1/k^4)
```
