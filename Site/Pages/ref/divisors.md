+++
id = "divisors"
kind = "mode"
title = "divisors"
summary = "The divisors of a positive integer below $10^{12}$ in increasing order, with a theorem about Mathlib’s `Nat.divisors`."
forms = ["CAS.Command.casDivisorsCommand"]
see_also = ["divisorSigma", "eulerPhi", "factorInteger", "moebiusMu"]
tutorials = ["proving"]
+++

::: usage
`#cas [divisors] ‹n›`
: lists the divisors of the positive integer ‹n› in increasing order, and proves `Nat.divisors ‹n› = {d₁, …, dₖ}`.
:::

`divisors` lists the divisors themselves, which is what you want for checking a perfect number, an amicable pair or a claim about `Nat.divisors n`. The proof does not factor ‹n›. The kernel pairs each divisor $d \le \sqrt{n}$ with its cofactor $n / d$ and counts the small ones with $\lfloor \sqrt{n} \rfloor$ divisions, so the time depends on the size of ‹n› and not on its factors.

## Details and Options

- ‹n› is a natural number with $1 \le n < 10^{12}$: a literal such as `360`, or a closed integer expression such as `(2^10 - 1)`.
- The theorem is `Nat.divisors n = {d₁, …, dₖ}`, an equation in `Finset ℕ` about Mathlib’s `Nat.divisors`.
- The proof is a counting certificate (`CAS.NumberTheory.divisors_eq_of_cert`). With $m = \lfloor \sqrt{n} \rfloor$, the kernel checks that the listed divisors up to $m$ divide $n$ and are as many as the $d \le m$ with $d \mid n$, and that the others are their cofactors $n / d$. Below $10^{12}$ this takes at most a million divisions.
- The report prints the divisors in increasing order. A number below $10^{12}$ has at most 6720 of them.
- There are no options. [[divisorSigma]] gives the number and the sums of powers of the divisors from the same certificate, without the list.

## Examples

### Basic Examples

The divisors of 12:

```lean
#cas [divisors] 12
```

---

The 24 divisors of $360 = 2^3 \cdot 3^2 \cdot 5$:

```lean
#cas [divisors] 360
```

### Scope

A prime has only the divisors 1 and itself:

```lean
#cas [divisors] 97
```

---

A closed expression, here the Mersenne number $2^{10} - 1 = 3 \cdot 11 \cdot 31$:

```lean
#cas [divisors] (2^10 - 1)
```

---

A million is $2^6 \cdot 5^6$, so it has $7 \cdot 7 = 49$ divisors. The kernel checks them with 1000 divisions:

```lean
#cas [divisors] 1000000
```

### Applications

The theorem, with the axioms its proof uses:

```lean
theorem divisors_twelve : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by
  cas

#print axioms divisors_twelve
```

---

A number is perfect when its divisors other than itself add up to it, so that $\sigma_1(n) = 2 n$. For $8128 = 2^6 \cdot 127$ the sum is $16256$:

```lean
#cas [divisors] 8128
```

```lean
#cas (divisorSigma 1 8128)
```

### Properties and Relations

[[divisorSigma]] gives the number of divisors, $\sigma_0(360) = 24$, and their sum, $\sigma_1(360) = 1170$, without the list:

```lean
#cas (divisorSigma 0 360)
```

```lean
#cas (divisorSigma 1 360)
```

---

A square has an odd number of divisors, because its square root is its own cofactor. For 36 there are nine:

```lean
#cas [divisors] 36
```

### Possible Issues

Mathlib’s `Nat.divisors 0` is the empty set, and 0 is refused:

```lean error
#cas [divisors] 0
```

---

The divisors are certified for $n < 10^{12}$ only:

```lean error
#cas [divisors] (10^12)
```

### Neat Examples

220 and 284 are the smallest amicable pair: the divisors of each, other than the number itself, add up to the other:

```lean
#cas [divisors] 220
```

```lean
#cas [divisors] 284
```
