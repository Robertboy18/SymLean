+++
id = "continuedFraction"
kind = "mode"
title = "continuedFraction"
summary = "The continued fraction $[a_0; a_1, \\dots, a_k]$ of a rational number, with a theorem that it equals the number."
forms = ["CAS.Command.casContinuedFractionCommand"]
see_also = ["fromContinuedFraction", "extendedGCD", "N", "integerDigits"]
tutorials = ["proving"]
+++

::: usage
`#cas [continuedFraction] ‹q›`
: gives the continued fraction [a₀; a₁, …, aₖ] of the rational literal ‹q› and proves ‹q› = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ)) in ℚ.
:::

I like continued fractions because they answer a concrete question: how well can a number be approximated by fractions with small denominators? Cutting the expansion off gives the convergents, and each convergent is closer to the number than every fraction with a smaller denominator. `continuedFraction` computes the expansion of a rational number by recording the quotients of Euclid’s algorithm. The theorem is the identity in $\mathbb{Q}$ together with the conditions on the terms that make the expansion unique, so it does not just say that the expansion has the value ‹q›. It says that this is the continued fraction of ‹q›.

## Details and Options

- ‹q› is an exact rational literal, built from natural and decimal literals with `-`, `/` and parentheses, such as `415/93`, `-7/3` or `0.25`. A decimal is the exact rational it denotes, so `3.14159` is $\tfrac{314159}{100000}$.
- The theorem is `q = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ))` in `ℚ`, and for $k \ge 1$ also `(∀ a ∈ [a₁, …, aₖ], 1 ≤ a) ∧ 2 ≤ aₖ`. These conditions make the expansion unique, since $[\dots, a_k - 1, 1]$ has the same value. `norm_num` proves the identity and `decide` the conditions.
- The terms come from Euclid’s algorithm, with $a_0 = \lfloor q \rfloor$, which may be 0 or negative. An integer $n$ gives `[n]`.
- An irrational number has an infinite continued fraction and is refused. A decimal approximation from [[N]] is a rational literal, with a finite continued fraction that agrees with the infinite one in its first terms.
- There are no options. [[fromContinuedFraction]] goes the other way.

## Examples

### Basic Examples

The expansion of $\tfrac{415}{93}$, with its theorem:

```lean
#cas [continuedFraction] (415/93)
```

---

A decimal is the exact rational it denotes, here $\tfrac{314159}{100000}$:

```lean
#cas [continuedFraction] (3.14159)
```

### Scope

A negative number has a negative first term, $-\tfrac{7}{3} = -3 + \cfrac{1}{1 + \cfrac{1}{2}}$:

```lean
#cas [continuedFraction] (-7/3)
```

---

An integer is its own continued fraction:

```lean
#cas [continuedFraction] (5)
```

---

A number between 0 and 1 starts with 0:

```lean
#cas [continuedFraction] (0.25)
```

### Applications

The theorem as a statement in `ℚ`, with the axioms its proof uses:

```lean
theorem continued_fraction_415_93 : (415 / 93 : ℚ) = 4 + 1 / (2 + 1 / (6 + 1 / 7)) := by
  cas

#print axioms continued_fraction_415_93
```

---

A tropical year is about 365.24219 days. The convergents $\tfrac{1}{4}$, $\tfrac{7}{29}$ and $\tfrac{8}{33}$ of its fractional part are leap year rules: one leap day in 4 years for the Julian calendar, and 8 in 33 for Omar Khayyam’s:

```lean
#cas [continuedFraction] (365.24219)
```

### Properties and Relations

[[fromContinuedFraction]] goes back from the terms to the number:

```lean
#cas [fromContinuedFraction] [4, 2, 6, 7]
```

---

Cutting off the expansion of 3.14159 gives its convergents, among them $\tfrac{333}{106}$ and Zu Chongzhi’s $\tfrac{355}{113}$:

```lean
#cas [fromContinuedFraction] [3, 7, 15]
```

```lean
#cas [fromContinuedFraction] [3, 7, 15, 1]
```

---

The terms 4, 2, 6 and 7 are the quotients of Euclid’s algorithm on 415 and 93. The convergent before the last, $[4; 2, 6] = \tfrac{58}{13}$, gives the Bézout coefficients of [[extendedGCD]], $415 \cdot 13 - 93 \cdot 58 = 1$:

```lean
#cas [fromContinuedFraction] [4, 2, 6]
```

```lean
#cas [extendedGCD] (415, 93)
```

### Possible Issues

An irrational number has an infinite continued fraction, and the mode refuses it:

```lean error
#cas [continuedFraction] (sqrt 2)
```

---

Powers are not literals, so I write $2^{10}$ out as 1024:

```lean error
#cas [continuedFraction] (1/2^10)
```

```lean
#cas [continuedFraction] (1/1024)
```

---

A decimal is exact, so its expansion follows the number it rounds only for a while. $\pi$ begins $[3; 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, \dots]$, and its decimal to 15 digits has 12 where $\pi$ has 14:

```lean
#cas [continuedFraction] (3.14159265358979)
```

### Neat Examples

The continued fraction of $e$ is $[2; 1, 2, 1, 1, 4, 1, 1, 6, \dots]$, with the even numbers in every third place. Its decimal to 16 digits keeps the pattern up to the term 12:

```lean
#cas [continuedFraction] (2.718281828459045)
```
