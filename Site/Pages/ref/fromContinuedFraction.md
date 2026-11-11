+++
id = "fromContinuedFraction"
kind = "mode"
title = "fromContinuedFraction"
summary = "The rational value of a finite continued fraction $[a_0; a_1, \\dots, a_k]$, with a theorem in $\\mathbb{Q}$."
forms = ["CAS.Command.casFromContinuedFractionCommand"]
see_also = ["continuedFraction", "extendedGCD", "fibonacci"]
tutorials = ["proving"]
+++

::: usage
`#cas [fromContinuedFraction] [‹a₀›, ‹a₁›, …, ‹aₖ›]`
: gives the rational number ‹a₀› + 1 / (‹a₁› + 1 / (⋯ + 1 / ‹aₖ›)) in lowest terms and proves the identity in ℚ.
:::

`fromContinuedFraction` takes the terms of a continued fraction and gives back its value, as Mathematica’s `FromContinuedFraction` does. It undoes [[continuedFraction]]. Where I use it most is for convergents. Cut an expansion off after a few terms and you get a fraction that is closer to the number than every fraction with a smaller denominator, which is why $\tfrac{22}{7}$ and $\tfrac{355}{113}$ approximate $\pi$ so well. The theorem is the identity in $\mathbb{Q}$, and `norm_num` proves it.

## Details and Options

- The argument is a list of integer literals `[a₀, a₁, …, aₖ]` with at least one term. The first term may be zero or negative, and the others are positive.
- The theorem is `q = a₀ + 1 / (a₁ + 1 / (⋯ + 1 / aₖ))` in `ℚ`, for the printed $q$ in lowest terms.
- The last term may be 1. Since $[\dots, a_{k-1}, 1] = [\dots, a_{k-1} + 1]$, such a list has the value of a shorter one: `[1, 1, 1]` and `[1, 2]` are both $\tfrac{3}{2}$. [[continuedFraction]] gives the shorter form, whose last term is at least 2.
- There are no options.

## Examples

### Basic Examples

The value of $[4; 2, 6, 7]$:

```lean
#cas [fromContinuedFraction] [4, 2, 6, 7]
```

---

Three ones:

```lean
#cas [fromContinuedFraction] [1, 1, 1]
```

### Scope

The first term may be negative:

```lean
#cas [fromContinuedFraction] [-3, 1, 2]
```

---

A first term 0 gives a number between 0 and 1:

```lean
#cas [fromContinuedFraction] [0, 1, 2]
```

### Applications

The theorem as a statement in `ℚ`, with the axioms its proof uses:

```lean
theorem from_continued_fraction_ones : (3 / 2 : ℚ) = 1 + 1 / (1 + 1 / 1) := by
  cas

#print axioms from_continued_fraction_ones
```

---

$\pi = [3; 7, 15, 1, 292, \dots]$, and its convergents are the classical approximations. $[3; 7]$ is Archimedes’ $\tfrac{22}{7}$, and $[3; 7, 15, 1]$ is Zu Chongzhi’s $\tfrac{355}{113}$, which is good to six decimals because the next term 292 is large:

```lean
#cas [fromContinuedFraction] [3, 7]
```

```lean
#cas [fromContinuedFraction] [3, 7, 15, 1]
```

---

The convergents of $\sqrt{2} = [1; 2, 2, 2, \dots]$ solve Pell’s equation $x^2 - 2 y^2 = \pm 1$. Six terms give $\tfrac{99}{70}$, and $99^2 - 2 \cdot 70^2 = 1$:

```lean
#cas [fromContinuedFraction] [1, 2, 2, 2, 2, 2]
```

```lean
example : (99 : ℤ) ^ 2 - 2 * 70 ^ 2 = 1 := by norm_num
```

### Properties and Relations

[[continuedFraction]] goes the other way and gives back the terms:

```lean
#cas [continuedFraction] (415/93)
```

---

`[1, 1, 1]` and `[1, 2]` have the same value, and [[continuedFraction]] gives the one whose last term is at least 2:

```lean
#cas [fromContinuedFraction] [1, 2]
```

```lean
#cas [continuedFraction] (3/2)
```

### Possible Issues

A continued fraction has at least the term $a_0$:

```lean error
#cas [fromContinuedFraction] []
```

---

Only the first term may be zero or negative:

```lean error
#cas [fromContinuedFraction] [1, 0, 2]
```

---

The terms are integers:

```lean error
#cas [fromContinuedFraction] [1, 1/2]
```

---

The terms go in a list, in square brackets:

```lean error
#cas [fromContinuedFraction] (4, 2, 6, 7)
```

### Neat Examples

Ten ones give the quotient $\tfrac{89}{55}$ of the [[fibonacci]] numbers $F_{11}$ and $F_{10}$, a convergent of the golden ratio $\varphi = [1; 1, 1, \dots]$:

```lean
#cas [fromContinuedFraction] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
```
