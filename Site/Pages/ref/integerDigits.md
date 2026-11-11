+++
id = "integerDigits"
kind = "mode"
title = "integerDigits"
summary = "The digits of a natural number in any base $b \\ge 2$, with a theorem about Mathlib’s `Nat.digits`."
forms = ["CAS.Command.casIntegerDigitsCommand"]
see_also = ["powerMod", "binomial", "continuedFraction", "fromContinuedFraction"]
tutorials = ["proving"]
+++

::: usage
`#cas [integerDigits] ‹n›`
: lists the decimal digits of the natural number ‹n›, most significant first, and proves `Nat.digits 10 ‹n› = [d₀, …, dₖ]`.
`#cas [integerDigits] (‹n›, ‹b›)`
: lists the digits of ‹n› in the base ‹b› ≥ 2, most significant first, and proves `Nat.digits ‹b› ‹n› = [d₀, …, dₖ]`.
:::

`integerDigits` writes a number in a base, as Mathematica’s `IntegerDigits` does, with the most significant digit first, the way you would write the number down. The one thing to watch is that the theorem goes the other way. It is about Mathlib’s `Nat.digits`, which lists the digits least significant first, so its list is the printed one reversed. I think that’s the right trade. The report reads naturally, and the theorem comes in the form that Mathlib’s lemmas about digits expect, such as `Nat.ofDigits_digits` and `Nat.modEq_nine_digits_sum`.

## Details and Options

- ‹n› and ‹b› are natural numbers: literals, or closed integer expressions such as `2^100`. Without ‹b› the base is 10.
- The theorem is `Nat.digits b n = [d₀, d₁, …, dₖ]`, with the least significant digit $d_0$ first, and the report prints the reverse `[dₖ, …, d₁, d₀]`. `norm_num` proves the equation, with `decide +kernel` and `simp` as fallbacks.
- A digit in base $b$ is a natural number below $b$, so the digits of 255 in base 16 are `[15, 15]`.
- The digits of 0 form the empty list, since `Nat.digits b 0 = []`.
- There are no options.

## Examples

### Basic Examples

The decimal digits of 2026:

```lean
#cas [integerDigits] 2026
```

---

The binary digits of 1234:

```lean
#cas [integerDigits] (1234, 2)
```

### Scope

Any base from 2 up. In base 16 the digits run from 0 to 15:

```lean
#cas [integerDigits] (255, 16)
```

---

Closed expressions, here $2^{10} - 1$, which has ten ones in base 2:

```lean
#cas [integerDigits] (2^10 - 1, 2)
```

---

Zero has no digits:

```lean
#cas [integerDigits] (0, 10)
```

### Applications

The theorem, with the axioms its proof uses. Mathlib’s list starts with the last binary digit of 1234:

```lean
theorem digits_1234 : Nat.digits 2 1234 = [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] := by
  cas

#print axioms digits_1234
```

---

Mathlib’s `Nat.ofDigits` reads digits back into a number, and `Nat.ofDigits_digits` turns the theorem into a statement about it:

```lean
example : Nat.ofDigits 2 [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] = 1234 := by
  rw [← digits_1234, Nat.ofDigits_digits]
```

---

Repeated squaring computes $a^{100}$ from the binary digits of 100: a squaring for each digit after the first, and a multiplication for each of those that is 1, eight steps in all:

```lean
#cas [integerDigits] (100, 2)
```

### Properties and Relations

The last three digits of $2^{100}$ are its remainder modulo 1000, which [[powerMod]] computes without the other 28 digits:

```lean
#cas [integerDigits] (2^100)
```

```lean
#cas (powerMod 2 100 1000)
```

### Possible Issues

Mathlib’s list is the printed one reversed, so a statement about the digits of 2026 has the last digit first:

```lean
example : Nat.digits 10 2026 = [6, 2, 0, 2] := by
  cas
```

---

Base 1 has no positional digits, and the mode refuses it. Mathlib’s `Nat.digits 1 n` is the list of $n$ ones:

```lean error
#cas [integerDigits] (1234, 1)
```

---

The argument is a number or a pair:

```lean error
#cas [integerDigits] (1234, 2, 10)
```

### Neat Examples

The digits of $1001^{10}$ in base 1000 are the binomial coefficients $\binom{10}{k}$, because none of them reaches 1000 and the expansion of $(1000 + 1)^{10}$ has no carries. [[binomial]] gives them one at a time:

```lean
#cas [integerDigits] (1001^10, 1000)
```

```lean
#cas (binomial 10 3)
```
