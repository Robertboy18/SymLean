+++
id = "jacobiSymbol"
kind = "call"
title = "jacobiSymbol"
summary = "The Jacobi symbol $(a / n)$ of an integer and an odd natural number, with a theorem about Mathlib’s `jacobiSym`."
calls = ["jacobiSymbol"]
see_also = ["powerMod", "primeQ", "modularInverse"]
guide = "number-theory"
tutorials = ["proving"]
+++

::: usage
`#cas (jacobiSymbol ‹a› ‹n›)`
: gives the Jacobi symbol (‹a› / ‹n›) of the integer ‹a› and the odd natural number ‹n›, one of −1, 0 and 1, and proves `jacobiSym ‹a› ‹n› = ‹j›`.
:::

`jacobiSymbol` computes the Jacobi symbol, and what it’s good for is ruling out squares modulo an odd integer. For a prime $n$ it is the Legendre symbol. For every odd $n$ the value $-1$ proves that ‹a› is not a square modulo ‹n›, but for a composite $n$ the value $1$ proves nothing of the kind, as Possible Issues shows.

## Details and Options

- ‹a› is an integer and ‹n› an odd natural number, literals or closed integer expressions.
- The theorem is `jacobiSym a n = j` for Mathlib’s `jacobiSym`, by `CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop`. The kernel runs a loop that takes out factors 2 with the value of $(2 / n)$ and otherwise swaps the arguments by quadratic reciprocity.
- $(a / 1) = 1$, and $j = 0$ exactly when $\gcd(a, n) > 1$.
- For every odd $n$, $j = -1$ shows that $a$ is not a square modulo $n$, by `ZMod.nonsquare_of_jacobiSym_eq_neg_one`.
- In a proof, [[cas]] proves `jacobiSym a n = j` for odd $n$ by the same run of the loop.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

The symbol $(1001 / 9907)$, with the theorem that the kernel checked:

```lean
#cas (jacobiSymbol 1001 9907)
```

### Scope

The integer may be negative. For an odd prime $p$, $(-1 / p) = -1$ exactly when $p \equiv 3 \pmod 4$:

```lean
#cas (jacobiSymbol (-1) 7)
```

---

The symbol is 0 exactly when $\gcd(a, n) > 1$, here $\gcd(6, 9) = 3$:

```lean
#cas (jacobiSymbol 6 9)
```

### Applications

`ZMod.nonsquare_of_jacobiSym_eq_neg_one` turns the value $-1$ into a statement about squares, and [[cas]] proves the value:

```lean
theorem not_square_mod_9907 : ¬IsSquare ((1001 : ℤ) : ZMod 9907) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one (by cas)

#print axioms not_square_mod_9907
```

### Properties and Relations

For an odd prime $p$, Euler’s criterion $a^{(p-1)/2} \equiv (a / p) \pmod p$ relates the symbol to [[powerMod]]. For $a = 2$ and $p = 7$, $2^3 = 8 \equiv 1$, and indeed $3^2 = 9 \equiv 2$, so 2 is a square modulo 7:

```lean
#cas (jacobiSymbol 2 7)
```

### Possible Issues

For a composite $n$ the value 1 does not make ‹a› a square. $(2 / 15) = (2 / 3)\,(2 / 5) = (-1)(-1) = 1$, while the squares modulo 15 are 0, 1, 4, 6, 9 and 10:

```lean
#cas (jacobiSymbol 2 15)
```

---

The symbol is defined for odd $n$, and the call takes only those:

```lean error
#cas (jacobiSymbol 2 4)
```
