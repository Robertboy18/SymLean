+++
id = "powerMod"
kind = "call"
title = "powerMod"
summary = "The remainder of $a^b$ modulo $m$ by repeated squaring, for exponents with hundreds of digits, with a theorem in `ℕ`."
calls = ["powerMod"]
see_also = ["modularInverse", "jacobiSymbol", "extendedGCD", "chineseRemainder", "integerDigits"]
guide = "number-theory"
tutorials = ["proving", "trust"]
+++

::: usage
`#cas (powerMod ‹a› ‹b› ‹m›)`
: gives the remainder of ‹a›^‹b› modulo ‹m› for natural numbers ‹a›, ‹b› and a positive modulus ‹m›, and proves `‹a› ^ ‹b› % ‹m› = ‹r›`.
:::

`powerMod` computes $a^b$ modulo $m$ without ever building the integer $a^b$, which for a large exponent would be far too big to write down. The proof is repeated squaring, so its size grows with the number of digits of the exponent and not with the exponent itself. Exponents with hundreds of digits are fine.

## Details and Options

- ‹a›, ‹b› and ‹m› are natural numbers, literals or closed integer expressions, with $m \ge 1$.
- The theorem is `a ^ b % m = r` in `ℕ`, with $r < m$. The proof is Mathlib’s `Mathlib.Meta.NormNum.evalNatPowMod`, repeated squaring.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

The remainder of $3^{1000}$ modulo 7:

```lean
#cas (powerMod 3 1000 7)
```

### Scope

An exponent with 27 digits, modulo the prime $10^9 + 7$, with the theorem that the kernel checked:

```lean
#cas (powerMod 2 123456789123456789123456789 1000000007)
```

### Applications

In a proof, [[cas]] proves the equation, with `propext` as its only axiom:

```lean
theorem three_pow_mod_seven : 3 ^ 1000 % 7 = 4 := by
  cas

#print axioms three_pow_mod_seven
```

### Properties and Relations

Fermat’s little theorem gives $a^{p-1} \equiv 1 \pmod p$ for a prime $p$ that does not divide $a$. Here $2^6 \equiv 1 \pmod 7$ and $100 = 6 \cdot 16 + 4$, so $2^{100} \equiv 2^4 = 16 \equiv 2$:

```lean
#cas (powerMod 2 100 7)
```

---

For an odd prime $p$, Euler’s criterion $a^{(p-1)/2} \equiv (a / p) \pmod p$ relates the remainder to the symbol of [[jacobiSymbol]]. For $a = 2$ and $p = 7$ the power is $2^3 = 8 \equiv 1$, and the symbol is 1:

```lean
#cas (jacobiSymbol 2 7)
```

### Possible Issues

Every natural number is 0 modulo 1, and Mathlib’s `a % 0 = a`. The call asks for $m \ge 1$:

```lean error
#cas (powerMod 2 10 0)
```

---

The call takes three arguments:

```lean error
#cas (powerMod 2 10)
```
