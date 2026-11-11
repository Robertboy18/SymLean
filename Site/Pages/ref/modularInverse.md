+++
id = "modularInverse"
kind = "call"
title = "modularInverse"
summary = "The inverse of an integer modulo $m \\ge 2$ in `ZMod m`, or a proof that there is none."
calls = ["modularInverse"]
see_also = ["extendedGCD", "powerMod", "chineseRemainder", "jacobiSymbol"]
guide = "number-theory"
tutorials = ["proving"]
+++

::: usage
`#cas (modularInverse ‹a› ‹m›)`
: gives the inverse of the integer ‹a› modulo ‹m› ≥ 2 and proves it in `ZMod ‹m›`, or proves that there is none.
:::

`modularInverse` finds the inverse of ‹a› modulo $m$, the $r$ with $a r \equiv 1 \pmod m$. We get it from the extended Euclidean algorithm, and the theorem is about `ZMod m`, where the kernel checks that the product of ‹a› and the answer is 1. When ‹a› and $m$ have a common factor there is no inverse, and the theorem you get says so instead.

## Details and Options

- ‹a› is an integer and ‹m› a natural number with $m \ge 2$, literals or closed integer expressions.
- When $\gcd(a, m) = 1$ the theorem is `(a : ZMod m) * r = 1 ∧ (a : ZMod m)⁻¹ = r` with $0 \le r < m$, by kernel evaluation in `ZMod m` and `ZMod.inv_eq_of_mul_eq_one`.
- Otherwise the theorem is `Nat.gcd |a| m = g ∧ ¬ IsUnit (a : ZMod m)` with $g > 1$, by `ZMod.isUnit_iff_coprime`, and the report prints the gcd.
- The inverse comes from the extended Euclidean algorithm. [[extendedGCD]] prints its Bézout coefficients.
- In a proof, [[cas]] proves `(a : ZMod m)⁻¹ = b` for a unit $a$ with the certificate of the call.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

$3 \cdot 4 = 12 \equiv 1 \pmod{11}$, and the theorem has both facts:

```lean
#cas (modularInverse 3 11)
```

### Scope

The integer may be negative, and $(-3) \cdot 2 = -6 \equiv 1 \pmod 7$:

```lean
#cas (modularInverse (-3) 7)
```

---

The private exponent of a small RSA key, the inverse of $e = 17$ modulo $\varphi(3233) = 3120$:

```lean
#cas (modularInverse 17 3120)
```

---

When $\gcd(a, m) > 1$ there is no inverse, and the theorem says so:

```lean
#cas (modularInverse 6 9)
```

### Applications

In a proof, [[cas]] proves the inverse with the certificate of the call:

```lean
theorem inverse_three_mod_eleven : (3 : ZMod 11)⁻¹ = 4 := by
  cas

#print axioms inverse_three_mod_eleven
```

### Properties and Relations

[[extendedGCD]] prints the Bézout coefficients, $17 \cdot (-367) + 3120 \cdot 2 = 1$. Modulo 3120 the coefficient $-367$ is $3120 - 367 = 2753$, the inverse above:

```lean
#cas [extendedGCD] (17, 3120)
```

### Possible Issues

`ZMod 1` is the zero ring, where every element is its own inverse, and the call asks for $m \ge 2$:

```lean error
#cas (modularInverse 3 1)
```
