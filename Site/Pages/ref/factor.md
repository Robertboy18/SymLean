+++
id = "factor"
kind = "mode"
title = "factor"
summary = "Factors a polynomial with rational coefficients, with a theorem that the product equals the input."
forms = ["CAS.Command.casFactorCommand"]
see_also = ["expand", "roots", "polynomialGCD", "apart", "together", "oracle"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [factor] ‹p›`
: factors the polynomial ‹p› with rational coefficients and proves that the product equals ‹p›.
:::

`factor` writes a polynomial as a product, which is usually the quickest way to read off its zeros and their multiplicities. The theorem is the identity $p = q$ for all real values of the variables, proved by `ring`. So the product is always right, even when the factors could be split further.

How far it factors depends on what you import. SymLean on its own finds rational roots, perfect powers and homogeneous forms. With Hex, the factors are proved irreducible over $\mathbb{Q}$. I like that the two claims stay apart: the identity is always proved, and irreducibility is claimed only when Hex has certified it.

## Details and Options

- The theorem is $\forall x_1, \dots, x_n,\; p = q$ about Mathlib’s real numbers, where $q$ is the printed product, proved by `ring`.
- The input is a polynomial with rational coefficients in one or more variables.
- Without Hex, the factors come from the rational roots with their multiplicities, from perfect powers, and from homogeneous polynomials in two variables. A remaining factor of degree two or more is printed whole, and it is not claimed to be irreducible.
- With `CASHex.Factor` imported (built by `lake -R -Khex=on build CASHex`), the factors are irreducible over $\mathbb{Q}$ whenever Hex certifies every one of them, and the output says “factors irreducible over ℚ”. The [Hex guide](guide:hex) has the details.
- With `CASOracle.Factor` imported, `#cas [factor, oracle := sympy] ‹p›` asks an external system for the factors. `sage`, `flint` and `maxima` work the same way, and `pari` in one variable. The identity is checked in Lean, and irreducibility is not. See [[oracle]].
- The tactic [[cas]] proves the same identities.

## Examples

### Basic Examples

A cubic with a double root:

```lean
#cas [factor] (2*x^3 - 3*x^2 + 1)
```

---

Two variables:

```lean
#cas [factor] (x^3*y - x*y^3)
```

### Scope

Four rational roots:

```lean
#cas [factor] (x^4 - 5*x^2 + 4)
```

---

The rational roots can be large:

```lean
#cas [factor] (x^3 - 200000001*x^2 + 200000000*x)
```

---

Without Hex, a factor with no rational root stays whole. Here it is $x^4 + x^2 + 1 = (x^2 - x + 1)(x^2 + x + 1)$:

```lean
#cas [factor] (x^6 - 1)
```

---

With Hex the factorization is complete over $\mathbb{Q}$. These lines are from the library’s Hex examples, with the output they pin:

```lean quote=CASHex/Examples.lean
#cas [factor] (x ^ 6 - 1)
```

```lean quote=CASHex/Examples.lean
#cas [factor] (x ^ 4 + 4)
```

### Options

An external system can propose the factors. Here SymPy finds Sophie Germain’s identity, and Lean checks the product:

```lean quote=tests/oracle/Oracles.lean
#cas [factor, oracle := sympy] (x ^ 4 + 4)
```

---

SageMath with two variables:

```lean quote=tests/oracle/Oracles.lean
#cas [factor, oracle := sage] (x ^ 3 - y ^ 3)
```

### Applications

The first factorization as a theorem, for every real `x`. Only the three standard axioms are used:

```lean
theorem cubic_with_double_root (x : ℝ) :
    2 * x ^ 3 - 3 * x ^ 2 + 1 = (x - 1) ^ 2 * (2 * x + 1) := by
  cas

#print axioms cubic_with_double_root
```

### Properties and Relations

[[expand]] multiplies the factors out again:

```lean
#cas [expand] ((x - 1)^2*(2*x + 1))
```

---

[[fullSimplify]] chooses between the factored and the expanded form by size. For $x^3 - x$ it keeps the input, which is smaller than $x (x - 1)(x + 1)$:

```lean
#cas [factor] (x ^ 3 - x)
```

```lean
#cas [fullSimplify] (x^3 - x)
```

---

[[polynomialGCD]] finds the factors two polynomials share:

```lean
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)
```

### Possible Issues

Without Hex, $x^4 + 4$ stays whole, although it factors over $\mathbb{Q}$ as the Hex line above shows:

```lean
#cas [factor] (x^4 + 4)
```

---

A polynomial that stays whole is not claimed to be irreducible. Here $x^2 + 1$ is irreducible, and the report does not say so:

```lean
#cas [factor] (x^2 + 1)
```

---

Mathematica is not one of the oracles:

```lean quote=tests/oracle/Refusals.lean
#cas [factor, oracle := mathematica] (x ^ 2 - 1)
```

### Neat Examples

With Hex, a rational content comes out in front and the double root shows as a square:

```lean quote=CASHex/Examples.lean
#cas [factor] (x ^ 3 / 2 - x ^ 2 + x / 2)
```
