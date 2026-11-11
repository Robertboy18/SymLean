+++
id = "product"
kind = "mode"
title = "product"
summary = "A finite product in closed form, telescoped or in factorials, with a theorem for every upper bound."
forms = ["CAS.Command.casProductCommand"]
see_also = ["sum", "rsolve", "factorial", "factor", "gamma"]
tutorials = ["proving"]
+++

::: usage
`#cas [product ‹k› ‹a› ‹n›] ‹e›`
: gives the product of ‹e› for ‹k› from the natural number ‹a› to the variable ‹n› in closed form, and proves it for every ‹n› by induction.
:::

`product` looks for a closed form of a finite product with a symbolic upper bound, and proves it for every $n$ by induction. The theorem is about Mathlib’s `∏ k ∈ Finset.Icc a n`, and the factorials in the answer are `Nat.factorial`.

The factors it takes are a constant times powers of linear factors $k + s$ with integer shifts $s$. When the exponents add up to zero, the product telescopes to a rational function of $n$, and when every shift is nonnegative, it is a product of factorials.

## Details and Options

- For the printed closed form `P`, the theorem is `∀ n : ℕ, ∏ k ∈ Finset.Icc a n, e = P`, and `∀ n : ℕ, a - 1 ≤ n → ∏ k ∈ Finset.Icc a n, e = P` when $a \ge 2$. The product over an empty range is 1.
- ‹e› is a rational function of ‹k›. Without Hex its linear factors must be written in the input, so `(k - 1) * (k + 1) / k ^ 2` has a closed form and `1 - 1 / k ^ 2` is refused. With `import CASHex.Factor`, the numerator and the denominator are factored completely over $\mathbb{Q}$.
- A factor that vanishes in the range is refused, and so are a rational shift such as `2*k - 1` and an irreducible factor of degree 2 or more: the factor must be a constant times powers of linear factors $k + s$ with an integer $s$.
- The upper bound must be a variable. There are no options.
- In a proof, [[cas]] proves the closed form for every $n$.

## Examples

### Basic Examples

A telescoping product, with the theorem for every $n$:

```lean
#cas [product k 1 n] ((k + 1) / k)
```

---

The product of the first $n$ integers:

```lean
#cas [product k 1 n] (k)
```

### Scope

A constant times a linear factor:

```lean
#cas [product k 1 n] (2*k)
```

---

Two linear factors give two factorials:

```lean
#cas [product k 1 n] (k * (k + 1))
```

---

With a shift of 2, the telescoping product leaves two factors:

```lean
#cas [product k 1 n] ((k + 2) / k)
```

---

A product from 2, the partial products of $\prod_{k \ge 2} (1 - 1/k^2)$ with the linear factors written out. The theorem holds for $n \ge 1$:

```lean
#cas [product k 2 n] ((k - 1)*(k + 1)/k^2)
```

---

A constant factor. From 0 to $n$ there are $n + 1$ of them:

```lean
#cas [product k 0 n] (3)
```

---

Negative and fractional constants:

```lean
#cas [product k 1 n] (-2)
```

```lean
#cas [product k 1 n] (2/3)
```

### Applications

The closed form in a proof. `cas` proves it by induction, and only the three standard axioms are used:

```lean
theorem product_telescoping : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, ((k : ℝ) + 1) / k = n + 1 := by
  cas

#print axioms product_telescoping
```

### Properties and Relations

The closed form $n!$ at $n = 10$ is the value of the call [[factorial]]:

```lean
#cas (factorial 10)
```

### Possible Issues

Without Hex the factors must be written out, and $1 - 1/k^2$ is the product from 2 above in another form:

```lean error
#cas [product k 2 n] (1 - 1/k^2)
```

With Hex, `CASHex.Factor` factors it, and the closed form is the same. This line is from the library’s Hex examples, with the output it pins:

```lean quote=CASHex/Examples.lean
#cas [product k 2 n] (1 - 1/k^2)
```

---

A rational shift is refused, here $2k - 1 = 2(k - 1/2)$, since the shifts must be integers:

```lean error
#cas [product k 1 n] (2*k - 1)
```

---

The factor $k^2 + 1$ is irreducible over $\mathbb{Q}$. Without Hex the message suggests factoring it, and with Hex it is refused for the same reason as a rational shift:

```lean error
#cas [product k 1 n] (k^2 + 1)
```

```lean quote=CASHex/Examples.lean
#cas [product k 1 n] (k^2 + 1)
```

---

A factor that vanishes in the range is refused, here the denominator $k$ at $k = 0$:

```lean error
#cas [product k 0 n] (1 / k)
```

---

The upper bound must be a variable. For the value $5!$, the call [[factorial]] is the one to use:

```lean error
#cas [product k 1 5] (k)
```

---

Only rational functions of $k$:

```lean error
#cas [product k 1 n] (sin k)
```
