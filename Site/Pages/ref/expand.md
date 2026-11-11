+++
id = "expand"
kind = "mode"
title = "expand"
summary = "Multiplies out a polynomial, with a theorem that the expansion equals the input for all real values."
forms = ["CAS.Command.casExpandCommand"]
see_also = ["factor", "collect", "trigExpand", "fullSimplify", "coefficientList"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [expand] ‹e›`
: multiplies out the products and natural powers of the polynomial ‹e› and proves that the expansion equals ‹e›.
:::

`expand` multiplies an expression out so you can see its terms and their coefficients. The theorem is an identity for all real values of the variables, proved by `ring`, so it holds with no conditions at all.

It also knows the classical families of polynomials. Ask for `ChebyshevT 5 x` and the theorem is about Mathlib’s own Chebyshev polynomial `Polynomial.Chebyshev.T`, which is the one you want when the expansion goes into a proof.

## Details and Options

- The theorem is $\forall x_1, \dots, x_n,\; e = p$ about Mathlib’s real numbers, where $p$ is the printed expansion, proved by `ring`.
- The input is a polynomial with rational coefficients in real variables, or a call `ChebyshevT n x`, `ChebyshevU n x`, `HermiteH n x`, `HermiteHe n x`, `LegendreP n x` or `BernoulliB n x`. For a call, the theorem is the expansion of Mathlib’s polynomial, or for `LegendreP` of SymLean’s `CAS.Analysis.SpecialFunctions.legendre`. The call pages, such as [[ChebyshevT]], have the details.
- An expression that is not a polynomial, such as `sin (x + y)` or `1 / (x + 1) ^ 2`, is printed unchanged. [[trigExpand]] expands sines and cosines of sums, and [[together]] and [[apart]] rewrite rational functions.
- [[collect]] groups an expansion by the powers of one variable, and [[coefficient]] and [[coefficientList]] read off its coefficients.
- The tactic [[cas]] proves the same identities.

## Examples

### Basic Examples

A product in two variables:

```lean
#cas [expand] ((x + 1)^3 * (y - 2))
```

---

The binomial theorem for $n = 4$:

```lean
#cas [expand] ((a + b)^4)
```

---

Rational coefficients stay exact:

```lean
#cas [expand] ((x - 1/2)^2 * (x + 2))
```

### Scope

The Chebyshev polynomial $T_5$. The theorem holds in every commutative ring:

```lean
#cas [expand] (ChebyshevT 5 x)
```

---

The Legendre polynomial $P_5$, with rational coefficients:

```lean
#cas [expand] (LegendreP 5 x)
```

---

The Hermite polynomials, in the physicists’ and the probabilists’ normalization:

```lean
#cas [expand] (HermiteH 5 x)
```

```lean
#cas [expand] (HermiteHe 3 x)
```

---

A Chebyshev polynomial of the second kind and a Bernoulli polynomial:

```lean
#cas [expand] (ChebyshevU 2 x)
```

```lean
#cas [expand] (BernoulliB 2 y)
```

### Applications

The first expansion as a theorem. It holds for all real `x` and `y`, and only the three standard axioms are used:

```lean
theorem cube_times_linear (x y : ℝ) :
    (x + 1) ^ 3 * (y - 2) =
      x ^ 3 * y - 2 * x ^ 3 + 3 * x ^ 2 * y - 6 * x ^ 2 + 3 * x * y - 6 * x + y - 2 := by
  cas

#print axioms cube_times_linear
```

### Properties and Relations

[[factor]] goes the other way:

```lean
#cas [factor] (2*x^3 - 3*x^2 + 1)
```

---

[[collect]] groups the terms by the powers of one variable, with the other variables in the coefficients:

```lean
#cas [collect x] ((1 + a*x)^2 + b*x)
```

### Possible Issues

The argument of a function is not expanded:

```lean
#cas [expand] (sin (x + y))
```

---

[[trigExpand]] expands sines and cosines of sums:

```lean
#cas [trigExpand] (sin (x + y))
```

---

A quotient is left as it is. [[together]] and [[apart]] rewrite rational functions:

```lean
#cas [expand] (1 / (x + 1) ^ 2)
```
