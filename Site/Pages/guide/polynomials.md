+++
id = "polynomials"
kind = "guide"
title = "Polynomials"
summary = "Coefficients, degrees, division, gcds, interpolation and Gröbner bases, with theorems about Mathlib’s `Polynomial` and `MvPolynomial`."
related_guides = ["algebra", "equations", "oracles", "tactics"]
tutorials = ["first-hour", "proving"]
+++

In the [algebra guide](guide:algebra) a polynomial is an expression in real variables. Here the polynomials themselves are the objects, together with the ideals they generate. In one variable you can read off coefficients and degrees, divide with remainder, take gcds and lcms and interpolate, and the theorems are about Mathlib’s `ℚ[X]`: its coefficients, its degree, `gcd`, `lcm`, `/` and `%`. In several variables they are about ideals of `MvPolynomial (Fin n) ℚ`: a Gröbner basis spans the same ideal as its input, and a membership comes with its cofactors.

::: commands
### Coefficients and degrees
- coefficient
- coefficientList
- exponent
### Division and GCDs
- polynomialGCD
- polynomialLCM
- polynomialQuotient
- polynomialRemainder
- polynomialQuotientRemainder
### Interpolation
- interpolatingPolynomial
### Ideals and Gröbner bases
- groebner
- member
:::

What I like about the gcd is that its proof doesn’t replay the Euclidean algorithm. It comes with a certificate, the cofactors of both inputs and a Bézout identity, which together show that the gcd divides both inputs and that every common divisor divides it. The kernel checks those identities however long the algorithm ran, and the theorem is about Mathlib’s own `gcd` in `ℚ[X]`:

```lean
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)
```

A Gröbner basis comes with two theorems: it spans the same ideal as the input, and it is a Gröbner basis for the lexicographic order. That order eliminates variables, so the last element is a polynomial in $y$ alone:

```lean
#cas [groebner x, y] [x^2 + y^2 - 5, x*y - 2]
```

The last element factors as $(y^2 - 1)(y^2 - 4)$, so $y$ is $\pm 1$ or $\pm 2$, and the first element then gives $x$. That’s the point of the lexicographic order: the common zeros can be read off one variable at a time.

Division, gcds and lcms work in one variable with rational coefficients. Mathlib’s operations are total, with `gcd 0 0 = 0`, `p / 0 = 0` and `p % 0 = p`, so a zero divisor, or two zero inputs to a gcd, is refused. The Gröbner search stops after 400 polynomials or 4000 pairs and suggests an oracle. The theorem says that the basis is a Gröbner basis of the same ideal, but not that it is the reduced one. And when `member` finds a nonzero remainder, it refuses, and the refusal proves nothing about non-membership.

In a proof, the tactic [[cas]] proves goals about `coeff`, `natDegree`, `gcd`, `lcm`, `/` and `%` in `ℚ[X]`, and goals `f ∈ Ideal.span {g₁, …, gₘ}` in any commutative ring, with cofactors from a Gröbner basis.
