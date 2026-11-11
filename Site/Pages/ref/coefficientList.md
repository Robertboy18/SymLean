+++
id = "coefficientList"
kind = "mode"
title = "coefficientList"
summary = "Gives the coefficients of a polynomial in one variable, constant term first, with a theorem about `Polynomial.coeff`."
forms = ["CAS.Command.casCoefficientListCommand"]
see_also = ["coefficient", "collect", "exponent", "interpolatingPolynomial"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [coefficientList ‹x›] ‹e›`
: gives the list of coefficients of the polynomial ‹e› in ‹x›, constant term first, and proves that entry `k` is `P.coeff k` for every `k`.
:::

`coefficientList` gives all the coefficients of a polynomial, in order. The list starts with the constant term, so the entry at position $k$ is the coefficient of $x^k$, and the theorem says exactly that: `∀ k, P.coeff k = [c₀, …, c_d].getD k 0`. One statement covers every $k$, even past the end of the list, where `getD` reads $0$, which is the coefficient there.

## Details and Options

- The theorem is `∀ k, P.coeff k = [c₀, …, c_d].getD k 0`, where `P` is ‹e› read as a polynomial as for [[coefficient]]: in `ℚ[X]`, or in `ℝ[X]` with the other variables as constants `C y`. By `Polynomial.ext_iff` and Mathlib’s `coeff_ofCoeffList` it is the identity `P = ofCoeffList [c₀, …, c_d]`, which is proved by evaluation.
- The input is a polynomial with rational coefficients, as for [[collect]]. The other variables stay symbolic in the coefficients. The zero polynomial is refused.
- The order is Mathematica’s. SymPy’s `Poly.all_coeffs` lists the highest degree first.
- The tactic [[cas]] proves single coefficients, as in [[coefficient]]. A single entry also follows from the list statement by specializing $k$ (see Applications).

## Examples

### Basic Examples

The coefficients of $(x + 1)^3 - x/2$:

```lean
#cas [coefficientList x] ((x + 1)^3 - x/2)
```

---

With parameters, the coefficients are symbolic:

```lean
#cas [coefficientList x] (a*x^2 + b*x + c)
```

### Scope

Zero coefficients are listed:

```lean
#cas [coefficientList x] (x^3 + 1)
```

### Applications

The list statement gives each coefficient by specializing $k$. Only the three standard axioms are used:

```lean
open Polynomial in
theorem coefficients_of_cube (h : ∀ k, ((X + 1) ^ 3 : ℚ[X]).coeff k = [1, 3, 3, 1].getD k 0) :
    ((X + 1) ^ 3 : ℚ[X]).coeff 1 = 3 :=
  h 1

#print axioms coefficients_of_cube
```

---

The tactic `cas` proves the single coefficient directly:

```lean
open Polynomial in
example : ((X + 1) ^ 3 : ℚ[X]).coeff 1 = 3 := by
  cas
```

### Properties and Relations

[[coefficient]] gives one entry of the list:

```lean
#cas [coefficient x 1] ((x + 1)^3 - x/2)
```

---

[[exponent]] gives the degree. With a parameter in the leading coefficient, it needs that coefficient to be nonzero:

```lean
#cas [exponent x] (a*x^2 + x + 1)
```

---

[[interpolatingPolynomial]] builds a polynomial from its values:

```lean
#cas [interpolatingPolynomial x] [(0, 1), (1, 3), (2, 7)]
```

### Possible Issues

The mode reads coefficients of polynomials only:

```lean error
#cas [coefficientList x] (x + 1/x)
```
