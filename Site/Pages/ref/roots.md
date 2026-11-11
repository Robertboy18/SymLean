+++
id = "roots"
kind = "mode"
title = "roots"
summary = "Every real or complex root of a polynomial equation, exact or enclosed, with a theorem that the list is complete."
forms = ["CAS.Command.casRootsCommand", "CAS.Command.casComplexRootsCommand"]
see_also = ["solve", "findRoot", "reduce", "factor", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [roots ‹x›] (‹lhs› = ‹rhs›)`
: lists every real solution of a polynomial equation in ‹x›, the rational ones exactly and the others as truncated decimals, and proves that the list is complete.
`#cas [roots ‹z› in ℂ] (‹lhs› = ‹rhs›)`
: lists every complex solution once, with exact values when all of them are Gaussian rationals and certified enclosures otherwise, and proves that the list is complete.
`#cas (digits := ‹d›) [roots ‹x›] (‹lhs› = ‹rhs›)`
: the same as the first form with ‹d› decimals, from 1 to 60.
:::

`roots` gives you every real solution of a polynomial equation. A rational solution is printed exactly, and an irrational one as a decimal truncated to 20 places, with a rational interval of width $10^{-20}$ around it in the theorem. For me the important part is the last clause of the theorem, which says that there are no other solutions. So the count in the report is the number of real solutions: when it says a cubic has one real root, it has one, and not one that a numerical method happened to find.

With `in ℂ` the list has the complex solutions too. When all of them are Gaussian rationals, such as $i$ or $1/2 + i/2$, they are exact. Otherwise each real one has an interval, and each pair of conjugates $\alpha \pm i\beta$ has an interval for $\alpha$ and one for $\beta$.

## Details and Options

- For each real solution that is not a printed rational, the report gives a rational interval `(l, u)` of width $10^{-d}$ whose end nearer to zero is the printed decimal. The theorem is the conjunction of `∃! x, x ∈ Set.Ioo l u ∧ lhs = rhs` for each interval, of `lhs = rhs` at each printed rational, and of `∀ x : ℝ, lhs = rhs → (x = r₁ ∨ … ∨ x = rₖ) ∨ x ∈ Set.Ioo l₁ u₁ ∨ …`.
- ‹lhs› and ‹rhs› are polynomials in ‹x› alone with rational coefficients, of any degree, and a polynomial `p` alone stands for `p = 0`. Each solution is listed once, whatever its multiplicity. An equation without real solutions gives “no real solutions”.
- `(digits := d)`, from 1 to 60 and by default 20, is the number of decimals of the enclosed real solutions. The complex form has no options.
- With `in ℂ`, for the expanded difference `p` of the two sides, the theorem is `∀ z : ℂ, p = 0 ↔ z = w₁ ∨ … ∨ z = wₖ` when every root is a Gaussian rational. Otherwise it is `∀ z : ℂ, p = 0 ↔ z ∈ [r₁, …, z₁, conj z₁, …]`, where each root is a `CAS.AlgRoot.complex` number with intervals for its real and imaginary parts.
- In a proof, [[cas]] proves bounds on a real root, such as `∃ x : ℝ, x ^ 3 - 2 * x - 5 = 0 ∧ 2 < x ∧ x < 3`, and counts of real roots `Fintype.card (p.rootSet ℝ) = n` for `p : ℚ[X]`.

## Examples

### Basic Examples

The cubic on which Newton showed his method, with its only real solution:

```lean
#cas [roots x] (x^3 - 2*x - 5 = 0)
```

---

Rational and irrational solutions together. The double root 1 is listed once:

```lean
#cas [roots x] ((x - 1)^2 * (x + 2) * (x^2 - 2))
```

---

Complex roots that are Gaussian rationals are exact:

```lean
#cas [roots z in ℂ] (z ^ 2 + 1 = 0)
```

### Scope

A polynomial alone stands for the equation $p = 0$:

```lean
#cas [roots x] (x^5 - x - 1)
```

---

Only rational solutions:

```lean
#cas [roots x] ((x-1)*(x-2)*(x-3)*(x-4) = 0)
```

---

No real solutions:

```lean
#cas [roots x] (x^2 + 1)
```

---

Rational solutions are exact, however small:

```lean
#cas [roots x] (x^2 = 1/10^30)
```

---

Complex roots with rational real and imaginary parts:

```lean
#cas [roots z in ℂ] (2 * z ^ 2 - 2 * z + 1 = 0)
```

```lean
#cas [roots z in ℂ] ((z - 1) ^ 3 * (z ^ 2 + 1) = 0)
```

---

Enclosed complex roots, two pairs of conjugates:

```lean
#cas [roots z in ℂ] (z ^ 4 + 1 = 0)
```

---

One real root and one pair of conjugates:

```lean
#cas [roots z in ℂ] (z ^ 3 = 2)
```

### Options

`(digits := 40)` gives 40 decimals, with intervals of width $10^{-40}$:

```lean
#cas (digits := 40) [roots x] (x^2 = 2)
```

### Applications

Bounds on a root in a proof. `cas` proves them, and only the three standard axioms are used:

```lean
theorem roots_cubic : ∃ x : ℝ, x ^ 3 - 2 * x - 5 = 0 ∧ 2 < x ∧ x < 3 := by
  cas

#print axioms roots_cubic
```

---

A count of real roots, for a polynomial over $\mathbb{Q}$:

```lean
open Polynomial in
example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  cas
```

### Properties and Relations

The real root of $z^5 - z - 1$ among its complex roots is the one that the real form finds above:

```lean
#cas [roots z in ℂ] (z ^ 5 - z - 1 = 0)
```

### Possible Issues

An identity has every real number as a solution, so there is no list:

```lean error
#cas [roots x] (x = x)
```

---

Only polynomial equations. For other equations, [[findRoot]] certifies one root in an interval:

```lean error
#cas [roots x] (sin x = 0)
```

---

At most 60 decimals:

```lean error
#cas (digits := 61) [roots x] (x^2 = 2)
```

### Neat Examples

The sixth roots of unity, two real and two pairs of conjugates:

```lean
#cas [roots z in ℂ] (z ^ 6 = 1)
```
