+++
id = "equations"
kind = "guide"
title = "Equations"
summary = "Polynomial equations, systems and inequalities solved completely, and certified roots of other equations in an interval."
related_guides = ["polynomials", "numerics", "linear-algebra", "algebra"]
tutorials = ["first-hour", "proving"]
+++

Before I solve anything, I ask myself whether I need every solution or one root in a particular interval. For a polynomial equation or system, SymLean gives every real solution, and the theorem says that the printed list holds all of them, so nothing is missing. That completeness is the important part. Rational solutions are exact. An irrational one is a closed form such as $\sqrt 2$ in [[solve]], or it is named by an interval that holds exactly one solution. An inequality is reduced to a union of intervals. And for an equation with other functions, such as $\cos x = x$, I ask for a certified root in an interval.

::: commands
### Exact solutions
- solve
- reduce
### Roots
- roots
- findRoot
:::

Newton showed his method on this cubic. It has one real solution, and the theorem says that there are no others. The decimal is truncated to 20 places, and the theorem puts the root in a rational interval of width $10^{-20}$:

```lean
#cas [roots x] (x^3 - 2*x - 5 = 0)
```

No algebra solves this next equation, so I ask for a root in $[0, 1]$. The theorem says that exactly one solution lies within $10^{-10}$ of the printed value:

```lean
#cas [findRoot x in [0, 1]] (cos x = x)
```

The exact modes stop at polynomials. `solve` and `roots` take polynomial equations with rational coefficients, `reduce` takes polynomial relations and quotients compared with 0, and for other equations `findRoot` is the mode. A nonlinear system goes through a Gröbner basis and needs finitely many complex solutions, so a circle on its own is refused. `findRoot` finds one simple root at a time. It samples the function at 65 points of the interval and narrows the first sign change from the left, and then the kernel checks opposite signs at the ends of a small interval and a derivative of one sign on it. That’s also where it stops. It refuses a double root, or any root where the derivative vanishes, two roots closer than the sample spacing, and a sign change across a pole. For a polynomial with a multiple root, `roots` is the mode to use.
