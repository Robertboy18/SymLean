+++
id = "differential-equations"
kind = "guide"
title = "Differential equations"
summary = "Linear differential equations solved exactly, certified initial-value problems, Laplace and Fourier transforms, and Fourier series."
related_guides = ["calculus", "numerics", "series-limits", "sums"]
tutorials = ["proving", "trust"]
+++

With a differential equation, the first thing I want to know is whether it has a closed form, and the tools here split along that line. When the equation is in one of the supported families, start with the exact solution. A linear equation gets its general solution, with the theorem that every solution is in the family, and an initial-value problem gets its only solution. When there is no closed form, [[ndsolve]] proves enclosures of the solution. The transforms and the Fourier coefficients live here too, and they are theorems about Mathlib’s integrals of the input function.

::: commands
### Differential equations
- dsolve
- ndsolve
### Transforms
- laplace
- inverseLaplace
- fourierTransform
### Fourier series
- fourier
- fourierCos
- fourierSin
:::

The harmonic oscillator, started at $y(0) = 1$ with $y'(0) = 0$. Look at the shape of the theorem. It’s an equivalence about every twice-differentiable function, so it says that $\cos x$ solves the problem and also that nothing else does:

```lean
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)
```

The solutions of this Riccati equation are not elementary, so I ask for numbers instead. The theorem has three parts: a solution exists on $[0, 1]$, it is unique, and at the two times I asked for, it lies in the printed intervals:

```lean
#cas [ndsolve y t in [0, 1], y 0 = 1/2, at [1/2, 1]] (y' = y ^ 2 + t)
```

Here is where each tool stops. `dsolve` takes equations that are linear in $y$ and its derivatives. With rational constant coefficients the order can be anything, while coefficients that depend on $x$ are handled in first order only, through an integrating factor. The initial values have to be given at one point, so for a boundary-value problem I fit the constants of the general solution myself. `ndsolve` takes a right side that is a polynomial in $t$ and $y$, of degree at most 4 in each, on an interval of length at most 20. Near a blow-up of the solution no certified step exists, and the command is refused. The transforms cover a fixed menu: `laplace` takes sums of at most eight terms $c\,t^n e^{at} g(bt)$, with $g$ a cosine, sine, hyperbolic cosine or hyperbolic sine or no $g$ at all, `inverseLaplace` a proper rational function of $s$, and `fourierTransform` a Gaussian. Mathlib has no uniqueness theorem for the Laplace transform, so `inverseLaplace` gives an inverse transform and doesn’t claim it’s the only one. The Fourier series work on $[-\pi, \pi]$ with integer frequencies, or on $[0, L]$ for sums of terms $c\,x^j e^{ax}$.
