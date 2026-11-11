+++
id = "first-hour"
kind = "tutorial"
title = "Getting started with SymLean"
summary = "From an empty Lean file to derivatives, integrals, roots and a proof, one command at a time."
+++

Let’s start with a few calculations and then use one of them in a proof. Everything here runs in an ordinary Lean file.

## Setting up {#setup}

SymLean builds with Lean 4.35.0 and Mathlib v4.35.0. In a project on the same toolchain, add it to `lakefile.lean`:

```
require SymLean from git "https://github.com/Robertboy18/SymLean.git" @ "main"
```

Then fetch it, get Mathlib’s cache, and build:

```
lake update SymLean
lake exe cache get
lake build
```

Mathlib comes from its cache, but SymLean itself is compiled on the first build, and the kernel checks every proof in it, every numerical certificate included. So that first build takes about ten minutes on 8 cores. I think it’s worth the wait, since every proof in the library is then checked on your machine. After that, a file that uses SymLean starts with

```
import CAS
```

which brings in `#cas` and the tactics `cas`, `cas?`, `cas_nf`, `cega` and `cega?`.

## A first calculation {#first}

To differentiate, write the mode in brackets and the expression after it. Variables need no declaration: `x`, `a` and `b` are real numbers, and `x` is the one named in the mode. Multiplication is Lean’s `*`, so you write `3 * x` and not `3x`.

```lean
#cas [derive x] (a * x ^ 3 + b * x)
```

The answer comes with the theorem behind it, which the kernel checked. Look at that theorem for a moment. It is a `HasDerivAt` statement for every `x`, `a` and `b`, so it’s a fact you can use later, not just a formula on the screen. In the editor the evidence is folded under `More details`. Here it sits under the report, as the certificate and the computation.

When a rule needs a condition, the answer says so. The rule for a square root needs a positive argument, so this derivative holds where $x + 1 > 0$ (the theorem writes the same condition as `0 < 2 * x + 2`):

```lean
#cas [derive x] (sqrt (2 * x + 2))
```

The condition is enough for the rule to apply, and that’s all it claims. It isn’t meant to be the whole set where the derivative exists.

## Equations, integrals and digits {#more}

The same command solves equations, and here the theorem is an if and only if: for every real $x$, the equation holds exactly at the solutions:

```lean
#cas [solve x] (x ^ 2 - 3 * x + 2 = 0)
```

An antiderivative is checked by differentiating it back, and a definite integral comes out exact when it can be:

```lean
#cas [integrate x] (x * exp x)
```

```lean
#cas [integrate x in [0, 1]] (1 / (1 + x ^ 2))
```

Digits are proved too. Each of these twenty is a digit of $e$, because the theorem traps $e$ between the truncated decimal and the next one up:

```lean
#cas [N 20] (exp 1)
```

No formula in radicals gives the roots of $x^5 - x - 1$. Its real root still has digits, though, and the theorem says it is the only real root:

```lean
#cas [roots x] (x ^ 5 - x - 1 = 0)
```

## From a calculation to a theorem {#theorem}

This is the part I care about most. In a proof you state the result in Mathlib’s language and let a tactic prove it. The first derivative above becomes an ordinary `HasDerivAt` statement:

```lean
example (a b x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ a * t ^ 3 + b * t) (3 * a * x ^ 2 + b) x := by
  cas
```

When you don’t know which call to use, `cas?` proves the goal and suggests the one to keep in the source:

```lean
example : (∫ t in (0 : ℝ)..1, t * Real.exp t) = 1 := by
  cas?
```

Numerical goals go to `cega`, which reads the box from the hypotheses, here $0 \le x \le 1$:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2 + x := by
  cega
```

## When a call fails {#fails}

Sooner or later a call fails, and I think it’s worth seeing what that looks like early. A goal that SymLean can’t prove stays as it was, and the message says what stopped the call. This statement is false, because Mathlib’s `Real.log` is defined everywhere and $\exp(\log(-1)) = \exp(0) = 1$:

```lean error
example (x : ℝ) : Real.exp (Real.log x) = x := by
  cas
```

The message points at the fix. With the hypothesis $0 < x$, which makes the statement true, the same call works:

```lean
example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := by
  cas
```

A refusal says only that no route of SymLean found a proof. It never adds an assumption or changes the statement, and I find that reassuring, because what you see in the file is what was proved. The reference page of each mode shows, under Possible Issues, the ways it can fail and the messages Lean prints. When you’re ready for longer proofs, [[proving|Proving with `cas`]] is the next tutorial.
