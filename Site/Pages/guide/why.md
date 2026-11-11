+++
id = "why"
kind = "guide"
title = "Why SymLean"
summary = "What can go wrong in the output of a computer algebra system, mistakes on record from Mathematica to SymPy, Sage, Maxima, FLINT and PARI/GP, and how proving the answer catches them."
+++

A computer algebra system answers with an expression, and whether that expression is right depends on conditions the output rarely states: a domain, a branch, an interval without poles, a precision. When I use one for a quick calculation, I can usually fill them in myself. In a proof those conditions are the point, so SymLean answers with a theorem that carries them, and Lean’s kernel checks it.

## What has to be proved {#proved}

For each kind of operation, here is what a system prints, what a proof needs on top of it, and what SymLean proves:

::: table
Operation | A system prints | What has to be proved as well | In SymLean
Simplification | an equal expression | that the two agree on the stated domain: for real $x$, $\sqrt{x^2} = \lvert x \rvert$, and $\sqrt{x^2} = x$ needs $x \ge 0$ | [[simplify]] proves that they agree under the conditions it prints
Differentiation | a formula for the derivative | that the function has this derivative wherever the theorem claims it, with the conditions of the denominators and branches | [[derive]] proves `HasDerivAt` under its conditions
Definite integration | a value | that the antiderivative $F$ satisfies $F' = f$ on the whole interval, poles and endpoints included, so that the fundamental theorem of calculus applies | [[integrate]] proves $F' = f$ there first
Root finding | a list of roots | that each listed value is a root, and for all roots, that there are no others | [[roots]] proves the list complete
Numerical computation | digits | that the exact value lies within a proved bound, rounding and truncation included | [[N]] proves every printed digit
:::

In an analytic proof, the last row decides whether a number can be part of the argument at all. A decimal value of a constant is evidence. A proved inequality between the constant and a threshold is a step of the proof, and that’s the one I need.

## Mistakes on record {#cases}

The list below comes from the projects’ own trackers and from published papers. Each entry names the version and the date of its report, and none is a claim about a later version. I don’t mean it as a scorecard. These are good systems kept up by careful people, and several of the bugs have been fixed since they were reported. What it shows is that even mature tools sometimes print a wrong answer that looks like any other.

- **Simplification.** SymPy 1.14.0 rewrites `acot(-x)` to `-acot(x)`, which is false at $x = 0$, where SymPy’s $\operatorname{acot} 0$ is $\pi/2$ ([sympy#30588](https://github.com/sympy/sympy/issues/30588), September 2026, fixed on the development branch). On the development branch of November 2026, `Abs(1/(2*n - 1) - 1/2).subs(n, 1)` gave $-1/2$ with $n$ declared a nonnegative integer, because a sign rule took the expression to be monotonic across its pole at $n = 1/2$ ([sympy#30976](https://github.com/sympy/sympy/issues/30976), introduced on 2026-10-29 and fixed on 2026-11-09, before any release).
- **Differentiation.** From 2015 to 1.14.0, SymPy gave $-1/(x\sqrt{1 - x^2})$ as the derivative of $\operatorname{asech} x$. For $x < -1$ that is the negative of the derivative of $\operatorname{acosh}(1/x)$, SymPy’s own definition of $\operatorname{asech}$ ([sympy#30335](https://github.com/sympy/sympy/issues/30335), August 2026, fixed on the development branch after 1.14.0).
- **Definite integration.** Fateman’s review of Mathematica, written in 1990 and 1991, reports that `Integrate[1/x^2, {x, -1, 1}]` gave $-2$, which is what $-1/x$ gives at the endpoints, across the pole at $0$. With the DefiniteIntegr package of version 1.2 loaded, the answer was $\infty$ ([J. Symbolic Comput. 13 (1992)](https://doi.org/10.1016/S0747-7171%2810%2980011-2), section 10). SymPy 1.14.0 gives $\int_0^1 \sqrt{2 - x}\,\sqrt{1/(2 - x)}\,dx = -1$, although the integrand is $1$ on the whole interval ([sympy#29792](https://github.com/sympy/sympy/issues/29792), May 2026, open on 2026-11-11).
- **Root finding.** Sage 10.9 gave $0$ and $2$ as the roots of $2x - 2$ over $\mathbb{Z}/4$, but neither is a root, and the roots are $1$ and $3$ ([sagemath/sage#42796](https://github.com/sagemath/sage/issues/42796), September 2026, fixed in 10.10). In FLINT 3.6.0, `fmpz_poly_num_real_roots_vca` counts one real root of $2x^4 - 2x^3 - 2x^2 - 3x - 4$, which has two, because a bound on the positive roots comes out too small ([flintlib/flint#2893](https://github.com/flintlib/flint/issues/2893), October 2026, open on 2026-11-11). SymPy 1.14.0 solves $x^3 + px + q = 0$ for real $p$ and $q$, and the solution at $p = 0$, $q = -1$ gives $0, 0, 0$, while the equation is $x^3 = 1$ ([sympy#30837](https://github.com/sympy/sympy/issues/30837), October 2026, open on 2026-11-11). Maxima’s `nroots(x^2 - 2, 0, a)` counted one root for a bigfloat $a$ just below $\sqrt{2}$, because the endpoint was rounded to a rational on the other side of the root ([Maxima bug #4958](https://sourceforge.net/p/maxima/bugs/4958/), August 2026, reported on a development build after 5.49 and fixed after 5.50.0, and the rounding was already in Maxima’s source of 2000).
- **Numerical computation.** SymPy 1.14.0 evaluates $\csc(231\pi/500 + 26944)$, a number near $-89.08$, to two digits as `3.7e+2`, and its assumptions call the number positive ([sympy#29850](https://github.com/sympy/sympy/issues/29850), June 2026, open on 2026-11-11). In FLINT 3.2.0, whose ball arithmetic is meant to be rigorous, `arb_nint` of the ball $[0.5 \pm 0.001]$ returned a ball that encloses $[-1, 0]$ and misses $1$, the nearest integer to $0.501$ ([flintlib/flint#2293](https://github.com/flintlib/flint/issues/2293), April 2025, fixed in 3.3.0).
- **Exact algebra.** Durán, Pérez and Varona found that Mathematica 8 to 9.0.1 computed wrong determinants of some integer matrices with large entries, and different values for the same matrix on repeated runs. Wolfram acknowledged the report they filed in October 2013, and their matrices still showed it in version 10 ([Notices AMS 61 (2014)](https://doi.org/10.1090/noti1173)). In Sage 9.7 to 10.6, with parallel linear algebra switched on, the Hecke operator $T_5$ on the one-dimensional space $S_{10}(\Gamma_1(2))$ came out as $534154/3$ instead of $870$. A change of default algorithm in 10.7 hid it, and the maintainers trace the fix to 10.8 ([sagemath/sage#41267](https://github.com/sagemath/sage/issues/41267), December 2025). In Sage 10.2 to 10.9 the reduced echelon form of some sparse rational matrices was wrong, a $2 \times 3$ matrix among them, because the multimodular algorithm verified its result against a bound computed from the wrong matrix ([sagemath/sage#42411](https://github.com/sagemath/sage/issues/42411), June 2026, fixed in 10.10). `primecertisvalid` in PARI/GP 2.17.2 and 2.19.0 accepted elliptic-curve primality certificates for composite numbers, $5053 = 31 \cdot 163$ among them ([PARI bug #2723](https://pari.math.u-bordeaux.fr/cgi-bin/bugreport.cgi?bug=2723), October 2026, patched on the development branch).

The two I find most telling are failed checks. Sage’s echelon form tested its own result, and `primecertisvalid` exists to validate certificates. So a check is only as good as the program that runs it. In SymLean the check is a proof, and the program that accepts it is Lean’s kernel, the same one that checks every proof in Mathlib.

## The same inputs in SymLean {#same-inputs}

Here is SymLean on four of the same inputs. On Fateman’s integral, SymLean’s own search makes the old mistake and proposes $-2$. I like this example because the search really is wrong and nothing bad comes of it: the proof needs $x \ne 0$ on all of $[-1, 1]$, so the value is refused, and the message names the condition that failed:

```lean error
#cas [integrate x in [-1, 1]] (1 / x ^ 2)
```

Next, Sage’s matrix. Sage’s algorithm checked its result against a bound computed from the wrong matrix. The theorem here needs no such bound: it gives the row operations $E$ with $E A = R$, $E$ invertible and $R$ in reduced echelon form, and those three facts determine $R$:

```lean
#cas [rowReduce] !![1000001000, -1/501000500, 3; 1, -1, 1]
```

FLINT’s quartic has two real roots. Each interval in the answer holds exactly one, and the theorem says there are no others:

```lean
#cas [roots x] (2*x^4 - 2*x^3 - 2*x^2 - 3*x - 4 = 0)
```

And SymPy’s number, with $\csc$ written as $1/\sin$. Where SymPy printed `3.7e+2`, each of these fifteen digits is proved:

```lean
#cas [N 15] (1 / sin (231 * π / 500 + 26944))
```

## Where the idea comes from {#precedent}

None of this is a new idea, and I’m glad it isn’t. The design, in which an untrusted search proposes an answer and the prover checks it, is Harrison and Théry’s, and it has since been used in HOL Light, Rocq, Isabelle and Lean. A computer algebra system built on top of a proof assistant is Kaliszyk and Wiedijk’s. SymLean follows this design. What we added is reach: many kinds of calculation behind one Lean front end, checked in the kernel by default.

- Harrison and Théry combined HOL with Maple by separating the search for a solution from checking it: Maple searched, and HOL proved the result (“A Skeptic’s Approach to Combining HOL and Maple”, [J. Automated Reasoning 21 (1998)](https://doi.org/10.1023/A:1006023127567)).
- Kaliszyk and Wiedijk built a prototype computer algebra system on top of HOL Light, with an interface close to those of Maple and Mathematica, in which every expression has a precise meaning and the prover proves each simplification (“Certified Computer Algebra on Top of an Interactive Theorem Prover”, [Calculemus 2007, LNCS 4573](https://doi.org/10.1007/978-3-540-73086-6_8)).
- Harrison verified nonlinear real formulas in HOL Light with sums of squares found by semidefinite programming, a numerical search whose certificate is easy to check in the prover ([TPHOLs 2007](https://doi.org/10.1007/978-3-540-74591-4_9)). Rocq’s `psatz` uses his driver to the external solver CSDP, and the expression the solver returns is normalized by `ring` and checked to be $-1$ ([Rocq reference manual, Micromega](https://rocq-prover.org/doc/master/refman/addendum/micromega.html)).
- Li, Passmore and Paulson decide univariate real polynomial problems in Isabelle/HOL with certificates from Mathematica. Isabelle checks the sample points, and it also checks that the roots Mathematica returned are all the real roots ([J. Automated Reasoning 62 (2019)](https://doi.org/10.1007/s10817-017-9424-6)).
- Lewis and Wu connected Lean 3 with Mathematica, used Mathematica as an untrusted oracle in proof search, and verified some of its computations in Lean ([J. Automated Reasoning 66 (2022)](https://doi.org/10.1007/s10817-021-09611-1)).
- Mathlib’s `linarith` lets an untrusted oracle search for a certificate of unsatisfiability, a list of coefficients of the hypotheses, and proves the contradiction from it, with `ring` checking the linear combination (`Mathlib.Tactic.Linarith.Frontend`).
- Mathlib’s `polyrith` asked SageMath for the coefficients of a `linear_combination` call, which Lean then checked. It was withdrawn in September 2025, after the public Sage server it used shut down ([mathlib4#29547](https://github.com/leanprover-community/mathlib4/pull/29547)). The calls it had suggested never depended on Sage.

## What this does not mean {#limits}

Here is what it does not mean.

- SymLean doesn’t compute everything Mathematica can. A search can fail, and a refusal proves nothing: SymLean finds no antiderivative for SymPy’s integrand above and says so.
- A list is complete only when the theorem says so. [[roots]] proves that no root is missing, while [[findRoot]] proves one root and its uniqueness near the printed value.
- The oracles are not verified. They propose, and their answers enter only through a proof ([Oracles](guide:oracles)).
- The default profile trusts Lean’s kernel and its standard axioms. Native evaluation is opt-in and adds Lean’s compiler ([What you trust](tutorial:trust#native)).
- Lean checks theorems about the data it is given. A build that embedded a stale copy of a data file would get a correct theorem about the stale data, so the build has to track its input files.
- The theorem is about what you wrote, with Lean’s definitions, where $1/0 = 0$ ([What a refusal means](tutorial:trust#refusal)).

To try it, start with [your first hour](tutorial:first-hour), or browse the [documentation](docs:index).
