+++
id = "home"
kind = "home"
title = "SymLean"
tagline = "A verified computer algebra system in Lean."
authors = ["Robert Joseph George", "Anima Anandkumar", "Thomas Y. Hou", "Changhe Yang", "Peicong Song"]
affiliation = "Caltech"
summary = "SymLean is a verified computer algebra system in Lean. Every answer comes with a theorem, and Lean's kernel has checked the proof."
+++

::: figure #teaser class="teaser"
```lean
#cas [integrate x] (atan x)
```
Caption: An antiderivative of $\arctan x$, with the Lean theorem underneath. Open the certificate to follow the differentiation step by step.
:::

## Abstract {#abstract}

I wanted to do the calculations in my proofs the way I do them in Mathematica, and keep a proof at the end. So we built SymLean. Ask for a derivative, an integral, the roots of a polynomial, or a bound on a box. You get the answer and a theorem about Mathlib’s functions, including the hypotheses it needs, such as a nonzero denominator.

The same calculations work inside a proof: `cas` handles identities, derivatives, integrals and limits, and `cega` handles numerical bounds. In both, a search proposes the answer and Lean checks a proof of it. If the check fails, the calculation is refused. What I like about this split is that the search is free to be clever, and even to be wrong, because nothing it finds becomes a theorem until Lean has checked the proof.

Computer algebra systems do get things wrong. [Why SymLean](guide:why) collects mistakes on record from several of them, shows what SymLean does on the same inputs, and says where the idea comes from.

## What SymLean does {#what}

You write `#cas`, pick a mode, and give it an expression. Variables don’t need declarations here, because each one is a real number. Here are six to try.

::: figure #six-examples
::: grid
### Algebra
```lean
#cas [factor] (2*x^3 - 3*x^2 + 1)
```
### Calculus
```lean
#cas [integrate x in [0, 1]] (x * exp x)
```
### Series and limits
```lean
#cas [series x 0 7] (sin x)
```
### Equations
```lean
#cas [roots x] (x ^ 5 - x - 1 = 0)
```
### Special functions
```lean
#cas (zeta 4)
```
### Certified numerics
```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```
:::
Caption: The quintic root and the Gaussian integral come back as decimals, and the statements underneath give their error bounds.
:::

[Getting started](tutorial:first-hour) takes these calculations into a Lean file of your own, and the [[docs|documentation]] lists the commands, their options and more examples.

## How an answer becomes a theorem {#pipeline}

::: figure #pipeline-figure svg="pipeline.svg"
Caption: Finding the antiderivative is the search step. Differentiating it gives Lean something it can check.
:::

Take the integral at the top of the page. The search proposes $F(x) = x \arctan x - \tfrac{1}{2} \log(1 + x^2)$, and from there on everything is checked. A verified differentiator computes $F'$, a verified normalizer shows that $F' - \arctan x$ is $0$, and the fundamental theorem of calculus turns that into a statement about $\int_a^b \arctan x \, dx$. Finding $F$ takes a search, but checking it takes one derivative, so I’m happy to let an untrusted program do the finding.

Each answer also carries its conditions. Lean’s division is total, so $1/0 = 0$, and an identity that a computer algebra system prints without conditions can be false as a Lean statement. Take $(x^4 - 1)/(x^2 - 1) = x^2 + 1$. At $x = 1$ the left side is $0/0$, which is $0$ in Lean, while the right side is $2$. The identity holds only where $x^2 - 1 \ne 0$. The report lists that condition, and the checked theorem underneath assumes it as `x * x - 1 ≠ 0`, the same condition with the square written as a product:

```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```

## What you have to trust {#trust}

Lean’s kernel checks every proof, and SymLean adds no axioms of its own. Here is the integral of $x e^x$ from $0$ to $1$, from the calculus example above, as a theorem, proved by `cas`, together with the axioms its proof uses. They are the three standard axioms that all of Mathlib uses:

```lean
theorem integral_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

#print axioms integral_x_exp
```

Everything else is allowed to make mistakes. The search routines, the interval planners and the optional oracle backends can all propose a wrong answer, and Lean accepts an answer only after the corresponding proof checks. There is one exception, and you have to ask for it. If you turn on [[options|`cega.nativeCertificates`]], for one declaration or for a whole build with `-Kcertificates=fast`, then `cega [fast]` evaluates its finite certificates with compiled code. You then trust Lean’s compiler as well, and every theorem that uses such a certificate records an extra axiom that you can see with `#print axioms`. The option stays off unless you turn it on. The [trust tutorial](tutorial:trust) goes through all of this.

## How it relates to Mathlib, Hex and SymPy {#relations}

::: figure #relations-figure svg="relations.svg"
Caption: Mathlib supplies the definitions used in the statements. Hex and the external systems can help find answers, and Lean still checks the proofs.
:::

**Mathlib.** The theorems are stated with Mathlib’s `Real.arctan`, `HasDerivAt`, interval integrals, `Real.Gamma` and `Matrix.det`, so you can use them in any Mathlib proof as they are. It works the other way too: Mathlib’s tactics `ring`, `field_simp`, `norm_num`, `positivity` and `linarith` are routes inside `cas`.

**Hex.** [Hex](https://github.com/leanprover/hex) is the Lean FRO’s verified computer algebra, and it is strong exactly where the core of SymLean is weak, in exact algebra over the integers and finite fields. With the optional library `CASHex`, `factor` proves the irreducibility of the factors over $\mathbb{Q}$ whenever Hex certifies every one of them, and you get primality certificates and fast determinants, each checked in the kernel. The [Hex guide](guide:hex) has the details.

**SymPy, SageMath, Maxima, PARI/GP and FLINT.** These are mature systems and very good at search, and I don’t need to trust them to use them. Through [DSLean](https://github.com/taterowney/DSLean), the optional library `CASOracle` asks them for a proposal, and SymLean proves it in Lean or refuses it. This line is from the library’s oracle tests:

```lean quote=tests/oracle/Oracles.lean
#cas [factor, oracle := pari] (x ^ 6 - 1)
```

The report is careful about what it claims: the identity is checked, and the irreducibility of the factors isn’t. The [[oracle]] page says how to build the library and set the systems up.

## Credits {#credits}

SymLean is built by a team at Caltech: Robert Joseph George and Anima Anandkumar, in collaboration with Thomas Y. Hou, Changhe Yang and Peicong Song. It is built on [Mathlib](https://github.com/leanprover-community/mathlib4), its certified numerics use [FloatLib](https://github.com/lean-dojo/FloatLib), and the optional routes use [Hex](https://github.com/leanprover/hex) and [DSLean](https://github.com/taterowney/DSLean). Thank you to the Lean and Mathlib communities for the mathematics, the tools and the conversations. LeanPDE, for partial differential equations, is a separate project built on SymLean.
