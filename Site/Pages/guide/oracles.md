+++
id = "oracles"
kind = "guide"
title = "Oracles"
summary = "SymPy, SageMath, Maxima, PARI/GP, FLINT and Gappa as untrusted search, with every proposal proved in Lean or refused."
related_guides = ["hex", "tactics", "certificates"]
tutorials = ["trust"]
+++

A mature computer algebra system is very good at search, and I don’t need to trust it to use it. With the optional library `CASOracle`, a command or the tactic `cas` asks an external tool for a proposal: an antiderivative, a factorization, cofactors, a solution, a closed form, a sum of squares or digits. SymLean then proves the statement from the proposal with its own checkers, and the kernel checks the proof. A proposal that doesn’t check is refused, so a bug in the tool can cost you an answer, but it can’t give you a false theorem.

::: commands
### Asking a tool
- oracle
### In proofs
- cas
- cas-integrate-primitive
### Settings
- options
:::

The requests and the answers go through [DSLean](https://github.com/taterowney/DSLean), by taterowney and the DSLean contributors. The [[oracle]] page lists the tools, what each one is asked, and how to build the library.

The part I like best is what happens in a proof. Here SymPy finds how the goal follows from the hypotheses, and what comes back is a suggestion with no oracle in it, so the proof you keep doesn’t need SymPy at all:

```lean quote=tests/oracle/Oracles.lean suggestion
theorem combination_by_sympy (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]
```
