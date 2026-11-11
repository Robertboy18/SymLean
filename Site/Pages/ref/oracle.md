+++
id = "oracle"
kind = "oracle"
title = "oracle"
summary = "Asks SymPy, SageMath, Maxima, PARI/GP, FLINT or Gappa for a proposal, and proves it in Lean or refuses."
see_also = ["cas", "cas-integrate-primitive", "factor", "nintegrate", "enclose", "options"]
tutorials = ["trust"]
+++

::: usage
`#cas [‹mode›, oracle := ‹tool›] ‹e›`
: asks ‹tool› for the answer of the mode, then proves it in Lean or refuses. The modes are `integrate`, `factor`, `groebner`, `solve`, `nsolve`, `nintegrate`, `eigenvalues`, `enclose`, `dsolve`, `sum` and `sos`.
`#cas (digits := ‹d›) [‹mode›, oracle := ‹tool›] ‹e›`
: the same with ‹d› digits, for `nsolve`, `nintegrate`, `eigenvalues` and `enclose`.
`cas [oracle := ‹tool›]`
: proves a definite integral, a membership in an ideal, an inequality between polynomials or an equation that follows from the hypotheses, from the proposal of ‹tool›. Except for a membership, it suggests a proof that needs no oracle.
:::

Some searches are better done by a mature computer algebra system, and I’d rather hand those to one than write them again in Lean. With `oracle := sympy`, SymLean asks SymPy for a proposal (an antiderivative, a factorization, cofactors, a solution, a closed form or a decimal) and then proves the statement in Lean, or refuses. Nothing the oracle says is trusted. If SymPy proposes something wrong, the proof fails, and you get a refusal instead of a theorem.

The examples here are quoted from the oracle tests, which run with the real tools, and each output is the one that `#guard_msgs` pins there.

## Details and Options

- The tools, the programs they run and their tasks:

::: table
Tool | Program | Modes of `#cas` | Goals of `cas`
`sympy` | SymPy | `integrate`, `factor`, `groebner`, `solve`, `nsolve`, `nintegrate`, `eigenvalues`, `dsolve`, `sum`, `sos` | integrals, memberships, inequalities, equations
`sage` | SageMath | `integrate`, `factor`, `groebner`, `solve`, `nintegrate`, `eigenvalues`, `dsolve`, `sum` | integrals, memberships, equations
`maxima` | Maxima | `integrate`, `factor` | integrals
`pari` | PARI/GP | `factor` in one variable, `nsolve` on a polynomial, `nintegrate`, `eigenvalues` | none
`flint` | FLINT | `factor`, `nsolve` on a polynomial, `nintegrate`, `eigenvalues` | none
`gappa` | Gappa | `enclose` | none
:::

- Nothing an oracle says is trusted. A command builds its theorem from its own input and the proposal, proves it with the checkers of SymLean, refuses a proof that uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and has the kernel check it before anything is reported.
- A missing program, a timeout, or an answer outside the checked expression language is a refusal with the reason.
- What can’t be checked is printed as a hint and isn’t part of the theorem: that a factor is irreducible, that a list of solutions is complete, that a Gröbner basis is reduced, that a family of solutions is the general solution. For factors with irreducibility proved, the [[hex|Hex routes]] of `#cas [factor]` propose the factors and certify each one.
- `nsolve` proves each root by the intermediate value theorem on an interval of width $2 \cdot 10^{-d}$ around the oracle’s decimal, and a root at a rational point, such as an end of the interval, by the equation at that point. The oracles compare the roots of a polynomial with the ends exactly, so that rounding does not drop such a root. The oracle finds the roots with its own numerics, which evaluate `log`, `sqrt`, real powers and quotients as complex functions, so it misses the roots that only Lean’s conventions give, such as those of `Real.sqrt (x - 1/3)` on $[0, 1/3]$, where Lean’s square root is $0$.
- `eigenvalues` proves each eigenvalue by a sign change of the square-free part of the characteristic polynomial on an interval of width $2 \cdot 10^{-d}$. Two eigenvalues closer than about $10^{-d}$ share such an interval and are refused, and more digits separate them.
- An inequality is proved by a sum of squares $S$, found by the Gram-matrix method and made exact as in [Peyrl and Parrilo 2008](https://doi.org/10.1016/j.tcs.2008.09.025), Section 3.1. cvxpy finds positive semidefinite Gram matrices numerically, and we round them to rationals, project them exactly onto the linear conditions of the identity and keep them when an exact $LDL^{\mathsf{T}}$ factorization shows them positive semidefinite. Lean then checks the identity with `ring` and the signs with `positivity`.
- For $0 < p$, some term of $S$ is a positive constant, or a positive constant times strict premises. When no such sum equals $p$, the oracle looks for a multiplier $M$ of degree at most 2, then at most 4, such that $M p$ is one.
- `tests/oracle/run.sh` runs one example per oracle and task with the real tools, and the edge cases of the numerical searches with SymPy and FLINT: roots at the ends of the interval and at the points of SymPy’s grid, a multiple root, and repeated and defective eigenvalues. Then it runs the same commands against programs that answer plausibly but wrongly, never answer, print garbage, answer outside the checked language, or answer with something too large to read. Every one of those is refused.

### Building

::: table
Module | What it adds
`CASOracle.Integrate` | `#cas [integrate x, oracle := ‹tool›]`
`CASOracle.Factor` | `#cas [factor, oracle := ‹tool›]`
`CASOracle.Solve` | `#cas [solve x, oracle := ‹tool›]`
`CASOracle.Numeric` | `nsolve`, `nintegrate`, `eigenvalues` and `enclose` with an oracle
`CASOracle.DSolve` | `#cas [dsolve y x, oracle := ‹tool›]`
`CASOracle.Sum` | `#cas [sum k 1 n, oracle := ‹tool›]`
`CASOracle.Sos` | `#cas [sos x, oracle := ‹tool›]`
`CASOracle.Ideal` | `#cas [groebner x, y, oracle := ‹tool›]` and the tactic `cas [oracle := ‹tool›]`
:::

- `CASOracle` is an optional library, and no module of `CAS` imports it. Build it with `lake -R -Koracle=on build CASOracle`, and `lake -R build` switches back.
- Lake fetches DSLean only with `-Koracle=on`. An update without it drops DSLean from `lake-manifest.json`, and `lake -R -Koracle=on update DSLean` puts it back.
- The files of `CASOracle` are ordinary Lean files, not modules, because DSLean’s are, so a `module` can’t import them.
- The tools are needed only when a command that names one is elaborated. SymPy, PARI and FLINT run in the Python of `SYMLEAN_SYMPY_PYTHON`, `SYMLEAN_PARI_PYTHON` or `SYMLEAN_FLINT_PYTHON`, else `SYMLEAN_ORACLE_PYTHON`, else `python3`, with `sympy` (and `cvxpy` for sums of squares), `cypari2` or `python-flint`. SageMath, Maxima and Gappa are the programs of `SYMLEAN_SAGE_PATH`, `SYMLEAN_MAXIMA_PATH` and `SYMLEAN_GAPPA_PATH`.
- The deadline of one run is the option [[options|`cas.oracle.timeout`]], in milliseconds, two minutes by default.

### Built on DSLean

We built `CASOracle` on [DSLean](https://github.com/taterowney/DSLean), by taterowney and the DSLean contributors, released under CC BY 4.0. Its grammars write each request in the tool’s own language and read the answer back into Lean. That translation is the fiddly part of talking to another system, and I’m grateful we didn’t have to write it ourselves. SymLean requires the port in [Robertboy18/DSLean](https://github.com/Robertboy18/DSLean), branch `leancas`, which updates DSLean to Lean 4.35.0 with the five changes that `NOTICE` lists. No DSLean file is copied into SymLean.

## Examples

### Basic Examples

SymPy factors a polynomial and the identity is proved. That the factors are irreducible is not, and the report says so:

```lean quote=tests/oracle/Oracles.lean
#cas [factor, oracle := sympy] (x ^ 4 + 4)
```

---

In a proof, SymPy finds how the goal follows from the hypotheses. The suggestion is the proof to keep, and it needs no oracle:

```lean quote=tests/oracle/Oracles.lean suggestion
theorem combination_by_sympy (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]
```

---

An antiderivative from SymPy, proved by differentiating it back:

```lean quote=tests/oracle/Oracles.lean
#cas [integrate x, oracle := sympy] (x ^ 2 * sin x)
```

### Scope

Maxima integrates too:

```lean quote=tests/oracle/Oracles.lean
#cas [integrate x, oracle := maxima] (x * exp x)
```

---

A Gröbner basis of the same ideal. That the basis is reduced is a hint:

```lean quote=tests/oracle/Oracles.lean
#cas [groebner x, y, oracle := sympy] [x ^ 2 + y ^ 2 - 5, x * y - 2]
```

---

Solutions, each checked by substitution. That the list is complete is not checked:

```lean quote=tests/oracle/Oracles.lean
#cas [solve x, y, oracle := sympy] (x ^ 2 + y ^ 2 = 5 ∧ x * y = 2)
```

---

A family of solutions of a differential equation, from SageMath:

```lean quote=tests/oracle/Oracles.lean
#cas [dsolve y x, oracle := sage] (y'' + y = 0)
```

---

A closed form of a sum, proved by induction:

```lean quote=tests/oracle/Oracles.lean
#cas [sum k 1 n, oracle := sympy] (1 / (k * (k + 1)))
```

---

Eigenvalues, each within $10^{-6}$:

```lean quote=tests/oracle/Oracles.lean
#cas [eigenvalues, oracle := sympy] !![2, 1, 0; 1, 3, 1; 0, 1, 4]
```

---

Gappa’s bounds on a box, checked by [[cega]]:

```lean quote=tests/oracle/Oracles.lean
#cas [enclose x in [1/3, 2], oracle := gappa] (sqrt x / (1 + x))
```

---

An inequality between polynomials, by a sum of squares. The suggested script checks the identity with `ring` and the signs with `positivity`. The test pins only its start, since the squares come from a numerical solver:

```lean quote=tests/oracle/Oracles.lean suggestion=start
theorem sos_quartic (x y : ℝ) : 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  cas [oracle := sympy]
```

### Options

The numerical modes take `(digits := ‹d›)`, from 1 to 12 and 6 by default. Here a cube root from FLINT:

```lean quote=tests/oracle/Oracles.lean
#cas (digits := 8) [nsolve x, oracle := flint] (x ^ 3 = 2)
```

### Applications

A definite integral, with SymPy’s primitive. The suggestion is a call of [[cas-integrate-primitive|`cas [integrate primitive := F]`]], which needs no oracle, and the theorem uses only the three standard axioms:

```lean quote=tests/oracle/Oracles.lean suggestion
theorem integral_by_oracle : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [oracle := sympy]
```

```lean quote=tests/oracle/Oracles.lean
#print axioms integral_by_oracle
```

---

SageMath finds the combination behind $a^2 + b^2 + c^2 = 0$ over $\mathbb{Q}$:

```lean quote=tests/oracle/Oracles.lean suggestion
theorem combination_by_sage (a b c : ℚ) (h₁ : a + b + c = 0)
    (h₂ : a * b + b * c + c * a = 0) : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
  cas [oracle := sage]
```

### Properties and Relations

The suggested proofs stand on their own. Here the two from above, compiled for this page without any oracle:

```lean
example (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  linear_combination h1 + x * h2
```

```lean
example : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [integrate primitive := fun x => (x - 1) * Real.exp x]
```

---

SymPy’s digits for $\int_0^1 e^{-x^2}\,dx$ are the ones [[nintegrate]] proves without an oracle:

```lean quote=tests/oracle/Oracles.lean
#cas [nintegrate x in [0, 1], oracle := sympy] (exp (-x ^ 2))
```

```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```

### Possible Issues

A nonnegative polynomial need not be a sum of squares. For Motzkin’s polynomial the oracle finds no certificate, and the refusal says nothing about the inequality:

```lean quote=tests/oracle/Oracles.lean
example (x y : ℝ) : 0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  cas [oracle := sympy]
```

---

The premise $x \ne 0$ is not an inequality, so it is not sent, and without it there is no sum with a positive term:

```lean quote=tests/oracle/Oracles.lean
example : ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2 := by
  cas [oracle := sympy]
```

---

A variable printed as `x✝` can’t be written back, so the script as printed doesn’t check. The goal is still proved from the same certificate, and the suggestion is the call itself:

```lean quote=tests/oracle/Oracles.lean
theorem sos_hidden_atom : ∀ x : ℝ, 0 ≤ x ^ 2 + 1 := by
  intro
  cas [oracle := sympy]
```

### Neat Examples

$p = (xy - 1)^2 + x^2$ is positive but takes values below every positive constant, at $x = 1/y$ for large $y$, so no sum of squares plus a constant equals it. A multiplier works, since $(1 + y^2)\,p = 1 + (x - y + xy^2)^2$, and the oracle finds one:

```lean quote=tests/oracle/Oracles.lean suggestion=start
theorem sos_not_attained : ∀ x y : ℝ, 0 < (x * y - 1) ^ 2 + x ^ 2 := by
  cas [oracle := sympy]
```

```lean quote=tests/oracle/Oracles.lean
#print axioms sos_not_attained
```
