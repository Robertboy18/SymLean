+++
id = "trust"
kind = "tutorial"
title = "What you trust"
summary = "What the kernel checks, which axioms a proof uses, and what the opt-in fast profile adds."
+++

When I use a tool in a proof, the first thing I want to know is what I’m trusting. For SymLean the answer is short. A result is a Lean proof, and Lean’s kernel checks it. Native evaluation, which also trusts Lean’s compiler, runs only when you explicitly enable it. Whatever a search finds is a proposal, and nothing it returns becomes a fact until the kernel has checked it. The sections below go through each part, with examples you can run.

## Reading the axioms {#axioms}

You can check the first part yourself with `#print axioms`, and that’s where I always start. Here is a bound on a box and a table of thirty-two integer inequalities:

```lean
theorem box_bound (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

theorem finite_rows : ∀ i : Fin 32, (i.val : ℤ) ^ 2 < 1024 := by
  cega

#print axioms box_bound
#print axioms finite_rows
```

Both use only Lean’s standard axioms. The bound went through interval arithmetic and the table through a finite decision procedure, two quite different routes, and the kernel checked both.

## What the kernel checks {#kernel}

Every closing tactic builds a complete proof of the goal. Before it closes the goal, it rejects a proof with holes or unassigned parts, and it checks that the type of the proof is the goal. The kernel then checks the declaration, as it checks every Lean declaration.

The planners, the candidate searches and the decoding of expressions sit outside all this. They decide which proof to build, and the kernel decides whether it is one. That split is why I’m comfortable with fast, unverified search inside SymLean. Every form of `cas` and `cega` closes the goal completely or restores it, and only `cas_nf`, which rewrites, may leave a changed goal.

The kernel routes of `cega` promise one more thing. Their proofs use no axiom beyond `propext`, `Classical.choice` and `Quot.sound` that the goal, the hypotheses or a supplied certificate don’t already use. A proof that does is rejected with the name of the axiom, and the next route is tried.

You can see the same split in a `#cas` report, which keeps the evidence apart from the explanation:

```lean
#cas [roots x] (x ^ 3 - 2 * x - 5 = 0)
```

The certificate lists the proposition that was proved, with exact rational endpoints: one root in an interval of width $10^{-20}$, and every real root inside it. That proposition is what the kernel checked. How the answer was found, meaning the route names and the steps of the planner, is explanation. I find it useful to read, but it proves nothing.

## Native certificates are opt-in {#native}

Large finite checks, such as a long table of inequalities, are slow to reduce in the kernel, and `cega [fast]` can check them by compiled code instead. You trade trust for speed, and the proof says so: it also trusts Lean’s compiler and runtime, and the proof depends on a generated axiom whose name contains `_native.cegaFast.ax`, so `#print axioms` shows it.

Native checking happens only when the option [[options|`cega.nativeCertificates`]] is true, and it is false by default, in SymLean and in every project that depends on it. With the option off, `cega [fast]` is bare `cega` and checks in the kernel:

```lean
theorem fast_without_native (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]

#print axioms fast_without_native
```

With the option on, a larger table is checked by compiled code, and the axioms say so:

```lean expect="_native.cegaFast.ax"
set_option cega.nativeCertificates true in
theorem fast_rows : ∀ i : Fin 64, (i.val : ℤ) ^ 2 < 4096 := by
  cega [fast]

#print axioms fast_rows
```

The table is a new one on purpose. If the kernel has already proved the statement earlier in the file, as it did for `finite_rows`, `cega [fast]` may reuse that kernel proof, and then no native axiom appears.

There are three ways to turn it on:

- `set_option cega.nativeCertificates true in` for one declaration, as above.
- `lake build -R -Kcertificates=fast` for the library itself. It passes the option to every module and builds into `.lake/build-fast`, apart from the kernel build.
- ``require SymLean ... with NameMap.empty.insert `certificates "fast"`` in a project that depends on SymLean.

The profiles are `kernel`, the default, and `fast` with its alias `native`. With `-R`, which makes Lake read its options again, any other value of `certificates` is an error of SymLean’s configuration, and Lake stops before it builds anything.

The option governs only the checks that run while it is set. A failed native attempt restores the proof state before the kernel routes run, so its axioms don’t survive a refusal, and a later kernel request for the same statement never receives a native proof. The analytic routes, exponentials and logarithms among them, check in the kernel in every profile.

## Searches propose, the kernel decides {#search}

Much of a computer algebra system is search, and search is where bugs live. So SymLean runs its searches as ordinary compiled code and treats every answer as a proposal. Here is what that means, area by area:

- **Integration.** The planner proposes an antiderivative. The kernel checks that its derivative equals the integrand on the whole interval, and only then is the fundamental theorem of calculus applied. A wrong proposal fails that check.
- **Cancellation and factoring.** `cancel` finds the common factor by a gcd search, then proves the identity with the cancelled form by `field_simp` and `ring1`, from the hypotheses that the divisors as written are nonzero. Those hypotheses are the conditions of the report. A factorization is a proposal too, and `ring` proves that the product equals the input.
- **Equations.** A Gröbner basis is computed by search and replayed by `linear_combination`, and the real roots of its eliminant are isolated by a certificate that the kernel evaluates.
- **Roots and limits.** The isolating intervals are found in compiled code, and the kernel checks their obligations. The theorem reaches the goal through a proved identity with the goal’s own function, so a misread function fails instead of proving another statement.
- **Hex and the oracles.** The [[hex|Hex routes]] have the kernel check Hex’s certificates, and the [[oracles|oracles]] run external programs whose answers SymLean proves or refuses.

In this example the common factor $x - 1$ is cancelled, and $x - 1 \ne 0$ appears as a hypothesis of the theorem:

```lean
#cas [cancel] ((x ^ 2 - 1) / (x - 1))
```

## What a refusal means {#refusal}

A failed call restores the goal and says what it lacked: a hypothesis, a regularity proof, more precision, a supported expression. Missing side conditions are never added as assumptions, and the statement is never changed.

A refusal proves nothing about the goal either way. An integration search that finds no candidate doesn’t show that no antiderivative exists, and a certificate that doesn’t reduce to `true` is reported in those words, not as a false statement.

Lean’s total functions still apply: $0/0 = 0$, $\log 0 = 0$, and $\exp(\log x) = x$ needs $0 < x$. For a nonzero $x$ of unknown sign the identity is $\exp(\log x) = \lvert x \rvert$, and the tactics prove the statement you wrote, under these meanings:

```lean
example (x : ℝ) (hx : x ≠ 0) : Real.exp (Real.log x) = |x| := by
  cas
```

Last, and this is the one I’d most like you to remember: a result never says more than its statement. A certified bound on a residual is not a bound on an error. It becomes an estimate of the distance to a solution only through a stability theorem that the surrounding proof supplies.

From here, the [documentation](docs:index) has a guide for each area, starting with [Why SymLean](guide:why).
