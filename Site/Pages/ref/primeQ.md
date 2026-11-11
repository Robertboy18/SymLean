+++
id = "primeQ"
kind = "call"
title = "primeQ"
summary = "Whether a natural number is prime, with a proof of `Nat.Prime n` or its negation, through the optional Hex library."
calls = ["primeQ"]
see_also = ["factorInteger", "moebiusMu", "eulerPhi", "jacobiSymbol", "cas", "hex"]
guide = "number-theory"
tutorials = ["proving"]
imports = ["Mathlib.Tactic.NormNum.Prime"]
+++

::: usage
`#cas (primeQ ‹n›)`
: decides whether the natural number ‹n› is prime and proves `Nat.Prime ‹n›` or `¬ Nat.Prime ‹n›`, with Hex.
:::

`primeQ` tells you whether ‹n› is prime and proves the answer either way. The certificates are the work of Hex, the Lean FRO’s verified computer algebra. Hex finds a certificate that ‹n› is prime, or a factor of ‹n›, and the kernel checks it. A factor you could check yourself by multiplying. A proof of primality is much harder to come by, and that is where Hex does the real work.

Hex is optional, and the build of this site leaves it out. The outputs on this page that need Hex are quoted from `CASHex/Examples.lean`, which the Hex build compiles. To turn Hex on, fetch it with the commands in the [Hex guide](guide:hex), build it with `lake -R -Khex=on build CASHex`, and start your file with `import CASHex.NumberTheory`.

## Details and Options

- ‹n› is a natural number, a literal or a closed integer expression.
- For a prime the theorem is `Nat.Prime n`. Hex’s `primality` gives a Pocklington certificate, which the kernel replays and `Hex.Nat.prime_iff` transports to `Nat.Prime`.
- For a composite $n$ the theorem is `¬ Nat.Prime n`. Hex’s factor search finds a factor $d$, the report prints $n = d \cdot (n / d)$, and `Nat.not_prime_mul` proves the theorem from it. 0 and 1 are not prime by `norm_num`.
- When Hex’s test finds $n$ composite but its factor search finds no factor within its budget, the call refuses and claims nothing.
- With `CASHex.Algebra` imported, bare [[cas]] proves `Nat.Prime n` with the same kind of certificate.
- There are no options. Without Hex the call refuses, and the message says how to turn Hex on.

## Examples

### Basic Examples

The Mersenne prime $2^{61} - 1$, with the theorem that the kernel checked:

```lean quote=CASHex/Examples.lean
#cas (primeQ 2305843009213693951)
```

### Scope

For a composite number the report prints a factorization, here $1000001 = 101 \cdot 9901$, and the theorem is `¬ Nat.Prime 1000001`:

```lean quote=CASHex/Examples.lean
#cas (primeQ 1000001)
```

---

The Mersenne prime $2^{127} - 1$, with 39 digits:

```lean quote=CASHex/Examples.lean
#cas (primeQ 170141183460469231731687303715884105727)
```

### Applications

With `CASHex.Algebra` imported, bare [[cas]] proves `Nat.Prime` in a proof, here after evaluating $2^{61} - 1$:

```lean quote=CASHex/Examples.lean
theorem mersenne_61_prime : Nat.Prime (2 ^ 61 - 1) := by
  cas
```

### Possible Issues

Without Hex the call refuses, and the message says how to turn Hex on:

```lean error
#cas (primeQ 97)
```

---

`primeQ` is a call, not a mode:

```lean error
#cas [primeQ] 97
```

---

For small numbers, Mathlib’s `norm_num` extension `Mathlib.Tactic.NormNum.Prime` proves `Nat.Prime n` without Hex. This page imports it, and bare [[cas]] falls back to `norm_num`:

```lean
example : Nat.Prime 1000003 := by
  cas
```

---

Bare `cas` hands `norm_num` no number above $10^{12}$, since on such a number its decision procedures can run without a bound. Without Hex, a large prime such as $2^{61} - 1$ is refused, and the message says why under `norm_num fallback`:

```lean error
example : Nat.Prime (2 ^ 61 - 1) := by
  cas
```
