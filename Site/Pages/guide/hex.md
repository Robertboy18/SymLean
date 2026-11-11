+++
id = "hex"
kind = "guide"
title = "Hex"
summary = "The optional routes through Hex: irreducibility, determinants and primes in `cas`, factors over the rationals with every one certified, and primality."
related_guides = ["polynomials", "number-theory", "linear-algebra", "oracles"]
tutorials = ["trust"]
+++

[Hex](https://github.com/leanprover/hex) is the Lean FRO’s verified computer algebra: dense polynomials over `ℤ`, `ℚ` and `ZMod p`, factoring with irreducibility certificates, determinants, primality and real roots. It works the way SymLean does, running its searches in compiled code and having the kernel check a certificate. And it is strong exactly where the core of SymLean is weak, in exact algebra over the integers and finite fields, so I’d much rather use Hex there than write a second version of the same algorithms.

We’re in touch with the Hex team about how the two projects fit together.

SymLean uses Hex through the optional library `CASHex`, and if you don’t ask for it, nothing changes: Lake neither fetches nor builds Hex, and no module of `CAS` imports it. To turn it on with Hex v0.10.0, run these from the root of SymLean:

```
lake -R -Khex=on update HexBerlekampZassenhausTheory HexBareissTheory HexPrimalityTheory
git -C .lake/packages/HexLLL apply ../../../CASHex/patches/hex-lll-gnu-source.patch
lake -R -Khex=on build CASHex
```

The first command fetches the Berlekamp-Zassenhaus factorizer, the Bareiss determinants and the primality certificates with their dependencies, 34 Hex packages in all, and writes them into `lake-manifest.json`. The second is for glibc systems that declare `RTLD_DEFAULT` only under `_GNU_SOURCE`. To switch back, run `lake -R build`, and `git checkout lake-manifest.json` restores the manifest.

::: table
Module | What it adds
`CASHex.Algebra` | the Hex route of bare [[cas]]: irreducibility, determinants and primality
`CASHex.Factor` | irreducible factors over `ℚ` for [[factor]], and the factorizer over `ℚ` of [[apart]], [[product]], [[rsolve]], [[dsolve]], [[inverseLaplace]], [[eigenvalues]], [[eigenvectors]] and rational [[integrate|integration]]
`CASHex.LinearAlgebra` | the Hex determinant of [[det]]
`CASHex.NumberTheory` | [[primeQ]], [[moebiusMu]] and [[factorInteger]], and [[eulerPhi]] from the factorization
:::

::: commands
### In proofs
- cas
### Factoring over the rationals
- factor
- apart
- product
- eigenvalues
- eigenvectors
### Numbers and matrices
- primeQ
- moebiusMu
- factorInteger
- eulerPhi
- det
### Settings
- options
:::

The examples below are quoted from `CASHex/Examples.lean`, which the Hex build compiles, and each one is checked by `#guard_msgs` or by its theorem. With `import CASHex.Algebra`, bare `cas` proves that the AES polynomial is irreducible over `ZMod 2`, by a Rabin certificate that the kernel checks:

```lean quote=CASHex/Examples.lean
theorem irreducible_aes : Irreducible (X ^ 8 + X ^ 4 + X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  cas
```

The proof uses only the three standard axioms:

```lean quote=CASHex/Examples.lean
#print axioms irreducible_aes
```

Factoring shows the difference best. Without Hex, [[factor|`#cas [factor]`]] splits off rational roots, perfect powers and homogeneous factors, so it leaves $x^4 + 4$ whole, although $x^4 + 4$ does factor over $\mathbb{Q}$. With `import CASHex.Factor`, the factors come with their irreducibility over $\mathbb{Q}$, proved in the kernel, whenever Hex certifies every one of them:

```lean quote=CASHex/Examples.lean
#cas [factor] (x ^ 4 + 4)
```

Primes work the same way. A prime is proved by Hex’s Pocklington certificate, which the kernel replays. This one is $2^{61} - 1$:

```lean quote=CASHex/Examples.lean
#cas (primeQ 2305843009213693951)
```

These routes are kernel-only, because an optional library shouldn’t be where the trusted base grows. A proof that uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound` that the goal and its hypotheses don’t already use is rejected, and so is a proof with a hole. Hex’s search runs under the budget [[options|`cas.hexHeartbeats`]], and setting it to `0` turns the route off.
