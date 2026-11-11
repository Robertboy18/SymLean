+++
id = "chineseRemainder"
kind = "mode"
title = "chineseRemainder"
summary = "All solutions of a system of congruences $x \\equiv r_i \\pmod{m_i}$, as one residue modulo the lcm, or a proof that there are none."
forms = ["CAS.Command.casChineseRemainderCommand"]
see_also = ["extendedGCD", "modularInverse", "powerMod", "factorInteger"]
tutorials = ["proving"]
+++

::: usage
`#cas [chineseRemainder] ([‹r₁›, …, ‹rₖ›], [‹m₁›, …, ‹mₖ›])`
: solves the congruences x ≡ ‹rᵢ› (mod ‹mᵢ›) and proves that the printed residue modulo the lcm of the moduli gives all the solutions, or that there are none.
:::

`chineseRemainder` solves simultaneous congruences. You give it the residues first and then the moduli, and the moduli need not be coprime. What I like is that the theorem is the complete answer and not just one solution: the printed $x$ is a solution, and every solution is congruent to $x$ modulo the lcm $M$ of the moduli. When two of the congruences contradict each other, the theorem says that there is no solution, and the report names the two.

## Details and Options

- The argument is a pair of lists of natural numbers, `([r₁, …, rₖ], [m₁, …, mₖ])`, with as many residues as moduli and at least one of each. The entries are literals or closed integer expressions.
- The moduli are positive, and they need not be coprime. A residue may exceed its modulus.
- The theorem is `x < M ∧ ∀ y : ℕ, (∀ p ∈ [(m₁, r₁), …], y ≡ p.2 [MOD p.1]) ↔ y ≡ x [MOD M]` with Mathlib’s `Nat.ModEq`, where $M = \operatorname{lcm}(m_1, \dots, m_k)$. The list in the theorem pairs each modulus with its residue, modulus first. The kernel decides $x < M$, the lcm and the congruences of $x$ (`CAS.NumberTheory.modEq_iff_of_lcm`).
- Two congruences $x \equiv r_i \pmod{m_i}$ and $x \equiv r_j \pmod{m_j}$ have a common solution exactly when $r_i \equiv r_j \pmod{\gcd(m_i, m_j)}$. When a pair fails this test, the theorem is `¬∃ y : ℕ, ∀ p ∈ [(m₁, r₁), …], y ≡ p.2 [MOD p.1]` (`CAS.NumberTheory.not_exists_of_incompatible`), and the report prints the pair.
- The solution comes from merging the congruences one at a time with Bézout coefficients, as [[extendedGCD]] computes them. There are no options.

## Examples

### Basic Examples

The problem of the *Sunzi Suanjing*: a number leaves the remainders 2, 3 and 2 on division by 3, 5 and 7:

```lean
#cas [chineseRemainder] ([2, 3, 2], [3, 5, 7])
```

### Scope

The moduli need not be coprime. These two have the common factor 2, and the solutions repeat modulo $\operatorname{lcm}(4, 6) = 12$:

```lean
#cas [chineseRemainder] ([2, 4], [4, 6])
```

---

When two congruences disagree modulo the gcd of their moduli, there is no solution. Here $x \equiv 1 \pmod{4}$ makes $x$ odd and $x \equiv 2 \pmod{6}$ makes it even:

```lean
#cas [chineseRemainder] ([1, 2], [4, 6])
```

---

A residue may exceed its modulus:

```lean
#cas [chineseRemainder] ([5], [3])
```

---

Large moduli, the two primes $10^9 + 7$ and $10^9 + 9$ of the [[factorInteger]] page:

```lean
#cas [chineseRemainder] ([3, 7], [1000000007, 1000000009])
```

### Applications

A proof can take the printed theorem as a hypothesis and use the equivalence, here for the next solution $128 = 23 + 105$. This proof uses no axioms at all:

```lean
theorem sunzi_next
    (h : 23 < 105 ∧ ∀ y : ℕ, (∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)),
      y ≡ p.2 [MOD p.1]) ↔ y ≡ 23 [MOD 105]) :
    ∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)), 128 ≡ p.2 [MOD p.1] :=
  (h.2 128).2 (by decide)

#print axioms sunzi_next
```

---

To decrypt the RSA cipher 2790 with the key $d = 2753$ for $n = 61 \cdot 53$, I can raise it to the power $d \bmod 60 = 53$ modulo 61 and to $d \bmod 52 = 49$ modulo 53, and put the two residues together into the message 65:

```lean
#cas (powerMod 2790 53 61)
```

```lean
#cas (powerMod 2790 49 53)
```

```lean
#cas [chineseRemainder] ([4, 12], [61, 53])
```

### Properties and Relations

The multiples of 3 that are 1 modulo 11 are the $3 k$ with $k \equiv 3^{-1} \equiv 4 \pmod{11}$, so the solution is $3 \cdot 4 = 12$ modulo 33. [[modularInverse]] gives the inverse:

```lean
#cas [chineseRemainder] ([0, 1], [3, 11])
```

```lean
#cas (modularInverse 3 11)
```

### Possible Issues

Each modulus needs its residue, and the residues come first:

```lean error
#cas [chineseRemainder] ([2, 3], [3, 5, 7])
```

---

The moduli must be positive:

```lean error
#cas [chineseRemainder] ([1], [0])
```

---

The residues are natural numbers, so $-1$ modulo 3 is written 2:

```lean error
#cas [chineseRemainder] ([-1], [3])
```

### Neat Examples

Ibn al-Haytham asked for a number that leaves the remainder 1 on division by 2, 3, 4, 5 and 6, and is divisible by 7:

```lean
#cas [chineseRemainder] ([1, 1, 1, 1, 1, 0], [2, 3, 4, 5, 6, 7])
```
