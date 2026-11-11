+++
id = "fibonacci"
kind = "call"
title = "fibonacci"
summary = "The Fibonacci number $F_n$, with $F_0 = 0$ and $F_1 = 1$, and a theorem about Mathlib’s `Nat.fib`."
calls = ["fibonacci"]
see_also = ["rsolve", "matrixPower", "binomial", "factorial"]
guide = "number-theory"
tutorials = ["proving", "trust"]
+++

::: usage
`#cas (fibonacci ‹n›)`
: gives the Fibonacci number $F_n$ of the natural number ‹n› and proves `Nat.fib ‹n› = ‹F›`.
:::

`fibonacci` uses the convention $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$, and the theorem is about Mathlib’s `Nat.fib`. The interesting part is the cost of the proof. It takes a number of steps that grows with the binary digits of ‹n›, not with ‹n› itself, because Mathlib’s `norm_num` extension uses the doubling formulas.

## Details and Options

- ‹n› is a natural number, a literal or a closed integer expression.
- The theorem is `Nat.fib n = F`. `norm_num` proves it with Mathlib’s extension for `Nat.fib` (`Mathlib.Tactic.NormNum.NatFib`), which uses the doubling formulas of `Nat.fastFib`, so the number of proof steps grows with the number of binary digits of $n$.
- The value has at most 10000 digits, the most that a call computes.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

The twentieth Fibonacci number, with the theorem that the kernel checked:

```lean
#cas (fibonacci 20)
```

### Scope

$F_{100}$, with 21 digits:

```lean
#cas (fibonacci 100)
```

### Applications

In a proof, [[cas]] proves the equation, here without any axioms:

```lean
theorem fib_twenty : Nat.fib 20 = 6765 := by
  cas

#print axioms fib_twenty
```

### Properties and Relations

[[rsolve]] solves the recurrence with the same initial values, and the closed form is Binet’s formula:

```lean
#cas [rsolve a n, a 0 = 0, a 1 = 1] (a (n + 2) = a (n + 1) + a n)
```

---

The powers of the matrix $\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$ hold consecutive Fibonacci numbers. [[matrixPower]] gives the tenth power, with $F_{11} = 89$, $F_{10} = 55$ and $F_9 = 34$:

```lean
#cas [matrixPower 10] !![1, 1; 1, 0]
```

### Possible Issues

Mathlib’s `Nat.fib` is defined on natural numbers, and a negative argument is refused:

```lean error
#cas (fibonacci (-5))
```

---

The value has at most 10000 digits. $F_{47851}$ has 10000 and $F_{47852}$ has 10001:

```lean error
#cas (fibonacci 47852)
```
