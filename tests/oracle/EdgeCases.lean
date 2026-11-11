/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CASOracle.Numeric

/-!
# Edge cases of the numerical searches

Run by `tests/oracle/run.sh`; it needs only SymPy (with mpmath) and python-flint. SymPy's scan of
a transcendental equation reports the points of its grid where the equation holds, the ends of
the interval included even where the value there only rounds to `0`, searches every cell where
the sign changes, by bisection where Anderson's method does not converge, skips the points where
the equation is not real, and a root that an oracle reports several times is certified once. The
roots of a polynomial are compared with the ends of the interval exactly. A root at a rational
point is certified there. An interval needs `a < b`. FLINT finds a repeated or a
defective eigenvalue like a simple one, eigenvalues closer than the tolerance are refused, and a
matrix with no real eigenvalue is reported as such. Each command's headline is checked
with `#guard_msgs` up to the details that follow it, so that a root or an eigenvalue reported
twice fails the check.
-/

set_option linter.hashCommand false
set_option maxHeartbeats 1000000

-- `sin` vanishes at `0`: the left end of the interval, a point of the grid inside it, and the
-- right end.
/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (sin x = 0)

/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 1], oracle := sympy] (sin x = 0)

/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 0], oracle := sympy] (sin x = 0)

-- Roots at both ends.
/--
Output (a root in each interval (existence checked)): -1.000000 ± 10^-6, 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 0], oracle := sympy] (x * sin (x + 1) = 0)

-- `sin (π x)` vanishes at the integers, where its computed value is a rounding residue rather
-- than `0`; at an end of the interval that residue has the sign of the one neighbour.
/--
Output (a root in each interval (existence checked)): -1.000000 ± 10^-6, 0.000000 ± 10^-6, 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 1], oracle := sympy] (sin (π * x) = 0)

/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6, 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (sin (π * x) = 0)

/--
Output (a root in each interval (existence checked)): -1.000000 ± 10^-6, 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 0], oracle := sympy] (sin (π * x) = 0)

-- A root at an end of the interval, or at a rational point inside, is certified at that point,
-- where the equation is proved: `sin π = 0`, `sin (k π) = 0` for an integer `k`, `cos (π / 2) = 0`,
-- `Real.sqrt 0 = 0` and `Real.log 1 = 0`.
/--
Output (a root in each interval (existence checked)): 0.333333 ± 10^-6, 0.666667 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/3, 2/3], oracle := sympy] (sin (3 * π * x) = 0)

/--
Output (a root in each interval (existence checked)): 0.142857 ± 10^-6, 0.285714 ± 10^-6, 0.428571 ± 10^-6, 0.571429 ± 10^-6, 0.714286 ± 10^-6, 0.857143 ± 10^-6, 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/7, 1], oracle := sympy] (sin (7 * π * x) = 0)

/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6, 1.000000 ± 10^-6, 2.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 2], oracle := sympy] (sin (π * x) = 0)

/--
Output (a root in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (cos (π * x / 2) = 0)

/--
Output (a root in each interval (existence checked)): 0.333333 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/3, 1], oracle := sympy] (Real.sqrt (x - 1/3) = 0)

/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 1], oracle := sympy] (Real.sqrt x = 0)

/--
Output (a root in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/2, 2], oracle := sympy] (Real.log x = 0)

-- `π` under `open Real` is Mathlib's notation for `Real.pi`.
open Real in
/--
Output (a root in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/3, 1], oracle := sympy] (sin (π * x) = 0)

-- SymPy's logarithm is complex left of `0`, where Lean's `Real.log x = Real.log |x|` vanishes at
-- `-1`; the refusal says so.
/--
error: nsolve: sympy reports no real root (which proves nothing); sympy evaluates log, sqrt, powers and quotients as complex functions or not at all where Lean's are fixed by convention, as Real.sqrt x = 0 for x < 0, so it can miss such roots
-/
#guard_msgs in
#cas [nsolve x in [-2, -1/2], oracle := sympy] (Real.log x = 0)

-- SymPy's square root is not real left of `0`, where the scan skips its points.
/--
Output (a root in each interval (existence checked)): 0.250000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [-1, 1], oracle := sympy] (Real.sqrt x - 1 / 2 = 0)

-- An interval needs two different ends.
/-- error: nsolve needs rational limits a < b -/
#guard_msgs in
#cas [nsolve x in [0, 0], oracle := sympy] (sin x = 0)

-- SymPy reports the triple root three times.
/--
Output (a root in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x, oracle := sympy] ((x - 1) ^ 3 = 0)

-- The roots `1/3` and `1/7` of these polynomials are ends of the intervals, and their rounded
-- values lie just below them: the oracles compare the roots with the ends exactly, and each is
-- certified at the end.
/--
Output (a root in each interval (existence checked)): 0.333333 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/3, 1], oracle := sympy] (x - 1/3 = 0)

/--
Output (a root in each interval (existence checked)): 0.142857 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/7, 1], oracle := sympy] (x - 1/7 = 0)

/--
Output (a root in each interval (existence checked)): 0.333333 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1/3, 1], oracle := flint] (x - 1/3 = 0)

-- A triple root between two points of SymPy's grid, `10^-4` from the end, where Anderson's method
-- does not converge and bisection finds it.
/--
Output (a root in each interval (existence checked)): 0.999900 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (sin (x - 9999/10000) ^ 3 = 0)

/--
Output (a root in each interval (existence checked)): 0.999900 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 2], oracle := sympy] (sin (x - 9999/10000) ^ 3 = 0)

-- Both ends round to zero here, and the root `0.9998` lies in the last cell of the grid, which is
-- searched as well; the ends, where the value is not zero, are refused.
/--
Output (a root in each interval (existence checked)): 0.999800 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (sin (x - 9998/10000) / 10 ^ 20 = 0)

-- `cos (π x) = 1` at both ends of `[0, 2]`, the right one by `Real.cos_eq_one_iff`, and
-- `sin (π x) = -1` at `3/2`, by `Real.sin_eq_neg_one_iff`.
open Real in
/--
Output (a root in each interval (existence checked)): 0.000000 ± 10^-6, 2.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 2], oracle := sympy] (cos (π * x) = 1)

open Real in
/--
Output (a root in each interval (existence checked)): 1.500000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [1, 2], oracle := sympy] (sin (π * x) = -1)

-- No root, and no caveat about conventions: the variable is inside no quotient, the constant
-- `1/3` aside.
/-- error: nsolve: sympy reports no real root (which proves nothing) -/
#guard_msgs in
#cas [nsolve x in [0, 1/4], oracle := sympy] (x = 1/3)

-- The identity, a repeated eigenvalue on a diagonal, and a Jordan block.
/--
Output (a real eigenvalue in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := flint] !![1, 0; 0, 1]

/--
Output (a real eigenvalue in each interval (existence checked)): 2.000000 ± 10^-6, 3.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := flint] !![2, 0, 0; 0, 2, 0; 0, 0, 3]

/--
Output (a real eigenvalue in each interval (existence checked)): 1.000000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := flint] !![1, 1; 0, 1]

-- Two eigenvalues closer than the tolerance share an interval and are refused, and more digits
-- separate them.
/--
error: eigenvalues: no eigenvalue proposed by flint could be certified (refused: [1.000000]); eigenvalues within 10^-6 of each other share an interval, where the sign need not change, and more digits, as in (digits := 8), separate them
-/
#guard_msgs in
#cas [eigenvalues, oracle := flint] !![1, 0; 0, 10000001/10000000]

/--
Output (a real eigenvalue in each interval (existence checked)): 1.00000000 ± 10^-8, 1.00000010 ± 10^-8

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 8) [eigenvalues, oracle := flint] !![1, 0; 0, 10000001/10000000]

-- A rotation has no real eigenvalue, and the oracle proposes none.
/-- error: eigenvalues: flint reports no real eigenvalue (which proves nothing) -/
#guard_msgs in
#cas [eigenvalues, oracle := flint] !![0, 1; -1, 0]
