# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The programs SymLean's oracles run in Python: SymPy, PARI (cypari2), FLINT (python-flint)
and SageMath.

`CASOracle` runs this file with one call appended, for one request, through DSLean's runner:
`python -c` for SymPy, PARI and FLINT, `sage -c` for Sage. The request's expressions are written
by DSLean from SymLean's checked expressions, in SymPy's source syntax (read here with
`parse_expr`, so `1 / 3` stays a rational) or in PARI/GP's. The answer is printed as lines

    @@ key payload

with expressions in SymPy's `str`, which DSLean reads back; a program that cannot answer prints
`@@ unavailable reason`, `@@ unsupported reason` or `@@ failed reason`. Nothing computed here is
trusted: SymLean proves every answer it accepts, or refuses it. No socket, no server.
"""

import itertools
import sys
from fractions import Fraction
from math import gcd


class Unavailable(Exception):
    """The backend's program or Python package is missing."""


class Unsupported(Exception):
    """The backend gave no answer in the language SymLean checks."""


def _sympy():
    try:
        import sympy
    except ImportError as error:
        raise Unavailable(f"SymPy is not importable by {sys.executable}: {error}")
    return sympy


def _symbols(names):
    sp = _sympy()
    return {name: sp.Symbol(name, real=True) for name in names}


def read(text, names):
    """The SymPy expression of request text written by DSLean, over the variables `names`."""
    symbols = _symbols(names)
    from sympy.parsing.sympy_parser import parse_expr
    return parse_expr(text, local_dict=symbols)


def V(*names):
    """The variables `names` of a request, as SymPy symbols."""
    return [_symbols(names)[name] for name in names]


def out(key, *payload):
    """One answer line."""
    print("@@", key, *[" ".join(str(p).split()) for p in payload])


def _one_line(error):
    return " ".join(str(error).split())[:500]


def run(task):
    """Run one task, turning every failure into an answer line."""
    try:
        task()
    except Unavailable as error:
        print("@@ unavailable", _one_line(error))
    except Unsupported as error:
        print("@@ unsupported", _one_line(error))
    except Exception as error:  # noqa: BLE001 - every failure becomes a refusal in Lean
        print("@@ failed", f"{type(error).__name__}: {_one_line(error)}")
    sys.stdout.flush()


def _decimal(value, digits):
    """A decimal string of a real SymPy/mpmath number with `digits` significant digits."""
    sp = _sympy()
    value = sp.Float(value, digits + 5)
    if abs(sp.im(value)) > 0:
        raise Unsupported("a complex value")
    return sp.Float(sp.re(value), digits + 5).__format__(f".{digits}e")


def _real_value(g, t):
    """The value of the mpmath function `g` at `t` if it is a real number, else `None`: where the
    function is not real or not defined, a grid scan has no value to compare."""
    import mpmath
    try:
        value = g(t)
    except (ArithmeticError, ValueError):
        return None
    if isinstance(value, mpmath.mpc):
        return value.real if value.imag == 0 else None
    return value


def _roots_in(p, roots, digits, lower=None, upper=None):
    """The rounded real roots `roots` of the polynomial `p` (a SymPy `Poly` over QQ) that lie in
    [lower, upper]. An end where `p` vanishes is a root in its own right, compared exactly, since
    rounding can put its value just outside the interval; a rounded root within 10^-digits of it
    is that root."""
    sp = _sympy()
    lo = sp.Rational(lower) if lower is not None else None
    hi = sp.Rational(upper) if upper is not None else None
    ends = [e for e in dict.fromkeys(e for e in (lo, hi) if e is not None) if p.eval(e) == 0]
    tolerance = sp.Rational(1, 10 ** digits)
    kept = [r for r in roots
            if not any(abs(r - e) <= tolerance * max(1, abs(e)) for e in ends)
            and (lo is None or r >= lo) and (hi is None or r <= hi)]
    return sorted(kept + ends)


def _bracketed_root(g, a, b, digits):
    """A root of the mpmath function `g` in [a, b], where its real values at the ends have opposite
    signs: Anderson's method, or bisection to 10^-(digits + 5) where it does not converge, as at a
    root of odd multiplicity above one."""
    import mpmath
    a, b = mpmath.mpf(a), mpmath.mpf(b)
    try:
        r = mpmath.findroot(g, (a, b), solver="anderson")
        if a <= r <= b:
            return r
    except (ArithmeticError, TypeError, ValueError):
        pass
    fa = _real_value(g, a)
    width = mpmath.mpf(10) ** -(digits + 5) * max(1, abs(a), abs(b))
    for _ in range(4 * (digits + 15) + 200):
        if b - a <= width:
            break
        m = (a + b) / 2
        fm = _real_value(g, m)
        if fm is None or fm == 0:
            return m
        if (fm < 0) == (fa < 0):
            a, fa = m, fm
        else:
            b = m
    return (a + b) / 2


def _polynomial(expr, variables):
    sp = _sympy()
    try:
        return sp.Poly(expr, *variables, domain="QQ")
    except Exception as error:
        raise Unsupported(f"not a polynomial with rational coefficients: {error}")


def _rat_text(text):
    """A rational as `p/q` text, through `Fraction`, so that no request string reaches a program
    that reads formulas."""
    q = Fraction(text)
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


# ---------------------------------------------------------------------------------------------
# Cofactor-tracking Buchberger over QQ, for SymPy (which returns bases without cofactors).

def _tracked_groebner(generators, variables):
    """A Gröbner basis `G` of the ideal of `generators` in lex order with cofactors:
    `G[i] = sum(C[i][j] * generators[j])`. Untrusted: SymLean checks the cofactors."""
    sp = _sympy()
    zero = sp.Poly(0, *variables, domain="QQ")
    one = sp.Poly(1, *variables, domain="QQ")
    m = len(generators)
    basis = []
    for j, g in enumerate(generators):
        if not g.is_zero:
            basis.append((g, [one if k == j else zero for k in range(m)]))

    def reduce(f, cof):
        changed = True
        while changed and not f.is_zero:
            changed = False
            for g, gcof in basis:
                lm_f = f.LM(order="lex")
                lm_g = g.LM(order="lex")
                if all(a >= b for a, b in zip(lm_f.exponents, lm_g.exponents)):
                    mono = sp.Poly(sp.Mul(*[v ** (a - b) for v, a, b in
                                            zip(variables, lm_f.exponents, lm_g.exponents)]),
                                   *variables, domain="QQ")
                    c = f.LC(order="lex") / g.LC(order="lex")
                    f = f - g * mono * c
                    cof = [a - b * mono * c for a, b in zip(cof, gcof)]
                    changed = True
                    break
        return f, cof

    pairs = [(i, j) for i in range(len(basis)) for j in range(i)]
    while pairs:
        i, j = pairs.pop()
        (f, fc), (g, gc) = basis[i], basis[j]
        lf, lg = f.LM(order="lex").exponents, g.LM(order="lex").exponents
        lcm = [max(a, b) for a, b in zip(lf, lg)]
        mf = sp.Poly(sp.Mul(*[v ** (c - a) for v, c, a in zip(variables, lcm, lf)]),
                     *variables, domain="QQ")
        mg = sp.Poly(sp.Mul(*[v ** (c - b) for v, c, b in zip(variables, lcm, lg)]),
                     *variables, domain="QQ")
        s = f * mf * (1 / f.LC(order="lex")) - g * mg * (1 / g.LC(order="lex"))
        sc = [a * mf * (1 / f.LC(order="lex")) - b * mg * (1 / g.LC(order="lex"))
              for a, b in zip(fc, gc)]
        r, rc = reduce(s, sc)
        if not r.is_zero:
            basis.append((r, rc))
            k = len(basis) - 1
            pairs.extend((k, t) for t in range(k))
    # Reduce to the reduced basis of SymPy, keeping cofactors.
    target = sp.groebner([g.as_expr() for g in generators], *variables, order="lex")
    result = []
    for t in target.polys:
        t = sp.Poly(t, *variables, domain="QQ")
        # t is in the ideal; express it through the tracked basis by division.
        r, cof = _divide_tracked(t, basis, variables, m)
        if not r.is_zero:
            raise Unsupported("internal: a basis element did not reduce to zero")
        result.append((t, cof))
    return result


def _divide_tracked(f, basis, variables, m):
    """Divide `f` by the tracked basis; return the remainder and cofactors of `f - remainder`
    in the original generators."""
    sp = _sympy()
    zero = sp.Poly(0, *variables, domain="QQ")
    cof = [zero for _ in range(m)]
    remainder = zero
    while not f.is_zero:
        lm = f.LM(order="lex").exponents
        lc = f.LC(order="lex")
        for g, gcof in basis:
            lg = g.LM(order="lex").exponents
            if all(a >= b for a, b in zip(lm, lg)):
                mono = sp.Poly(sp.Mul(*[v ** (a - b) for v, a, b in zip(variables, lm, lg)]),
                               *variables, domain="QQ")
                c = lc / g.LC(order="lex")
                f = f - g * mono * c
                cof = [a + b * mono * c for a, b in zip(cof, gcof)]
                break
        else:
            term = sp.Poly(lc * sp.Mul(*[v ** a for v, a in zip(variables, lm)]),
                           *variables, domain="QQ")
            remainder = remainder + term
            f = f - term
    return remainder, cof


def _membership_cofactors(target, generators, variables, max_power):
    """Cofactors `c` with `target ** k = sum(c[j] * generators[j])` for the least `k` up to
    `max_power`, or `Unsupported`."""
    tracked = _tracked_groebner(generators, variables)
    for k in range(1, max_power + 1):
        r, cof = _divide_tracked(target ** k, tracked, variables, len(generators))
        if r.is_zero:
            return k, cof
    raise Unsupported(f"the target is not in the ideal (tried powers up to {max_power})")


def _row(values):
    """A row of expressions as one payload: `;` never occurs in SymPy's `str`."""
    return " ; ".join(str(v) for v in values)


# ---------------------------------------------------------------------------------------------
# Sums of squares. A Gram matrix is found numerically by cvxpy and rounded to exact rationals
# (Peyrl and Parrilo): rounding over a ladder of denominators, the exact least-norm projection
# onto the linear constraints, and an exact LDL^T factorization, with facial reduction when the
# numerical matrix is singular. Polynomials are dicts from exponent tuples to Fractions. For a
# strict inequality, 1 x 1 blocks carry the positive terms (a constant, products of strict
# hypotheses), and when that search fails, a multiplier of degree at most 2, then at most 4, is
# tried.

SOS_MAX_BASIS = 40
SOS_MAX_BLOCKS = 64
SOS_MAX_POSITIVE = 32
SOS_MULTIPLIER_DEGREES = (2, 4)
SOS_DENOMINATORS = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 64, 100, 128, 256, 1000, 1024, 10 ** 4,
                    2 ** 16, 10 ** 6, 2 ** 24, 10 ** 8]


def _sos_add(p, q, c=Fraction(1)):
    """p + c * q."""
    r = dict(p)
    for m, v in q.items():
        s = r.get(m, Fraction(0)) + c * v
        if s == 0:
            r.pop(m, None)
        else:
            r[m] = s
    return r


def _sos_mul(p, q):
    r = {}
    for m1, a in p.items():
        for m2, b in q.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            s = r.get(m, Fraction(0)) + a * b
            if s == 0:
                r.pop(m, None)
            else:
                r[m] = s
    return r


def _sos_degree(p):
    return max((sum(m) for m in p), default=0)


def _sos_poly(expr, variables):
    """The dict polynomial of a SymPy expression with rational coefficients."""
    P = _polynomial(expr, variables)
    return {tuple(m): Fraction(int(c.p), int(c.q)) for m, c in P.terms() if c != 0}


def _sos_expr(p, variables):
    sp = _sympy()
    return sp.Add(*[sp.Rational(c.numerator, c.denominator) *
                    sp.Mul(*[v ** e for v, e in zip(variables, m)]) for m, c in p.items()])


def _sos_order(m):
    return (sum(m), m)


def _sos_monomials(n, lo, hi):
    """The monomials of degree lo to hi, highest degree first."""
    found = set()
    for d in range(lo, hi + 1):
        for c in itertools.combinations_with_replacement(range(n), d):
            e = [0] * n
            for i in c:
                e[i] += 1
            found.add(tuple(e))
    return sorted(found, key=_sos_order, reverse=True)


def _sos_in_hull(points, target):
    """Whether `target` is a convex combination of `points`, by a linear program."""
    import numpy as np
    from scipy.optimize import linprog
    pts = np.array(points, dtype=float).T
    k = pts.shape[1]
    A_eq = np.vstack([pts, np.ones((1, k))])
    b_eq = np.concatenate([np.array(target, dtype=float), [1.0]])
    result = linprog(np.zeros(k), A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * k, method="highs")
    return result.status == 0


def _sos_newton_basis(p, n):
    """The monomials whose squares lie in the Newton polytope of p."""
    support = list(p)
    lo = min(sum(m) for m in support)
    hi = max(sum(m) for m in support)
    candidates = _sos_monomials(n, (lo + 1) // 2, hi // 2)
    return [m for m in candidates if _sos_in_hull(support, tuple(2 * x for x in m))]


def _sos_constraints(blocks, target, normal=()):
    """The linear system on the Gram entries `(block j, i, k)`: for each monomial, its
    coefficient in sum_j sum_{i,k} Q_j[i,k] w_i w_k g_j equals that of the target; and the traces
    of the blocks `normal`, if any, add up to 1."""
    columns = []
    contributions = {}
    for j, (basis, g) in enumerate(blocks):
        size = len(basis)
        for i in range(size):
            for k in range(size):
                column = len(columns)
                columns.append((j, i, k))
                for m, c in _sos_mul(_sos_mul(basis[i], basis[k]), g).items():
                    contributions.setdefault(m, {})[column] = c
    alphas = sorted(set(contributions) | set(target), reverse=True)
    rows = [contributions.get(a, {}) for a in alphas]
    rhs = [target.get(a, Fraction(0)) for a in alphas]
    if normal:
        rows.append({column: Fraction(1) for column, (j, i, k) in enumerate(columns)
                     if j in normal and i == k})
        rhs.append(Fraction(1))
    return columns, rows, rhs


def _sos_solve(blocks, target, normal=()):
    """Gram matrices maximizing their smallest eigenvalue t (at most 1), and t."""
    import cvxpy as cp
    import numpy as np
    columns, rows, rhs = _sos_constraints(blocks, target, normal)
    Qs = [cp.Variable((len(b), len(b)), symmetric=True) for b, _ in blocks]
    t = cp.Variable()
    flat = [Qs[j][i, k] for (j, i, k) in columns]
    constraints = []
    for row, b in zip(rows, rhs):
        if not row:
            if b != 0:
                raise Unsupported("a term of the polynomial is out of reach of the squares of "
                                  "the monomial basis")
            continue
        constraints.append(sum(float(c) * flat[column] for column, c in row.items()) == float(b))
    for Q in Qs:
        constraints.append(Q - t * np.eye(Q.shape[0]) >> 0)
    constraints.append(t <= 1)
    problem = cp.Problem(cp.Maximize(t), constraints)
    installed = cp.installed_solvers()
    reasons = []
    for solver in ("CLARABEL", "SCS"):
        if solver not in installed:
            continue
        try:
            problem.solve(solver=solver)
        except Exception as error:  # noqa: BLE001 - the next solver may succeed
            reasons.append(f"{solver}: {_one_line(error)}")
            continue
        if problem.status in ("optimal", "optimal_inaccurate") and t.value is not None:
            return [np.array(Q.value) for Q in Qs], float(t.value)
        reasons.append(f"{solver}: {problem.status}")
    raise Unsupported(f"the Gram problem has no numerical solution "
                      f"({'; '.join(reasons) or 'neither CLARABEL nor SCS is installed'})")


def _sos_solve_exact(M, r):
    """A solution of M y = r over the rationals, free variables 0, or None."""
    n = len(M)
    A = [M[i][:] + [r[i]] for i in range(n)]
    m = len(A[0]) - 1 if A else 0
    pivots = []
    row = 0
    for col in range(m):
        pivot = next((i for i in range(row, n) if A[i][col] != 0), None)
        if pivot is None:
            continue
        A[row], A[pivot] = A[pivot], A[row]
        inverse = 1 / A[row][col]
        A[row] = [v * inverse for v in A[row]]
        for i in range(n):
            if i != row and A[i][col] != 0:
                f = A[i][col]
                A[i] = [a - f * b for a, b in zip(A[i], A[row])]
        pivots.append(col)
        row += 1
        if row == n:
            break
    for i in range(row, n):
        if A[i][m] != 0:
            return None
    y = [Fraction(0)] * m
    for i, col in enumerate(pivots):
        y[col] = A[i][m]
    return y


def _sos_project(rows, rhs, x):
    """The least-norm correction of x onto the solutions of the linear system, exactly."""
    residual = [b - sum(c * x[col] for col, c in row.items()) for row, b in zip(rows, rhs)]
    if all(v == 0 for v in residual):
        return x
    if any(residual[i] != 0 for i in range(len(rows)) if not rows[i]):
        return None
    index = [i for i, row in enumerate(rows) if row]
    M = [[sum(c * rows[b].get(col, 0) for col, c in rows[a].items()) for b in index]
         for a in index]
    y = _sos_solve_exact(M, [residual[i] for i in index])
    if y is None:
        return None
    x = list(x)
    for yi, i in zip(y, index):
        if yi != 0:
            for col, c in rows[i].items():
                x[col] += c * yi
    return x


def _sos_ldl(Q):
    """L and D with Q = sum_k D[k] l_k l_k^T, l_k the k-th column of L, or None if Q is not
    positive semidefinite."""
    n = len(Q)
    A = [row[:] for row in Q]
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for k in range(n):
        d = A[k][k]
        if d < 0:
            return None
        if d == 0:
            if any(A[i][k] != 0 for i in range(k + 1, n)):
                return None
            continue
        D[k] = d
        L[k][k] = Fraction(1)
        for i in range(k + 1, n):
            L[i][k] = A[i][k] / d
        for i in range(k + 1, n):
            if L[i][k] != 0:
                for j in range(k + 1, n):
                    A[i][j] -= L[i][k] * A[k][j]
    return L, D


def _sos_round(blocks, target, numeric, normal=(), accept=None):
    """Exact terms `[(d, l)]` for each block from the numerical Gram matrices, or None; with
    `accept`, the first rounding whose terms it accepts."""
    columns, rows, rhs = _sos_constraints(blocks, target, normal)
    position = {c: n for n, c in enumerate(columns)}
    sizes = [len(b) for b, _ in blocks]
    for denominator in SOS_DENOMINATORS:
        x = [Fraction(float(numeric[j][i, k])).limit_denominator(denominator)
             for (j, i, k) in columns]
        for n, (j, i, k) in enumerate(columns):
            if i > k:
                x[n] = x[position[(j, k, i)]]
        x = _sos_project(rows, rhs, x)
        if x is None:
            continue
        matrices = [[[Fraction(0)] * s for _ in range(s)] for s in sizes]
        for v, (j, i, k) in zip(x, columns):
            matrices[j][i][k] = v
        if any(matrices[j][i][k] != matrices[j][k][i] for j in range(len(sizes))
               for i in range(sizes[j]) for k in range(sizes[j])):
            continue
        factors = [_sos_ldl(Q) for Q in matrices]
        if any(f is None for f in factors):
            continue
        result = []
        for (basis, _), (L, D) in zip(blocks, factors):
            terms = []
            for k, d in enumerate(D):
                if d == 0:
                    continue
                ell = {}
                for i in range(len(basis)):
                    if L[i][k] != 0:
                        ell = _sos_add(ell, basis[i], L[i][k])
                if ell:
                    terms.append((d, ell))
            result.append(terms)
        if accept is None or accept(result):
            return result
    return None


def _sos_rational_kernel(Q, tol=1e-6):
    """A rational basis, in reduced row echelon form, of the numerical kernel of Q."""
    import numpy as np
    w, v = np.linalg.eigh(Q)
    scale = max(1.0, float(np.max(np.abs(w))))
    kernel = v[:, w < tol * scale]
    if kernel.shape[1] == 0:
        return []
    K = kernel.T.copy()
    rows, cols = K.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        pivot = r + int(np.argmax(np.abs(K[r:, c])))
        if abs(K[pivot, c]) < 1e-6:
            continue
        K[[r, pivot]] = K[[pivot, r]]
        K[r] /= K[r, c]
        for i in range(rows):
            if i != r:
                K[i] -= K[i, c] * K[r]
        r += 1
    return [[Fraction(float(a)).limit_denominator(1000) for a in K[i]] for i in range(r)]


def _sos_kernel_fits(Q, K, tol=1e-5):
    """Whether the rounded kernel vectors annihilate the numerical Gram matrix to the tolerance
    `tol`."""
    import numpy as np
    scale = max(1.0, float(np.max(np.abs(Q))))
    for row in K:
        v = np.array([float(a) for a in row])
        if np.linalg.norm(Q @ v) > tol * scale * max(1.0, np.linalg.norm(v)):
            return False
    return True


def _sos_nullspace(K, n):
    """Vectors spanning {v : K v = 0}, exactly."""
    if not K:
        return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    A = [row[:] for row in K]
    pivots = []
    r = 0
    for c in range(n):
        pivot = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inverse = 1 / A[r][c]
        A[r] = [x * inverse for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
    vectors = []
    for f in (c for c in range(n) if c not in pivots):
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for i, c in enumerate(pivots):
            v[c] = -A[i][f]
        vectors.append(v)
    return vectors


def _sos_reduce_block(basis, K):
    """The block basis V^T w, for V spanning the nullspace of K."""
    reduced = []
    for v in _sos_nullspace(K, len(basis)):
        q = {}
        for c, b in zip(v, basis):
            if c != 0:
                q = _sos_add(q, b, c)
        reduced.append(q)
    return reduced


def _sos_primitive(ell):
    """`(c, l / c)` where `l / c` has coprime integer coefficients and a positive leading
    coefficient."""
    coefficients = [ell[m] for m in sorted(ell, key=_sos_order, reverse=True)]
    lcm = 1
    for c in coefficients:
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    common = 0
    for c in coefficients:
        common = gcd(common, int(c * lcm))
    content = Fraction(common, lcm)
    if coefficients[0] < 0:
        content = -content
    return content, {m: c / content for m, c in ell.items()}


def _sos_search(blocks, target, required=(), normal=(), max_reductions=3):
    """Exact terms `[(d, l)]` with d > 0 for each block `(basis, g)`, none for a block that
    facial reduction emptied, such that the sum over the blocks of d * l^2 * g is the target.
    Each `(group, reason)` of `required` asks for a term in one of the blocks `group`, and the
    search is refused with `reason` once they have all vanished; the 1 x 1 blocks `normal` have
    entries adding up to 1."""
    blocks = list(blocks)
    for _ in range(max_reductions + 1):
        for group, reason in required:
            if not any(blocks[j][0] for j in group):
                raise Unsupported(reason)
        live = [j for j, (basis, _) in enumerate(blocks) if basis]
        position = {j: i for i, j in enumerate(live)}
        live_normal = [position[j] for j in normal if j in position]
        live_required = [[position[j] for j in group if j in position] for group, _ in required]

        def acceptable(found):
            return all(any(found[i] for i in group) for group in live_required)

        numeric, t = _sos_solve([blocks[j] for j in live], target, live_normal)
        if t < -1e-6:
            raise Unsupported(f"the solver found no positive semidefinite Gram matrix (best "
                              f"smallest eigenvalue {t:.3g})")
        found = _sos_round([blocks[j] for j in live], target, numeric, live_normal, acceptable)
        if found is not None:
            result = [[] for _ in blocks]
            for j, terms in zip(live, found):
                result[j] = terms
            return result
        if t > 1e-7:
            raise Unsupported(f"none of the attempted roundings of the numerical Gram matrix "
                              f"(smallest eigenvalue {t:.3g}) gave an acceptable exact "
                              "certificate")
        changed = False
        for j, Q in zip(live, numeric):
            K = _sos_rational_kernel(Q)
            if K and not _sos_kernel_fits(Q, K):
                raise Unsupported("the numerical Gram matrix is singular, and no rational kernel "
                                  "was recovered within tolerance")
            if K:
                blocks[j] = (_sos_reduce_block(blocks[j][0], K), blocks[j][1])
                changed = True
        if not changed:
            break
    raise Unsupported("no exact sum-of-squares certificate found")


def _sos_terms(found, labels):
    """The terms `(label, d, l)` of the blocks' terms, with `l` primitive with integer
    coefficients; terms with the same label and `l` are merged."""
    merged = {}
    for label, terms in zip(labels, found):
        for d, ell in terms:
            content, primitive = _sos_primitive(ell)
            key = (label, frozenset(primitive.items()))
            weight, _ = merged.get(key, (Fraction(0), primitive))
            merged[key] = (weight + d * content * content, primitive)
    return [(label, d, ell) for (label, _), (d, ell) in merged.items()]


def _sos_total(terms, hypotheses, n):
    """The sum of the terms `(J, d, l)`: d * l^2 * prod_{j in J} hypotheses[j]."""
    total = {}
    for J, d, ell in terms:
        g = {tuple([0] * n): Fraction(1)}
        for j in J:
            g = _sos_mul(g, hypotheses[j])
        total = _sos_add(total, _sos_mul(_sos_mul(ell, ell), g), d)
    return total


def _sos_products(hypotheses, strict, top, limit=SOS_MAX_POSITIVE):
    """The multisets of the strict hypotheses of positive degree whose product has degree at most
    `top`, as nondecreasing tuples of indices: the empty one first, then by size, at most
    `limit`."""
    usable = sorted(j for j in set(strict)
                    if 0 <= j < len(hypotheses) and _sos_degree(hypotheses[j]) > 0)
    found = [()]
    frontier = [((), 0)]
    while frontier and len(found) < limit:
        following = []
        for alpha, degree in frontier:
            for j in usable:
                if alpha and j < alpha[-1]:
                    continue
                if degree + _sos_degree(hypotheses[j]) <= top:
                    following.append((alpha + (j,), degree + _sos_degree(hypotheses[j])))
        found.extend(alpha for alpha, _ in following)
        frontier = following
    return found[:limit]


def _sos_positive(target, hypotheses, strict, n, multiplier_degree, max_reductions):
    """The certificate of `_sos_strict_certificate` with a multiplier of degree at most
    `multiplier_degree`, or none for 0."""
    one = {tuple([0] * n): Fraction(1)}
    top = _sos_degree(target) + multiplier_degree

    def product(indices):
        g = one
        for j in indices:
            g = _sos_mul(g, hypotheses[j])
        return g

    def monomials(k):
        return [{m: Fraction(1)} for m in _sos_monomials(n, 0, k)]

    subsets = [s for size in range(len(hypotheses) + 1)
               for s in itertools.combinations(range(len(hypotheses)), size)]
    # With a multiplier s the identity is s * target - (squares) - (positive terms) = 0.
    sign = Fraction(-1) if multiplier_degree else Fraction(1)
    blocks, labels, kinds = [], [], []
    for K in subsets if multiplier_degree else []:
        g = product(K)
        if g and _sos_degree(g) <= multiplier_degree and len(blocks) < SOS_MAX_BLOCKS:
            blocks.append((monomials((multiplier_degree - _sos_degree(g)) // 2),
                           _sos_mul(target, g)))
            labels.append(K)
            kinds.append("multiplier")
    for J in subsets:
        g = product(J)
        if not g or _sos_degree(g) > top or len(blocks) == SOS_MAX_BLOCKS:
            continue
        if not hypotheses and not multiplier_degree:
            # The Newton polytope of target - c.
            basis = [{m: Fraction(1)} for m in _sos_newton_basis({**target, **one}, n)]
        else:
            basis = monomials((top - _sos_degree(g)) // 2)
        if basis:
            blocks.append((basis, _sos_add({}, g, sign)))
            labels.append(J)
            kinds.append("square")
    for alpha in _sos_products(hypotheses, strict, top):
        blocks.append(([one], _sos_add({}, product(alpha), sign)))
        labels.append(alpha)
        kinds.append("positive")
    if any(len(b) > SOS_MAX_BASIS for b, _ in blocks):
        raise Unsupported(f"the Gram matrix would have more than {SOS_MAX_BASIS} rows")
    positive = [j for j, kind in enumerate(kinds) if kind == "positive"]
    required = [(positive, "the positive terms vanish in the best numerical solution")]
    if multiplier_degree:
        required.append(([j for j, kind in enumerate(kinds) if kind == "multiplier"],
                         "the multiplier vanishes in the best numerical solution"))
    found = _sos_search(blocks, {} if multiplier_degree else target, required,
                        positive if multiplier_degree else (), max_reductions)
    multiplier = _sos_terms([f if kind == "multiplier" else [] for f, kind in zip(found, kinds)],
                            labels)
    terms = _sos_terms([f if kind != "multiplier" else [] for f, kind in zip(found, kinds)],
                       labels)
    s = _sos_total(multiplier, hypotheses, n) if multiplier_degree else one
    if _sos_mul(s, target) != _sos_total(terms, hypotheses, n):
        raise Unsupported("internal: the rounded certificate does not add up")
    return multiplier, terms


def _sos_strict_certificate(target, hypotheses, strict, n, max_reductions=3):
    """`(multiplier, terms)`, lists of `(J, d, l)` standing for d * l^2 * prod_{j in J}
    hypotheses[j], such that s * target is the sum of the terms exactly, s being the sum of the
    multiplier's terms (1 if there are none). Every d is positive and every l primitive with
    integer coefficients, and some term has l = 1 and J (a multiset) within `strict`, the
    hypotheses that stand for 0 < g. So the sum is positive where 0 <= g for every hypothesis
    and 0 < g for the strict ones, and target is positive there too, as s >= 0."""
    if not target:
        raise Unsupported("the polynomial is zero")
    if not hypotheses and _sos_degree(target) % 2 == 1:
        raise Unsupported("the degree is odd, and a sum of squares has even degree")
    reasons = []
    for multiplier_degree in (0,) + SOS_MULTIPLIER_DEGREES:
        try:
            return _sos_positive(target, hypotheses, strict, n, multiplier_degree,
                                 max_reductions)
        except Unsupported as error:
            reasons.append(str(error))
    attempts = "; ".join(f"with a multiplier of degree at most {k}: {reason}"
                         for k, reason in zip(SOS_MULTIPLIER_DEGREES, reasons[1:]))
    raise Unsupported(f"no sum of squares with a positive term: {reasons[0]}; {attempts}")


def _sos_certificate(target, hypotheses, n, max_reductions=3):
    """Terms `(J, d, l)` with target = sum d * l^2 * prod_{j in J} hypotheses[j] exactly, d > 0
    and l primitive with integer coefficients."""
    if not target:
        raise Unsupported("the polynomial is zero")
    degree = _sos_degree(target)
    if not hypotheses and degree % 2 == 1:
        raise Unsupported("the degree is odd, and a sum of squares has even degree")
    one = {tuple([0] * n): Fraction(1)}
    blocks = []
    labels = []
    if not hypotheses:
        basis = _sos_newton_basis(target, n)
        if not basis:
            raise Unsupported("no monomial has its square in the Newton polytope")
        blocks.append(([{m: Fraction(1)} for m in basis], one))
        labels.append(())
    else:
        blocks.append(([{m: Fraction(1)} for m in _sos_monomials(n, 0, degree // 2)], one))
        labels.append(())
        subsets = (s for size in range(1, len(hypotheses) + 1)
                   for s in itertools.combinations(range(len(hypotheses)), size))
        for subset in subsets:
            if len(blocks) == SOS_MAX_BLOCKS:
                break
            g = one
            for j in subset:
                g = _sos_mul(g, hypotheses[j])
            if not g or _sos_degree(g) > degree:
                continue
            k = (degree - _sos_degree(g)) // 2
            blocks.append(([{m: Fraction(1)} for m in _sos_monomials(n, 0, k)], g))
            labels.append(subset)
    if any(len(b) > SOS_MAX_BASIS for b, _ in blocks):
        raise Unsupported(f"the Gram matrix would have more than {SOS_MAX_BASIS} rows")
    certificate = _sos_terms(_sos_search(blocks, target, max_reductions=max_reductions), labels)
    if _sos_total(certificate, hypotheses, n) != target:
        raise Unsupported("internal: the rounded certificate does not add up")
    return certificate


# ---------------------------------------------------------------------------------------------
# SymPy.

class SympyBackend:
    def __init__(self):
        self.sp = _sympy()

    def integrate(self, f, x):
        result = self.sp.integrate(f, x)
        if result.has(self.sp.Integral):
            raise Unsupported("SymPy left the integral unevaluated")
        out("antiderivative", result)

    def factor(self, f, variables):
        sp = self.sp
        constant, factors = sp.factor_list(sp.together(f), *variables)
        out("constant", sp.Rational(constant))
        for g, m in factors:
            out("factor", int(m), g)

    def solve(self, equations, variables):
        sp = self.sp
        for solution in sp.solve(equations, variables, dict=True):
            if set(solution) != set(variables):
                raise Unsupported("SymPy returned a parametric solution")
            out("solution", _row(sp.radsimp(solution[v]) for v in variables))

    def nroots(self, f, x, digits, lower=None, upper=None):
        sp = self.sp
        import mpmath
        lo = sp.Rational(lower) if lower is not None else None
        hi = sp.Rational(upper) if upper is not None else None
        roots = []
        if f.is_polynomial(x):
            # SymPy's real roots are exact, so each is compared with the ends exactly.
            for r in _polynomial(f, [x]).real_roots():
                if (lo is None or r >= lo) and (hi is None or r <= hi):
                    roots.append(sp.N(r, digits + 5))
        else:
            if lo is None or hi is None:
                raise Unsupported("a non-polynomial equation needs an interval [lower, upper]")
            mpmath.mp.dps = digits + 10
            g = sp.lambdify(x, f, "mpmath")
            n = 2000
            grid = sorted({lo + (hi - lo) * sp.Rational(i, n) for i in range(n + 1)})
            values = [_real_value(g, mpmath.mpf(sp.N(t, digits + 10))) for t in grid]
            # Each point of the grid where f vanishes is a root, and each sign change between two
            # neighbours brackets one. At an end, a value below the working precision counts as a
            # zero, since a root there rounds to such a residue of either sign; inside, a residue
            # still shows up as a sign change. The bracket next to such an end is searched as
            # well, and its root is that of the end when it lies within 10^-digits of it. A point
            # where f is not real is skipped.
            tolerance = mpmath.mpf(10) ** -(digits + 5)
            near = mpmath.mpf(10) ** -digits
            last = len(grid) - 1

            def vanishes(i):
                return values[i] is not None and (
                    values[i] == 0 or (i in (0, last) and abs(values[i]) <= tolerance))

            for i, (a, fa) in enumerate(zip(grid, values)):
                if fa is None:
                    continue
                if vanishes(i):
                    roots.append(sp.Float(sp.N(a, digits + 5), digits + 5))
                if i < last and values[i + 1] is not None and fa * values[i + 1] < 0:
                    left = mpmath.mpf(sp.N(a, digits + 10))
                    right = mpmath.mpf(sp.N(grid[i + 1], digits + 10))
                    r = _bracketed_root(g, left, right, digits)
                    if not ((vanishes(i) and abs(r - left) <= near) or
                            (vanishes(i + 1) and abs(r - right) <= near)):
                        roots.append(sp.Float(r, digits + 5))
        for r in roots:
            out("root", _decimal(r, digits))

    def nintegrate(self, f, x, lower, upper, digits):
        sp = self.sp
        value = sp.Integral(f, (x, sp.Rational(lower), sp.Rational(upper))).evalf(digits + 5)
        out("value", _decimal(value, digits))

    def eigenvalues(self, rows, digits):
        sp = self.sp
        matrix = sp.Matrix([[sp.Rational(a) for a in row] for row in rows])
        t = sp.Symbol("t")
        p = sp.Poly(matrix.charpoly(t).as_expr(), t)
        for r in p.real_roots():
            out("eigenvalue", _decimal(sp.N(r, digits + 5), digits))

    def groebner(self, polys, variables):
        sp = self.sp
        generators = [_polynomial(p, variables) for p in polys]
        tracked = _tracked_groebner(generators, variables)
        basis = [g for g, _ in tracked]
        for g, cof in tracked:
            out("basis", g.as_expr())
            out("to_basis", _row(c.as_expr() for c in cof))
        for f in generators:
            r, cof = _divide_tracked(f, [(g, [sp.Poly(1 if k == i else 0, *variables,
                                                      domain="QQ")
                                              for k in range(len(basis))])
                                         for i, g in enumerate(basis)],
                                     variables, len(basis))
            if not r.is_zero:
                raise Unsupported("internal: a generator did not reduce to zero")
            out("from_basis", _row(c.as_expr() for c in cof))

    def member(self, target, generators, variables, max_power):
        if not generators:
            raise Unsupported("no hypotheses to combine")
        target = _polynomial(target, variables)
        generators = [_polynomial(p, variables) for p in generators]
        k, cof = _membership_cofactors(target, generators, variables, max_power)
        out("power", k)
        out("cofactors", _row(c.as_expr() for c in cof))

    def sos(self, target, hypotheses, variables, strict=None):
        """A certificate of 0 <= target, each hypothesis g standing for 0 <= g, or, with
        `strict` the indices of the hypotheses that stand for 0 < g, of 0 < target. Its terms
        d * l^2 * prod_{j in J} hypotheses[j] are printed as `square d ; l` for J empty and
        `multiplied J ; d ; l` otherwise, J written as indices separated by spaces. They add up
        to target, or for 0 < target to s * target, one of them being d * prod_{j in J}
        hypotheses[j] with J strict (repeats allowed); s is the sum of the terms printed as
        `multiplier_square d ; l` and `multiplier_multiplied J ; d ; l`, or 1 if there are
        none."""
        try:
            import cvxpy  # noqa: F401
            import scipy  # noqa: F401
        except ImportError:
            raise Unavailable(f"cvxpy is not importable by {sys.executable}: pip install cvxpy")
        p = _sos_poly(target, variables)
        gs = [_sos_poly(g, variables) for g in hypotheses]
        if strict is None:
            multiplier, terms = [], _sos_certificate(p, gs, len(variables))
        else:
            multiplier, terms = _sos_strict_certificate(p, gs, list(strict), len(variables))
        for prefix, found in (("multiplier_", multiplier), ("", terms)):
            for J, d, ell in found:
                if J:
                    out(prefix + "multiplied",
                        _row([" ".join(str(j) for j in J), d, _sos_expr(ell, variables)]))
                else:
                    out(prefix + "square", _row([d, _sos_expr(ell, variables)]))

    def dsolve(self, equation, x, derivatives):
        """`derivatives[k]` is the symbol standing for the `k`-th derivative of the unknown."""
        sp = self.sp
        y = sp.Function("y")
        order = len(derivatives) - 1
        lhs = equation.subs({d: sp.diff(y(x), x, k) if k else y(x)
                             for k, d in enumerate(derivatives)})
        solution = sp.dsolve(sp.Eq(lhs, 0), y(x))
        if isinstance(solution, list):
            raise Unsupported("SymPy returned several solution families")
        if not (isinstance(solution, sp.Eq) and solution.lhs == y(x)):
            raise Unsupported("SymPy returned an implicit solution")
        rhs = solution.rhs
        constants = sorted((s for s in rhs.free_symbols if s.name.startswith("C")),
                           key=lambda s: s.name)
        if len(constants) > order:
            raise Unsupported("more constants than the order")
        renamed = {c: sp.Symbol(f"C{i + 1}", real=True) for i, c in enumerate(constants)}
        out("constants", len(renamed))
        out("solution", rhs.subs(renamed))

    def sum(self, f, k, lower, n):
        sp = self.sp
        index = sp.Symbol(k.name, integer=True, nonnegative=True)
        upper = sp.Symbol(n.name, integer=True, nonnegative=True)
        result = sp.simplify(sp.summation(f.subs(k, index), (index, sp.Integer(lower), upper)))
        if result.has(sp.Sum):
            raise Unsupported("SymPy left the sum unevaluated")
        out("closed_form", result.subs(upper, n))


# ---------------------------------------------------------------------------------------------
# PARI/GP through cypari2. Formulas reach PARI in GP syntax, written by DSLean.

class PariBackend:
    def __init__(self):
        try:
            import cypari2
        except ImportError as error:
            raise Unavailable(f"cypari2 is not importable by {sys.executable}: {error}")
        self.pari = cypari2.Pari()
        self.sp = _sympy()

    def _real(self, value):
        return self.sp.Float(str(value).replace(" E", "e"), 50)

    def factor(self, f, gp, x):
        """`f` is the polynomial in SymPy, `gp` the same in GP over the variable `x`."""
        sp = self.sp
        p = self.pari(gp)
        if p.type() != "t_POL":
            raise Unsupported("not a polynomial")
        matrix = self.pari.factor(p)
        product = sp.Integer(1)
        factors = []
        for i in range(self.pari.matsize(matrix)[0]):
            # The coefficients, lowest degree first, read as rationals: no formula is parsed.
            coefficients = [Fraction(str(c)) for c in matrix[i, 0].Vecrev()]
            g = sp.Add(*[sp.Rational(c.numerator, c.denominator) * x ** k
                         for k, c in enumerate(coefficients)])
            m = int(matrix[i, 1])
            factors.append((sp.expand(g), m))
            product *= g ** m
        constant = sp.simplify(f / product)
        if not constant.is_Rational:
            raise Unsupported("PARI's factors do not account for the input")
        out("constant", constant)
        for g, m in factors:
            out("factor", m, g)

    def nroots(self, gp, digits, lower=None, upper=None):
        self.pari.set_real_precision(digits + 10)
        p = self.pari(gp)
        if p.type() != "t_POL":
            raise Unsupported("PARI's real roots are for polynomials")
        x = self.sp.Symbol("x")
        coefficients = [Fraction(str(c)) for c in p.Vecrev()]
        exact = self.sp.Poly(sum((self.sp.Rational(c.numerator, c.denominator) * x ** k
                                  for k, c in enumerate(coefficients)), self.sp.Integer(0)), x,
                             domain="QQ")
        roots = [self._real(r) for r in self.pari.polrootsreal(p)]
        for r in _roots_in(exact, roots, digits, lower, upper):
            out("root", _decimal(r, digits))

    def nintegrate(self, gp, x, lower, upper, digits):
        self.pari.set_real_precision(digits + 10)
        value = self.pari(f"intnum({x} = {_rat_text(lower)}, {_rat_text(upper)}, {gp})")
        out("value", _decimal(self._real(value), digits))

    def eigenvalues(self, rows, digits):
        self.pari.set_real_precision(digits + 10)
        matrix = ";".join(",".join(_rat_text(a) for a in row) for row in rows)
        for r in self.pari(f"polrootsreal(charpoly([{matrix}]))"):
            out("eigenvalue", _decimal(self._real(r), digits))


# ---------------------------------------------------------------------------------------------
# FLINT through python-flint.

def eval_acb(expr, env, flint):
    """Evaluate a SymPy expression in FLINT's complex ball arithmetic, the symbols given by
    `env`."""
    sp = _sympy()
    rec = lambda a: eval_acb(a, env, flint)
    if expr.is_Rational:
        return flint.acb(flint.arb(flint.fmpq(int(expr.p), int(expr.q))))
    if expr.is_Symbol:
        return env[expr]
    if expr is sp.pi:
        return flint.acb.pi()
    if expr is sp.E:
        return flint.acb(1).exp()
    if expr.is_Add:
        total = flint.acb(0)
        for a in expr.args:
            total += rec(a)
        return total
    if expr.is_Mul:
        total = flint.acb(1)
        for a in expr.args:
            total *= rec(a)
        return total
    if expr.is_Pow:
        base, exponent = expr.args
        if exponent.is_Integer:
            return rec(base) ** int(exponent)
        return rec(base) ** rec(exponent)
    unary = {sp.sin: "sin", sp.cos: "cos", sp.tan: "tan", sp.atan: "atan", sp.asin: "asin",
             sp.acos: "acos", sp.exp: "exp", sp.log: "log", sp.sinh: "sinh", sp.cosh: "cosh",
             sp.tanh: "tanh"}
    if expr.func in unary:
        return getattr(rec(expr.args[0]), unary[expr.func])()
    if expr.func is sp.Abs:
        return flint.acb(abs(rec(expr.args[0])))
    raise Unsupported(f"FLINT cannot evaluate {expr.func.__name__}")


class FlintBackend:
    def __init__(self):
        try:
            import flint
        except ImportError as error:
            raise Unavailable(f"python-flint is not importable by {sys.executable}: {error}")
        self.flint = flint
        self.sp = _sympy()

    def factor(self, f, variables):
        sp, flint = self.sp, self.flint
        p = _polynomial(sp.together(f), variables)
        ctx = flint.fmpq_mpoly_ctx.get(tuple(v.name for v in variables), "lex")
        poly = ctx.from_dict({tuple(m): flint.fmpq(int(c.p), int(c.q)) for m, c in p.terms()})
        constant, factors = poly.factor()
        out("constant", sp.Rational(int(constant.p), int(constant.q)))
        for g, m in factors:
            expr = sp.Add(*[sp.Rational(int(c.p), int(c.q)) *
                            sp.Mul(*[v ** e for v, e in zip(variables, mono)])
                            for mono, c in g.to_dict().items()])
            out("factor", int(m), expr)

    def _real_roots(self, poly, digits):
        """The distinct real roots of the `fmpq_poly` `poly`, increasing. Arb isolates the roots
        of its square-free factors, so a multiple root is found like a simple one, and it gives
        a real root an imaginary part of exactly zero and a non-real one a ball away from zero."""
        sp = self.sp
        roots = []
        for root, _ in poly.complex_roots():
            if root.imag.is_zero():
                roots.append(sp.Float(root.real.mid().str(digits + 5, radius=False), digits + 5))
        return sorted(roots)

    def nroots(self, f, x, digits, lower=None, upper=None):
        sp, flint = self.sp, self.flint
        p = _polynomial(f, [x])
        coefficients = [flint.fmpq(int(c.p), int(c.q)) for c in reversed(p.all_coeffs())]
        flint.ctx.dps = digits + 10
        roots = self._real_roots(flint.fmpq_poly(coefficients), digits)
        for r in _roots_in(p, roots, digits, lower, upper):
            out("root", _decimal(r, digits))

    def nintegrate(self, f, x, lower, upper, digits):
        sp, flint = self.sp, self.flint
        flint.ctx.dps = digits + 10

        def integrand(t, _analytic):
            return eval_acb(f, {x: t}, flint)

        a, b = Fraction(lower), Fraction(upper)
        value = flint.acb.integral(integrand, flint.acb(flint.arb(flint.fmpq(a.numerator,
                                                                             a.denominator))),
                                   flint.acb(flint.arb(flint.fmpq(b.numerator, b.denominator))))
        out("value", _decimal(sp.Float(value.real.mid().str(digits + 5, radius=False),
                                       digits + 5), digits))

    def eigenvalues(self, rows, digits):
        """The real roots of the characteristic polynomial, which FLINT computes exactly over
        the rationals. A repeated or defective eigenvalue is found like a simple one, which
        `acb_mat.eig` cannot do: it fails to isolate the eigenvalues of diag(2, 2, 3) even with
        `multiple=True`."""
        flint = self.flint
        flint.ctx.dps = digits + 10
        matrix = flint.fmpq_mat([[flint.fmpq(Fraction(a).numerator, Fraction(a).denominator)
                                  for a in row] for row in rows])
        for v in self._real_roots(matrix.charpoly(), digits):
            out("eigenvalue", _decimal(v, digits))


# ---------------------------------------------------------------------------------------------
# SageMath, run as `sage -c`, so `sage.all` is importable here; no notebook, no server. Requests
# are read with SymPy and converted with `_sage_()`; answers are converted back with
# `_sympy_()`, so that they are printed in SymPy's syntax.

class SageBackend:
    def __init__(self):
        try:
            import sage.all as sage
        except ImportError as error:
            raise Unavailable(f"this program is not running inside Sage: {error}")
        self.sage = sage
        self.sp = _sympy()

    def _sr(self, expr):
        return self.sage.SR(expr._sage_())

    def _back(self, value):
        return self.sp.sympify(value._sympy_())

    def _ring(self, variables):
        return self.sage.PolynomialRing(self.sage.QQ, [v.name for v in variables], order="lex")

    def _poly(self, ring, expr):
        return ring(str(self.sp.expand(expr)).replace("**", "^"))

    def _poly_expr(self, p, variables):
        # The terms of the polynomial, read as exponent vectors and rationals.
        sp = self.sp
        terms = []
        for exponents, c in p.dict().items():
            if isinstance(exponents, int):
                exponents = (exponents,)
            terms.append(sp.Rational(int(c.numerator()), int(c.denominator())) *
                         sp.Mul(*[v ** int(e) for v, e in zip(variables, exponents)]))
        return sp.Add(*terms)

    def integrate(self, f, x):
        result = self.sage.integrate(self._sr(f), self.sage.SR.var(x.name, domain="real"))
        if "integrate" in str(result):
            raise Unsupported("Sage left the integral unevaluated")
        out("antiderivative", self._back(result))

    def factor(self, f, variables):
        ring = self._ring(variables)
        factorization = self._poly(ring, f).factor()
        out("constant", factorization.unit())
        for g, m in factorization:
            out("factor", int(m), self._poly_expr(g, variables))

    def solve(self, equations, variables):
        sage = self.sage
        unknowns = [sage.SR.var(v.name, domain="real") for v in variables]
        solutions = sage.solve([self._sr(e) == 0 for e in equations], unknowns,
                               solution_dict=True)
        for solution in solutions:
            values = [solution.get(u) for u in unknowns]
            if any(v is None or v.is_real() is False or "I" in str(v) for v in values):
                continue
            out("solution", _row(self._back(v) for v in values))

    def groebner(self, polys, variables):
        ring = self._ring(variables)
        generators = [self._poly(ring, p) for p in polys]
        ideal = ring.ideal(generators)
        basis = list(ideal.groebner_basis())
        for g in basis:
            out("basis", self._poly_expr(g, variables))
            out("to_basis", _row(self._poly_expr(c, variables) for c in g.lift(ideal)))
        basis_ideal = ring.ideal(basis)
        for f in generators:
            out("from_basis", _row(self._poly_expr(c, variables) for c in f.lift(basis_ideal)))

    def member(self, target, generators, variables, max_power):
        ring = self._ring(variables)
        ideal = ring.ideal([self._poly(ring, p) for p in generators])
        target = self._poly(ring, target)
        for k in range(1, max_power + 1):
            if target ** k in ideal:
                out("power", k)
                out("cofactors", _row(self._poly_expr(c, variables)
                                      for c in (target ** k).lift(ideal)))
                return
        raise Unsupported("the target is not in the ideal")

    def nintegrate(self, f, x, lower, upper, digits):
        sage = self.sage
        bits = int((digits + 10) * 3.33)
        value = sage.integral(self._sr(f), sage.SR.var(x.name, domain="real"), sage.QQ(lower),
                              sage.QQ(upper))
        value = sage.RealField(bits)(value.n(bits))
        out("value", _decimal(self.sp.Float(str(value), digits + 5), digits))

    def dsolve(self, equation, x, derivatives):
        sage = self.sage
        xs = sage.SR.var(x.name, domain="real")
        y = sage.function("y")(xs)
        lhs = self._sr(equation).subs({sage.SR.var(d.name): (sage.diff(y, xs, k) if k else y)
                                       for k, d in enumerate(derivatives)})
        solution = sage.desolve(lhs == 0, y, ivar=xs)
        renamed = {}
        index = 1
        for name in ("_C", "_K1", "_K2"):
            if name in str(solution):
                renamed[sage.SR.var(name)] = sage.SR.var(f"C{index}", domain="real")
                index += 1
        out("constants", index - 1)
        out("solution", self._back(solution.subs(renamed)))

    def sum(self, f, k, lower, n):
        sage = self.sage
        index = sage.SR.var(k.name, domain="integer")
        upper = sage.SR.var(n.name, domain="integer")
        result = sage.sum(self._sr(f), index, sage.ZZ(lower), upper).full_simplify()
        if "sum" in str(result):
            raise Unsupported("Sage left the sum unevaluated")
        out("closed_form", self._back(result))

    def eigenvalues(self, rows, digits):
        sage = self.sage
        matrix = sage.matrix(sage.QQ, [[sage.QQ(a) for a in row] for row in rows])
        field = sage.RealField(int((digits + 10) * 3.33))
        for r in matrix.charpoly().roots(ring=field, multiplicities=False):
            out("eigenvalue", _decimal(self.sp.Float(str(r), digits + 5), digits))

