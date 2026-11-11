# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Tests of the Python programs alone: the computations Lean does not check step by step, and
the answer lines. Every task runs end to end, through Lean, in tests/oracle/Oracles.lean, the
edge cases of the numerical searches in tests/oracle/EdgeCases.lean, and the trust boundary is
tested in tests/oracle/Refusals.lean. Run with
`python3 -m pytest -q -p no:cacheprovider oracle`.
"""

import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))
import symlean_oracle as oracle  # noqa: E402


def answer_lines(capsys, task):
    oracle.run(task)
    return capsys.readouterr().out.splitlines()


def test_read_keeps_rationals():
    sp = pytest.importorskip("sympy")
    (v0,) = oracle.V("v0")
    assert oracle.read("( ( 1 / 3 ) * ( v0 ** 2 ) )", ["v0"]) == sp.Rational(1, 3) * v0 ** 2


def test_tracked_groebner_cofactors():
    sp = pytest.importorskip("sympy")
    x, y = oracle.V("v0", "v1")
    generators = [sp.Poly(x ** 2 + y ** 2 - 5, x, y, domain="QQ"),
                  sp.Poly(x * y - 2, x, y, domain="QQ")]
    for g, cofactors in oracle._tracked_groebner(generators, [x, y]):
        assert sp.expand(g.as_expr() - sum(c.as_expr() * f.as_expr()
                                           for c, f in zip(cofactors, generators))) == 0


def test_membership_cofactors():
    sp = pytest.importorskip("sympy")
    x, y = oracle.V("v0", "v1")
    target = sp.Poly(x ** 2 - 1, x, y, domain="QQ")
    generators = [sp.Poly(x * y - 1, x, y, domain="QQ"), sp.Poly(x - y, x, y, domain="QQ")]
    k, cofactors = oracle._membership_cofactors(target, generators, [x, y], 4)
    assert sp.expand((target ** k).as_expr() - sum(c.as_expr() * g.as_expr()
                                                  for c, g in zip(cofactors, generators))) == 0


def test_membership_refuses_a_non_member():
    sp = pytest.importorskip("sympy")
    x, y = oracle.V("v0", "v1")
    with pytest.raises(oracle.Unsupported):
        oracle._membership_cofactors(sp.Poly(x, x, y, domain="QQ"),
                                     [sp.Poly(y, x, y, domain="QQ")], [x, y], 2)


def test_answer_lines(capsys):
    pytest.importorskip("sympy")
    (v0,) = oracle.V("v0")
    assert answer_lines(capsys, lambda: oracle.SympyBackend().integrate(
        oracle.read("sin( v0 )", ["v0"]), v0)) == ["@@ antiderivative -cos(v0)"]
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().integrate(
        oracle.read("exp( v0 ** v0 )", ["v0"]), v0))
    assert lines == ["@@ unsupported SymPy left the integral unevaluated"]
    lines = answer_lines(capsys, lambda: 1 / 0)
    assert lines == ["@@ failed ZeroDivisionError: division by zero"]


def test_flint_ball_evaluation():
    flint = pytest.importorskip("flint")
    (v0,) = oracle.V("v0")
    expr = oracle.read("( exp( v0 ) - ( ( v0 ** 2 ) / 2 ) )", ["v0"])
    value = oracle.eval_acb(expr, {v0: flint.acb(1)}, flint)
    assert abs(Fraction(value.real.mid().str(20, radius=False)) - Fraction("2.2182818284590452")) \
        < Fraction(1, 10 ** 15)


def payload_values(lines, key):
    """The numbers of the answer lines `@@ key value`, as fractions."""
    assert all(line.startswith(f"@@ {key} ") for line in lines), lines
    return [Fraction(line.split()[2]) for line in lines]


def sympy_roots(capsys, text, lower, upper):
    pytest.importorskip("sympy")
    (v0,) = oracle.V("v0")
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().nroots(
        oracle.read(text, ["v0"]), v0, 10, lower, upper))
    return payload_values(lines, "root")


def test_sympy_roots_at_points_of_the_grid(capsys):
    # sin vanishes exactly at 0: the left end of [0, 1], a point of the grid inside [-1, 1] and
    # the right end of [-1, 0]. Each is reported once.
    assert sympy_roots(capsys, "sin( v0 )", "0", "1") == [0]
    assert sympy_roots(capsys, "sin( v0 )", "-1", "1") == [0]
    assert sympy_roots(capsys, "sin( v0 )", "-1", "0") == [0]
    # Both ends of [-1, 0].
    assert sympy_roots(capsys, "( v0 * sin( ( v0 + 1 ) ) )", "-1", "0") == [-1, 0]
    # A sign change between two points of the grid.
    (root,) = sympy_roots(capsys, "( cos( v0 ) - v0 )", "0", "1")
    assert abs(root - Fraction("0.7390851332")) < Fraction(1, 10 ** 9)


def test_sympy_roots_at_inexact_ends(capsys):
    # sin(pi x) vanishes at the integers, but its value there is a rounding residue, of either
    # sign. An end counts once, even where the residue differs in sign from its neighbour.
    sine = "sin( ( pi * v0 ) )"
    assert sympy_roots(capsys, sine, "-1", "1") == [-1, 0, 1]
    assert sympy_roots(capsys, sine, "0", "1") == [0, 1]
    assert sympy_roots(capsys, sine, "-1", "0") == [-1, 0]
    assert sympy_roots(capsys, sine, "1/2", "1") == [1]
    thirds = sympy_roots(capsys, "sin( ( 3 * ( pi * v0 ) ) )", "1/3", "1")
    assert len(thirds) == 3
    assert all(abs(r - t) < Fraction(1, 10 ** 9) for r, t in
               zip(thirds, [Fraction(1, 3), Fraction(2, 3), 1]))
    # A positive function that is flat near 0 has no root, inside or at the ends.
    assert sympy_roots(capsys, "exp( ( -1 / ( ( v0 ** 2 ) + 1/10000 ) ) )", "-1", "1") == []


def test_sympy_roots_on_awkward_intervals(capsys):
    # A one-point interval is one point of the grid.
    assert sympy_roots(capsys, "sin( v0 )", "0", "0") == [0]
    # Points where the function is not real, or not defined, are skipped.
    assert sympy_roots(capsys, "( sqrt( v0 ) - 1/2 )", "-1", "1") == [Fraction(1, 4)]
    assert sympy_roots(capsys, "( 1 / v0 )", "-1", "1") == []


def close_to(found, expected):
    """Whether the roots `found` are within 10^-9 of the rationals `expected`, in order."""
    return len(found) == len(expected) and \
        all(abs(r - Fraction(e)) < Fraction(1, 10 ** 9) for r, e in zip(found, expected))


def flint_roots(capsys, text, lower, upper):
    pytest.importorskip("flint")
    (v0,) = oracle.V("v0")
    lines = answer_lines(capsys, lambda: oracle.FlintBackend().nroots(
        oracle.read(text, ["v0"]), v0, 10, lower, upper))
    return payload_values(lines, "root")


def test_polynomial_roots_at_rational_ends(capsys):
    # The roots 1/3 and 1/7 are ends of the intervals, and their rounded values lie below them.
    for roots in (sympy_roots, flint_roots):
        assert close_to(roots(capsys, "( v0 - 1/3 )", "1/3", "1"), ["1/3"])
        assert close_to(roots(capsys, "( v0 - 1/7 )", "1/7", "1"), ["1/7"])
        assert close_to(roots(capsys, "( v0 - 1/3 )", "0", "1/3"), ["1/3"])
        assert roots(capsys, "( v0 - 1/3 )", "0", "1/4") == []
        assert close_to(roots(capsys, "( ( v0 - 1/3 ) * ( v0 - 1/2 ) )", "1/3", "1/2"),
                        ["1/3", "1/2"])


class FakePari:
    """The calls of `PariBackend.nroots` for `x - 1/3`, whose real root PARI rounds to a value just
    below `1/3`; cypari2 itself need not be installed."""

    class Polynomial:
        def type(self):
            return "t_POL"

        def Vecrev(self):
            return ["-1/3", "1"]

    def set_real_precision(self, digits):
        pass

    def __call__(self, gp):
        return self.Polynomial()

    def polrootsreal(self, p):
        return ["0.33333333333333333333"]


def test_pari_polynomial_root_at_a_rational_end(capsys):
    pytest.importorskip("sympy")
    backend = oracle.PariBackend.__new__(oracle.PariBackend)
    backend.pari = FakePari()
    backend.sp = oracle._sympy()
    lines = answer_lines(capsys, lambda: backend.nroots("x - 1/3", 10, "1/3", "1"))
    assert close_to(payload_values(lines, "root"), ["1/3"])
    lines = answer_lines(capsys, lambda: backend.nroots("x - 1/3", 10, "0", "1/4"))
    assert lines == []


def test_sympy_roots_of_odd_multiplicity(capsys):
    # A triple root between two points of the grid, where Anderson's method does not converge
    # and bisection finds it.
    cube = "( sin( ( v0 - 9999/10000 ) ) ** 3 )"
    assert close_to(sympy_roots(capsys, cube, "0", "1"), ["9999/10000"])
    assert close_to(sympy_roots(capsys, cube, "0", "2"), ["9999/10000"])


def test_sympy_roots_next_to_ends_that_round_to_zero(capsys):
    # Both ends round to zero here, and the root 0.9998 lies in the last cell of the grid: the
    # cell is searched, and the ends are reported as well.
    roots = sympy_roots(capsys, "( sin( ( v0 - 9998/10000 ) ) / 10 ** 20 )", "0", "1")
    assert close_to(roots, ["0", "9998/10000", "1"])


def flint_eigenvalues(capsys, rows):
    pytest.importorskip("flint")
    lines = answer_lines(capsys, lambda: oracle.FlintBackend().eigenvalues(rows, 10))
    return payload_values(lines, "eigenvalue")


def test_flint_repeated_eigenvalues(capsys):
    assert flint_eigenvalues(capsys, [[1, 0], [0, 1]]) == [1]
    assert flint_eigenvalues(capsys, [[2, 0, 0], [0, 2, 0], [0, 0, 3]]) == [2, 3]
    # Jordan blocks: one eigenvalue, defective.
    assert flint_eigenvalues(capsys, [[1, 1], [0, 1]]) == [1]
    assert flint_eigenvalues(capsys, [[2, 1], [-1, 4]]) == [3]
    assert flint_eigenvalues(capsys, [[4, 1], [2, 3]]) == [2, 5]
    # A rotation has no real eigenvalue.
    assert flint_eigenvalues(capsys, [[0, 1], [-1, 0]]) == []


def test_flint_real_roots_at_any_precision(capsys):
    flint = pytest.importorskip("flint")
    lines = answer_lines(capsys, lambda: oracle.FlintBackend().eigenvalues([[1]], 648))
    assert payload_values(lines, "eigenvalue") == [1]
    # The roots of x^2 + 10^-40 are not real, though their imaginary parts are tiny.
    roots = oracle.FlintBackend()._real_roots(
        flint.fmpq_poly([flint.fmpq(1, 10 ** 40), 0, 1]), 10)
    assert roots == []


def total(terms, gs, n):
    """The sum of d * l^2 * prod_{j in J} gs[j] over the terms (J, d, l), each d positive and
    each l with integer coefficients."""
    result = {}
    for J, d, ell in terms:
        assert d > 0
        assert all(c.denominator == 1 for c in ell.values())
        g = {tuple([0] * n): Fraction(1)}
        for j in J:
            g = oracle._sos_mul(g, gs[j])
        result = oracle._sos_add(result, oracle._sos_mul(oracle._sos_mul(ell, ell), g), d)
    return result


def sos_terms(text, hypotheses, names):
    """The certificate of the polynomial `text` under the hypotheses `0 <= g`, with the exact
    check that its terms add up to the polynomial."""
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    variables = oracle.V(*names)
    p = oracle._sos_poly(oracle.read(text, names), variables)
    gs = [oracle._sos_poly(oracle.read(g, names), variables) for g in hypotheses]
    terms = oracle._sos_certificate(p, gs, len(variables))
    assert total(terms, gs, len(names)) == p
    return terms


def test_sos_certificates():
    sos_terms("v0 ** 4 + v1 ** 4 - 4 * v0 * v1 + 2", [], ["v0", "v1"])
    sos_terms("(v0 ** 2 + v1 ** 2) ** 2 - 4 * v0 ** 2 * v1 ** 2", [], ["v0", "v1"])
    terms = sos_terms("v0 ** 3 + v1 ** 3 - v0 ** 2 * v1 - v0 * v1 ** 2", ["v0", "v1"],
                      ["v0", "v1"])
    assert any(J for J, _, _ in terms)


def test_sos_facial_reduction(monkeypatch):
    # (x - 1)^2 (x^2 + 1) vanishes at 1, so its Gram matrix over the monomials 1, x, x^2 is
    # singular, with kernel (1, 1, 1). The first rounding is made to fail: the search then
    # reduces the basis by the kernel and rounds the solution of the smaller problem.
    kernels = []
    reduce_block = oracle._sos_reduce_block

    def reduced(basis, K):
        kernels.append(K)
        return reduce_block(basis, K)

    rounding = oracle._sos_round
    roundings = []

    def failing_once(*args, **kwargs):
        roundings.append(None)
        return None if len(roundings) == 1 else rounding(*args, **kwargs)

    monkeypatch.setattr(oracle, "_sos_reduce_block", reduced)
    monkeypatch.setattr(oracle, "_sos_round", failing_once)
    sos_terms("(v0 - 1) ** 2 * (v0 ** 2 + 1)", [], ["v0"])
    assert kernels == [[[1, 1, 1]]]
    assert len(roundings) == 2


def test_sos_refusals():
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    x, y = oracle.V("v0", "v1")
    motzkin = oracle._sos_poly(x ** 4 * y ** 2 + x ** 2 * y ** 4 - 3 * x ** 2 * y ** 2 + 1,
                               [x, y])
    with pytest.raises(oracle.Unsupported, match="no positive semidefinite Gram matrix"):
        oracle._sos_certificate(motzkin, [], 2)
    with pytest.raises(oracle.Unsupported, match="the degree is odd"):
        oracle._sos_certificate(oracle._sos_poly(x ** 3 + 1, [x, y]), [], 2)


def test_sos_answer_lines(capsys):
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    x, y = oracle.V("v0", "v1")
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().sos(
        oracle.read("(v0 ** 2 - v1 ** 2) ** 2", ["v0", "v1"]), [], [x, y]))
    assert lines == ["@@ square 1 ; v0**2 - v1**2"]
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().sos(
        oracle.read("v0 ** 3", ["v0"]), [oracle.read("v0", ["v0"])], [x]))
    assert lines == ["@@ multiplied 0 ; 1 ; v0"]


def strict_terms(text, hypotheses, strict, names):
    """The certificate of 0 < `text` under the hypotheses `0 <= g`, `0 < g` for the indices
    `strict`, with the exact checks: s * p is the sum of the terms, where s is the sum of the
    multiplier's terms (1 without a multiplier), and one term is a positive constant times
    strict hypotheses."""
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    n = len(names)
    one = {tuple([0] * n): Fraction(1)}
    variables = oracle.V(*names)
    p = oracle._sos_poly(oracle.read(text, names), variables)
    gs = [oracle._sos_poly(oracle.read(g, names), variables) for g in hypotheses]
    multiplier, terms = oracle._sos_strict_certificate(p, gs, strict, n)
    s = total(multiplier, gs, n) if multiplier else one
    assert oracle._sos_mul(s, p) == total(terms, gs, n)
    assert any(ell == one and set(J) <= set(strict) for J, _, ell in terms)
    return multiplier, terms


def test_sos_strict_certificates():
    multiplier, _ = strict_terms("v0 ** 4 - v0 + 1", [], [], ["v0"])
    assert not multiplier
    multiplier, _ = strict_terms("v0 ** 2 + v1 ** 2 + 2 - (v0 * v1 + v0 + v1)", [], [],
                                 ["v0", "v1"])
    assert not multiplier
    multiplier, _ = strict_terms("v0 ** 3 + v0", ["v0"], [0], ["v0"])
    assert not multiplier
    # The positive term of x^3 under 0 < x is x * x * x.
    _, terms = strict_terms("v0 ** 3", ["v0"], [0], ["v0"])
    assert any(J == (0, 0, 0) and ell == {(0,): 1} for J, _, ell in terms)
    # A hypothesis a < b enters as 0 < b - a.
    strict_terms("v0 ** 2 - 1", ["v0 - 1"], [0], ["v0"])


def test_sos_strict_multiplier():
    # Without premises the positive term is a constant, and (x y - 1)^2 + x^2 takes values
    # below every positive constant, so the oracle multiplies it by a sum of squares.
    multiplier, _ = strict_terms("(v0 * v1 - 1) ** 2 + v0 ** 2", [], [], ["v0", "v1"])
    assert multiplier


def test_sos_rounding_passes_over_a_vanished_required_block(monkeypatch):
    np = pytest.importorskip("numpy")
    one = {(0,): Fraction(1)}
    x = {(1,): Fraction(1)}
    # x^2 + 1 as a square over the monomials 1, x and a 1 x 1 block for the positive constant.
    blocks = [([one, x], one), ([one], one)]
    target = {(2,): Fraction(1), (0,): Fraction(1)}
    numeric = [np.array([[0.98, 0.0], [0.0, 1.0]]), np.array([[0.02]])]
    # The first denominators round the 1 x 1 block's 0.02 to 0. That block is required, so the
    # search passes over these roundings, although the first block rounds to the identity over
    # 1, x, whose constant term is positive, and takes the first one that keeps it: 1/32.
    assert oracle._sos_round(blocks, target, numeric)[1] == []
    monkeypatch.setattr(oracle, "_sos_solve", lambda blocks, target, normal=(): (numeric, 0.02))
    found = oracle._sos_search(blocks, target, required=[([1], "lost")])
    assert found[1] == [(Fraction(1, 32), one)]


def test_sos_search_refuses_when_no_rounding_is_acceptable(monkeypatch):
    np = pytest.importorskip("numpy")
    one = {(0,): Fraction(1)}
    x = {(1,): Fraction(1)}
    blocks = [([one, x], one), ([one], one)]
    target = {(2,): Fraction(1), (0,): Fraction(1)}
    # The solver is replaced by a fixed answer whose required 1 x 1 block holds 1e-9, which every
    # denominator up to 10^8 rounds to 0, while the first block rounds to the identity. So every
    # rounding loses the required block, and the margin 0.02 rules out facial reduction.
    numeric = [np.array([[1.0, 0.0], [0.0, 1.0]]), np.array([[1e-9]])]
    monkeypatch.setattr(oracle, "_sos_solve", lambda blocks, target, normal=(): (numeric, 0.02))
    with pytest.raises(oracle.Unsupported) as refusal:
        oracle._sos_search(blocks, target, required=[([1], "lost")])
    assert str(refusal.value) == ("none of the attempted roundings of the numerical Gram matrix "
                                  "(smallest eigenvalue 0.02) gave an acceptable exact "
                                  "certificate")


def test_sos_strict_refusals():
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    x, = oracle.V("v0")
    with pytest.raises(oracle.Unsupported, match="no sum of squares with a positive term"):
        oracle._sos_strict_certificate(oracle._sos_poly(x ** 2, [x]), [], [], 1)
    with pytest.raises(oracle.Unsupported, match="the degree is odd"):
        oracle._sos_strict_certificate(oracle._sos_poly(x ** 3 + 1, [x]), [], [], 1)


def test_sos_strict_answer_lines(capsys):
    pytest.importorskip("sympy")
    pytest.importorskip("cvxpy")
    x, y = oracle.V("v0", "v1")
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().sos(
        oracle.read("v0", ["v0"]), [oracle.read("v0", ["v0"])], [x], strict=[0]))
    assert lines == ["@@ multiplied 0 ; 1 ; 1"]
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().sos(
        oracle.read("v0 ** 2 + 1", ["v0"]), [], [x], strict=[]))
    assert lines == ["@@ square 1 ; v0", "@@ square 1 ; 1"]
    lines = answer_lines(capsys, lambda: oracle.SympyBackend().sos(
        oracle.read("(v0 * v1 - 1) ** 2 + v0 ** 2", ["v0", "v1"]), [], [x, y], strict=[]))
    assert lines[0].startswith("@@ multiplier_square ")
    assert {line.split()[1] for line in lines} <= {"multiplier_square", "square"}
