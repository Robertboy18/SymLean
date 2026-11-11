# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Math for the SymLean site: LaTeX to MathML, and the display syntax of SymLean to LaTeX.

`tex_to_mathml` converts the LaTeX of the page sources with latex2mathml and adjusts the result
for MathML Core, which browsers render without help: operator names become identifiers, symbols
that latex2mathml marks as identifiers become operators, and named functions get the thin space
TeX would put after them. The TeX source is kept in `alttext`.

`cas_to_tex` reads the result line of a `#cas` report, such as `x*atan(x) - 1/2*log(1 + x^2)`,
and writes it in traditional notation, like Mathematica's TraditionalForm. The parser is strict:
anything outside the expression grammar (prose, `if` chains it cannot place, unknown words)
makes it return None, and the page shows the plain form only.
"""

from __future__ import annotations

import html
import re
import unicodedata

import latex2mathml.converter

# ---------------------------------------------------------------------------
# LaTeX to MathML

_FUNCTION_NAMES = (
    "sin cos tan cot sec csc arcsin arccos arctan sinh cosh tanh coth log ln exp lim liminf "
    "limsup max min sup inf det deg gcd lcm erf erfc sgn arg Re Im"
).split()
_FUNCTION_RE = "|".join(sorted(_FUNCTION_NAMES, key=len, reverse=True))
_IDENT_OPERATORS = {"\u221e"}  # latex2mathml writes ∞ as <mo>; it is an identifier


def _entity_char(match: str) -> str:
    """The character of an `&#x....;` entity or the text itself."""
    m = re.fullmatch(r"&#x([0-9A-Fa-f]+);", match)
    return chr(int(m.group(1), 16)) if m else match


def fix_mathml(xml: str) -> str:
    """Adjust latex2mathml output for MathML Core."""
    # Multi-letter operator names (\operatorname, \min) are identifiers in upright type.
    xml = re.sub(r"<mo>([A-Za-z]{2,})</mo>", r"<mi>\1</mi>", xml)

    # Single symbols that latex2mathml leaves as identifiers (\pm, \lfloor) are operators,
    # and ∞ is an identifier.
    def ident_symbol(m: re.Match[str]) -> str:
        ch = _entity_char(m.group(1))
        if len(ch) == 1 and unicodedata.category(ch)[0] in "SP" and ch not in _IDENT_OPERATORS:
            return f"<mo>{m.group(1)}</mo>"
        return m.group(0)

    xml = re.sub(r"<mi>(&#x[0-9A-Fa-f]+;|[^<&])</mi>", ident_symbol, xml)

    def op_symbol(m: re.Match[str]) -> str:
        return f"<mi>{m.group(1)}</mi>" if _entity_char(m.group(1)) in _IDENT_OPERATORS else m.group(0)

    xml = re.sub(r"<mo>(&#x[0-9A-Fa-f]+;)</mo>", op_symbol, xml)
    # A named function followed by its argument gets a thin space, as in TeX.
    xml = re.sub(
        rf"(<mi>(?:{_FUNCTION_RE})</mi>)(?=<(?:mi|mn|msub|msup|msubsup|mfrac|msqrt|mroot)[ >])",
        r'\1<mspace width="0.1667em"/>',
        xml,
    )
    xml = re.sub(
        rf"(</mi>|</mn>|</msup>|</msub>|</mfrac>|</msqrt>)(<mi>(?:{_FUNCTION_RE})</mi>)",
        r'\1<mspace width="0.1667em"/>\2',
        xml,
    )
    xml = xml.replace('columnalign="left"', 'columnalign="left" style="text-align: left"')
    return xml


class MathError(ValueError):
    """A formula latex2mathml cannot convert."""


def tex_to_mathml(tex: str, display: bool = False) -> str:
    """The MathML of the LaTeX `tex`, inline or as a display formula."""
    try:
        xml = latex2mathml.converter.convert(tex, display="block" if display else "inline")
    except Exception as err:  # latex2mathml raises a variety of exception types
        raise MathError(f"cannot convert {tex!r}: {err}") from err
    xml = fix_mathml(xml)
    alt = html.escape(tex.strip(), quote=True)
    xml = xml.replace("<math ", f'<math alttext="{alt}" ', 1)
    return xml


# ---------------------------------------------------------------------------
# The display syntax of SymLean to LaTeX

_GREEK = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta", "ε": r"\varepsilon",
    "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta", "ι": r"\iota", "κ": r"\kappa",
    "λ": r"\lambda", "μ": r"\mu", "ν": r"\nu", "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho",
    "σ": r"\sigma", "τ": r"\tau", "φ": r"\varphi", "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega",
    "Γ": r"\Gamma", "Δ": r"\Delta", "Θ": r"\Theta", "Λ": r"\Lambda", "Ξ": r"\Xi",
    "Π": r"\Pi", "Σ": r"\Sigma", "Φ": r"\Phi", "Ψ": r"\Psi", "Ω": r"\Omega",
}
_BLACKBOARD = {"ℝ": r"\mathbb{R}", "ℂ": r"\mathbb{C}", "ℕ": r"\mathbb{N}", "ℤ": r"\mathbb{Z}",
               "ℚ": r"\mathbb{Q}"}
_SUBSCRIPTS = dict(zip("₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼ", "0123456789aeoxhklmnpstij"))
_NAMED_CONSTANTS = {"pi": r"\pi", "π": r"\pi", "∞": r"\infty", "e": "e", "i": "i"}
_SIMPLE_FUNCTIONS = {
    "sin": r"\sin", "cos": r"\cos", "tan": r"\tan", "cot": r"\cot", "sec": r"\sec",
    "csc": r"\csc", "sinh": r"\sinh", "cosh": r"\cosh", "tanh": r"\tanh", "coth": r"\coth",
    "asin": r"\arcsin", "arcsin": r"\arcsin", "acos": r"\arccos", "arccos": r"\arccos",
    "atan": r"\arctan", "arctan": r"\arctan", "log": r"\log", "ln": r"\ln",
    "gamma": r"\Gamma", "Gamma": r"\Gamma", "Γ": r"\Gamma", "zeta": r"\zeta", "ζ": r"\zeta",
    "erf": r"\operatorname{erf}", "erfc": r"\operatorname{erfc}", "sign": r"\operatorname{sgn}",
    "asinh": r"\operatorname{arsinh}", "acosh": r"\operatorname{arcosh}",
    "atanh": r"\operatorname{artanh}", "max": r"\max", "min": r"\min", "gcd": r"\gcd",
}
# Indexed families f(n, x) written f_n(x).
_INDEXED_FUNCTIONS = {
    "BesselJ": "J", "LegendreP": "P", "ChebyshevT": "T", "ChebyshevU": "U", "HermiteH": "H",
    "HermiteHe": r"\mathit{He}", "BernoulliB": "B",
}


class _Fail(Exception):
    pass


_TOKEN_RE = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<num>\d+(?:\.\d+)?…?)
  | (?P<mat>!!\[)
  | (?P<vec>!\[)
  | (?P<ident>[A-Za-z\u0370-\u03ff\u2080-\u209c\u1d62\u2c7c][A-Za-z0-9_'\u0370-\u03ff\u2080-\u209c\u1d62\u2c7c]*)
  | (?P<bb>[ℝℂℕℤℚ])
  | (?P<sym>≤|≥|≠|≈|±|∈|∉|∨|∧|↦|√|∞|→|×|[-+*/^!=<>(),;\[\]{}|])
    """,
    re.VERBOSE,
)


def _tokenize(s: str) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    pos = 0
    while pos < len(s):
        m = _TOKEN_RE.match(s, pos)
        if not m:
            raise _Fail(f"unexpected {s[pos]!r}")
        pos = m.end()
        kind = m.lastgroup or ""
        if kind == "ws":
            continue
        out.append((kind, m.group(kind)))
    out.append(("end", ""))
    return out


# Binding powers of the infix operators.
_INFIX = {
    "↦": 5, "∨": 10, "∧": 15,
    "=": 20, "≠": 20, "<": 20, ">": 20, "≤": 20, "≥": 20, "≈": 20, "∈": 20, "∉": 20, "→": 20,
    "±": 30, "+": 30, "-": 30, "*": 40, "×": 40, "/": 40, "^": 60,
}
_RELATIONS = {"=", "≠", "<", ">", "≤", "≥", "≈", "∈", "∉", "→"}


class _Parser:
    """A Pratt parser of the display syntax. Nodes are tuples whose first item is the kind."""

    def __init__(self, s: str) -> None:
        self.toks = _tokenize(s)
        self.i = 0

    def peek(self, k: int = 0) -> tuple[str, str]:
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def take(self) -> tuple[str, str]:
        tok = self.toks[self.i]
        self.i += 1
        return tok

    def expect(self, value: str) -> None:
        kind, text = self.take()
        if text != value or kind == "end":
            raise _Fail(f"expected {value!r}, got {text!r}")

    def sequence(self, closers: set[str]) -> list:
        items = [self.expr(0)]
        while self.peek()[1] == ",":
            self.take()
            items.append(self.expr(0))
        if self.peek()[1] not in closers:
            raise _Fail(f"unexpected {self.peek()[1]!r}")
        return items

    def top(self):
        items = self.sequence({""})
        if self.peek()[0] != "end":
            raise _Fail("trailing input")
        return items[0] if len(items) == 1 else ("seq", items)

    def expr(self, rbp: int):
        left = self.prefix(rbp)
        while True:
            kind, text = self.peek()
            if kind == "sym" and text == "!" and rbp < 70:
                self.take()
                left = ("fact", left)
                continue
            if kind == "sym" and text in _INFIX:
                bp = _INFIX[text]
                if bp <= rbp:
                    break
                self.take()
                if text == "^":
                    right = self.expr(bp - 1)  # right associative
                    left = ("pow", left, right)
                elif text in _RELATIONS:
                    right = self.expr(bp)
                    if left[0] == "rel":
                        left = ("rel", left[1] + [(text, right)])
                    else:
                        left = ("rel", [(None, left), (text, right)])
                else:
                    right = self.expr(bp)
                    left = ("bin", text, left, right)
                continue
            # A numeral before the imaginary unit multiplies it: 2i.
            if kind == "ident" and text == "i" and left[0] == "num" and rbp < 40:
                self.take()
                left = ("bin", "*", left, ("id", "i"))
                continue
            # A numeral directly before √ multiplies it: 3√π.
            if kind == "sym" and text == "√" and left[0] == "num":
                right = self.expr(40)
                left = ("bin", "*", left, right)
                continue
            break
        return left

    def prefix(self, rbp: int):
        kind, text = self.take()
        if kind == "num":
            return ("num", text)
        if kind == "bb":
            return ("bb", text)
        if kind == "sym":
            if text == "-":
                return ("neg", self.expr(max(35, rbp)))
            if text == "√":
                return ("sqrt", self.expr(55))
            if text == "∞":
                return ("id", "∞")
            if text == "(":
                items = self.sequence({")"})
                self.expect(")")
                return ("paren", items[0]) if len(items) == 1 else ("tuple", items)
            if text == "[":
                if self.peek()[1] == "]":
                    self.take()
                    return ("list", [])
                items = self.sequence({"]", ";"})
                if self.peek()[1] == ";" and len(items) == 1:
                    # A continued fraction [a₀; a₁, …, aₖ].
                    self.take()
                    rest = self.sequence({"]"})
                    self.expect("]")
                    return ("cf", items[0], rest)
                self.expect("]")
                return ("list", items)
            if text == "{":
                items = self.sequence({"}"})
                self.expect("}")
                return ("set", items)
            if text == "|":
                inner = self.expr(0)
                self.expect("|")
                return ("abs", inner)
            raise _Fail(f"unexpected {text!r}")
        if kind == "vec":
            items = self.sequence({"]"})
            self.expect("]")
            return ("vec", items)
        if kind == "mat":
            rows = [self.sequence({";", "]"})]
            while self.peek()[1] == ";":
                self.take()
                rows.append(self.sequence({";", "]"}))
            self.expect("]")
            return ("mat", rows)
        if kind == "ident":
            if text == "if":
                cond = self.expr(0)
                self.expect("then")
                yes = self.expr(0)
                self.expect("else")
                no = self.expr(0)
                return ("if", cond, yes, no)
            if text in ("then", "else"):
                raise _Fail("misplaced keyword")
            if self.peek()[1] == "(":
                self.take()
                args = self.sequence({")"})
                self.expect(")")
                return ("call", text, args)
            # Application by juxtaposition, as in `a n` for a sequence.
            nk, nt = self.peek()
            if nk in ("ident", "num") and nt not in ("then", "else", "if") and _is_letter(text):
                arg = self.take()
                return ("call", text, [("num", arg[1]) if arg[0] == "num" else ("id", arg[1])])
            return ("id", text)
        raise _Fail(f"unexpected {text!r}")


def _is_letter(name: str) -> bool:
    return len(name) == 1 and name.isalpha()


def _ident_tex(name: str) -> str:
    """An identifier: one letter, a Greek letter, a constant, or a letter with a subscript."""
    if name in _NAMED_CONSTANTS:
        return _NAMED_CONSTANTS[name]
    base, sub = name, ""
    # Unicode subscripts: a₀, bₙ.
    m = re.fullmatch(r"(.+?)([\u2080-\u209c\u1d62\u2c7c]+)", base)
    if m:
        base, sub = m.group(1), "".join(_SUBSCRIPTS.get(c, "") for c in m.group(2))
    else:
        m = re.fullmatch(r"(.+?)_([A-Za-z0-9]+)", base) or re.fullmatch(r"([^\d_']+?)(\d+)", base)
        if m:
            base, sub = m.group(1), m.group(2)
    primes = ""
    while base.endswith("'"):
        primes += "'"
        base = base[:-1]
    if len(base) == 1 and base.isascii() and base.isalpha():
        tex = base
    elif base in _GREEK:
        tex = _GREEK[base]
    else:
        raise _Fail(f"word {name!r}")
    tex += primes
    if sub:
        sub_tex = {"min": r"\min", "max": r"\max"}.get(sub, sub)
        if len(sub) > 1 and sub not in ("min", "max") and not sub.isdigit():
            sub_tex = rf"\mathrm{{{sub}}}"
        tex += f"_{{{sub_tex}}}"
    return tex


_ATOMIC = {"num", "id", "bb", "call", "paren", "tuple", "list", "set", "vec", "mat", "abs", "sqrt",
           "fact"}


def _strip(node):
    """The node without its outer parentheses."""
    while node[0] == "paren":
        node = node[1]
    return node


def _starts_with_digit(node) -> bool:
    kind = node[0]
    if kind == "num":
        return True
    if kind in ("bin",) and node[1] in ("*", "^"):
        return _starts_with_digit(node[2])
    if kind == "pow":
        return _starts_with_digit(node[1])
    if kind == "frac":
        return False
    return False


def _is_function_like(node) -> bool:
    """Whether `node` prints as a named function application or ends like one."""
    kind = node[0]
    if kind == "call":
        return True
    if kind == "pow":
        return _is_function_like(node[1])
    return False


def _tex(node, ctx: str = "") -> str:
    kind = node[0]
    if kind == "num":
        return node[1].replace("…", r"\ldots")
    if kind == "id":
        return _ident_tex(node[1])
    if kind == "bb":
        return _BLACKBOARD[node[1]]
    if kind == "paren":
        inner = node[1]
        if inner[0] in ("num", "id", "call", "bb"):
            return _tex(inner)
        return _paren(_tex(inner))
    if kind == "tuple":
        return r"\left(" + ",\\ ".join(_tex(x) for x in node[1]) + r"\right)"
    if kind == "list":
        return r"\left[" + ",\\ ".join(_tex(x) for x in node[1]) + r"\right]"
    if kind == "cf":
        return r"\left[" + _tex(node[1]) + ";\\ " + ",\\ ".join(_tex(x) for x in node[2]) + r"\right]"
    if kind == "set":
        return r"\left\{" + ",\\ ".join(_tex(x) for x in node[1]) + r"\right\}"
    if kind == "vec":
        return r"\begin{pmatrix}" + r" \\ ".join(_tex(x) for x in node[1]) + r"\end{pmatrix}"
    if kind == "mat":
        rows = [" & ".join(_tex(x) for x in row) for row in node[1]]
        return r"\begin{pmatrix}" + r" \\ ".join(rows) + r"\end{pmatrix}"
    if kind == "abs":
        return rf"\left|{_tex(node[1])}\right|"
    if kind == "sqrt":
        return rf"\sqrt{{{_tex(_strip(node[1]))}}}"
    if kind == "fact":
        inner = node[1]
        base = _tex(inner)
        if inner[0] not in ("num", "id", "paren", "call"):
            base = rf"\left({base}\right)"
        return base + "!"
    if kind == "neg":
        inner = node[1]
        if inner[0] == "paren" and inner[1][0] in ("bin", "pow", "call", "fact") and \
                not (inner[1][0] == "bin" and inner[1][1] in ("+", "-", "±")):
            inner = inner[1]
        body = _tex(inner)
        if inner[0] == "bin" and inner[1] in ("+", "-", "±"):
            body = rf"\left({body}\right)"
        return "-" + body
    if kind == "pow":
        base, exp = node[1], _strip(node[2])
        btex = _tex(base)
        if base[0] in ("neg", "bin", "rel") or (base[0] == "call" and base[1] == "exp"):
            btex = rf"\left({btex}\right)"
        if base[0] == "call" and base[1] in _SIMPLE_FUNCTIONS and _SIMPLE_FUNCTIONS[base[1]].startswith("\\") \
                and base[1] not in ("gamma", "Gamma", "zeta", "max", "min", "gcd"):
            # sin(x)^2 is written sin²(x).
            fn = _SIMPLE_FUNCTIONS[base[1]]
            return f"{fn}^{{{_tex(exp)}}}" + _paren(",\\ ".join(_tex(_strip(a)) for a in base[2]))
        return f"{{{btex}}}^{{{_tex(exp)}}}"
    if kind == "call":
        return _call_tex(node[1], node[2])
    if kind == "bin":
        op, a, b = node[1], node[2], node[3]
        if op == "/":
            return rf"\frac{{{_tex(_strip(a))}}}{{{_tex(_strip(b))}}}"
        if op == "*":
            return _product_tex(node)
        if op in ("∧", "∨", "↦"):
            word = {"∧": r"\land", "∨": r"\lor", "↦": r"\mapsto"}[op]
            return f"{_tex(a)} {word} {_tex(b)}"
        if op == "×":
            return f"{_tex(a)} \\times {_tex(b)}"
        if op in ("+", "-", "±"):
            sym = {"+": "+", "-": "-", "±": r"\pm"}[op]
            btex = _tex(b)
            if b[0] == "neg" or (op == "-" and b[0] == "bin" and b[1] in ("+", "-")):
                btex = rf"\left({btex}\right)"
            return f"{_tex(a)} {sym} {btex}"
        raise _Fail(f"operator {op}")
    if kind == "rel":
        parts = []
        for op, e in node[1]:
            if op is not None:
                parts.append({"=": "=", "≠": r"\ne", "<": "<", ">": ">", "≤": r"\le", "≥": r"\ge",
                              "≈": r"\approx", "∈": r"\in", "∉": r"\notin", "→": r"\to"}[op])
            parts.append(_tex(e))
        return " ".join(parts)
    if kind == "if":
        rows = []
        cur = node
        while cur[0] == "if":
            rows.append(f"{_tex(cur[2])} & \\text{{if }} {_tex(cur[1])}")
            cur = cur[3]
        rows.append(f"{_tex(cur)} & \\text{{otherwise}}")
        return r"\begin{cases}" + r" \\ ".join(rows) + r"\end{cases}"
    if kind == "seq":
        return ",\\quad ".join(_tex(x) for x in node[1])
    raise _Fail(f"node {kind}")


def _paren(tex: str) -> str:
    """Parentheses around `tex`, stretchy when it is taller than a line of text."""
    if re.search(r"\\(frac|begin|binom|sqrt|left)", tex):
        return rf"\left({tex}\right)"
    return f"({tex})"


def _factors(node) -> list:
    if node[0] == "bin" and node[1] == "*":
        return _factors(node[2]) + _factors(node[3])
    return [node]


def _product_tex(node) -> str:
    factors = _factors(node)
    out = ""
    prev = None
    for f in factors:
        ftex = _tex(f)
        if f[0] in ("bin",) and f[1] in ("+", "-", "±"):
            ftex = rf"\left({ftex}\right)"
        elif f[0] == "neg":
            ftex = rf"\left({ftex}\right)" if prev is not None else ftex
        if prev is None:
            out = ftex
        elif _starts_with_digit(f):
            out += r" \cdot " + ftex
        elif prev[0] == "num" or f[0] == "paren":
            out += ftex if not ftex.startswith("\\") or f[0] == "paren" else " " + ftex
        else:
            out += r"\," + ftex
        prev = f
    return out


def _call_tex(name: str, args: list) -> str:
    if name == "sqrt" and len(args) == 1:
        return rf"\sqrt{{{_tex(_strip(args[0]))}}}"
    if name == "exp" and len(args) == 1:
        return f"e^{{{_tex(_strip(args[0]))}}}"
    if name == "abs" and len(args) == 1:
        return rf"\left|{_tex(_strip(args[0]))}\right|"
    if name == "binomial" and len(args) == 2:
        return rf"\binom{{{_tex(_strip(args[0]))}}}{{{_tex(_strip(args[1]))}}}"
    if name == "floor" and len(args) == 1:
        return rf"\left\lfloor {_tex(_strip(args[0]))} \right\rfloor"
    if name == "ceil" and len(args) == 1:
        return rf"\left\lceil {_tex(_strip(args[0]))} \right\rceil"
    if name in _INDEXED_FUNCTIONS and len(args) == 2:
        sym = _INDEXED_FUNCTIONS[name]
        return f"{sym}_{{{_tex(_strip(args[0]))}}}" + _paren(_tex(_strip(args[1])))
    arg_tex = ",\\ ".join(_tex(_strip(a)) for a in args)
    if name in _SIMPLE_FUNCTIONS:
        return _SIMPLE_FUNCTIONS[name] + _paren(arg_tex)
    if _is_letter(name) or name in _GREEK:
        return _ident_tex(name) + _paren(arg_tex)
    raise _Fail(f"function {name!r}")


def cas_to_tex(text: str) -> str | None:
    """The traditional notation of a SymLean display value, or None if it is not an expression."""
    text = text.strip()
    if not text or len(text) > 600:
        return None
    try:
        tree = _Parser(text).top()
        return _tex(tree)
    except (_Fail, RecursionError, KeyError, IndexError):
        return None


def is_worth_typesetting(tex: str) -> bool:
    """Whether the traditional form says more than the plain one."""
    return bool(re.search(r"\\|\^|_", tex))
