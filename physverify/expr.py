"""Expression language shared by the Python planner/judge and the Lean kernel.

The AST mirrors `PhysVerify.Expr` in `lean/PhysVerify/Expr.lean` node-for-node, so a
theory is translated to Lean by literal serialization (`to_lean`), never by
re-interpreting its meaning.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction

FUNCS = ("sin", "cos", "exp", "log")


@dataclass(frozen=True)
class E:
    kind: str  # var lit pi neg add sub mul div powi sqrt rpow app
    args: tuple = ()
    name: str = ""  # var name / function name
    q: Fraction | int | None = None  # literal value, integer or rational exponent

    def __repr__(self) -> str:
        return to_str(self)


def var(n: str) -> E: return E("var", name=n)
def lit(q) -> E: return E("lit", q=Fraction(q))
PI = E("pi")


# ---------------------------------------------------------------- parsing

_TOKEN = re.compile(r"\s*(?:(\d+\.?\d*(?:[eE][-+]?\d+)?|\.\d+(?:[eE][-+]?\d+)?)|([A-Za-z_][A-Za-z_0-9]*)|(\*\*|[-+*/^(),]))")


def _tokens(s: str) -> list[str]:
    out, pos = [], 0
    s = s.strip()
    while pos < len(s):
        m = _TOKEN.match(s, pos)
        if not m or m.end() == pos:
            raise ValueError(f"cannot parse {s[pos:]!r}")
        out.append(m.group(m.lastindex))
        pos = m.end()
    return [("^" if t == "**" else t) for t in out]


class _Parser:
    def __init__(self, s: str):
        self.t, self.i = _tokens(s), 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, want=None):
        tok = self.peek()
        if tok is None or (want is not None and tok != want):
            raise ValueError(f"expected {want!r}, got {tok!r}")
        self.i += 1
        return tok

    def expr(self) -> E:
        node = self.term()
        while self.peek() in ("+", "-"):
            op = self.take()
            node = E("add" if op == "+" else "sub", (node, self.term()))
        return node

    def term(self) -> E:
        node = self.unary()
        while self.peek() in ("*", "/"):
            op = self.take()
            node = E("mul" if op == "*" else "div", (node, self.unary()))
        return node

    def unary(self) -> E:
        if self.peek() == "-":
            self.take()
            return E("neg", (self.unary(),))
        if self.peek() == "+":
            self.take()
            return self.unary()
        return self.power()

    def power(self) -> E:
        base = self.atom()
        if self.peek() == "^":
            self.take()
            q = self._exponent()
            if q.denominator == 1:
                return E("powi", (base,), q=int(q))
            return E("rpow", (base,), q=q)
        return base

    def _exponent(self, paren: bool = False) -> Fraction:
        # exponents are literal numbers: 2, -3, -2.1, (1/2), (-21/10)
        neg = False
        if self.peek() == "(":
            self.take()
            q = self._exponent(paren=True)
            self.take(")")
            return q
        if self.peek() == "-":
            self.take()
            neg = True
        q = Fraction(self.take())
        if paren and self.peek() == "/":
            self.take()
            q /= Fraction(self.take())
        return -q if neg else q

    def atom(self) -> E:
        tok = self.take()
        if tok == "(":
            node = self.expr()
            self.take(")")
            return node
        if re.match(r"[\d.]", tok):
            return lit(Fraction(tok))
        if tok == "pi":
            return PI
        if tok in PIECEWISE and self.peek() == "(":
            self.take("(")
            args = [self.expr()]
            while self.peek() == ",":
                self.take(",")
                args.append(self.expr())
            self.take(")")
            if len(args) != PIECEWISE[tok]:
                raise ValueError(f"{tok} takes {PIECEWISE[tok]} argument(s), got {len(args)}")
            return piecewise(tok, *args)
        if tok in FUNCS or tok == "sqrt":
            self.take("(")
            arg = self.expr()
            self.take(")")
            return E("sqrt", (arg,)) if tok == "sqrt" else E("app", (arg,), name=tok)
        return var(tok)


PIECEWISE = {"abs": 1, "min": 2, "max": 2, "minmod": 2}


def piecewise(name: str, *a: E) -> E:
    """abs, min, max and minmod, written with |x| = sqrt(x^2) so the AST (and its Lean mirror) needs
    no new node: |x| = sqrt(x^2), max(a, b) = (a + b + |a - b|)/2, min(a, b) = (a + b - |a - b|)/2,
    minmod(a, b) = max(0, min(a, b)) + min(0, max(a, b)) (the argument of smaller magnitude if a and
    b have the same sign, else 0). Each |x| is later split into the closed cells x >= 0 and x <= 0
    (`schemes.checks.sign_cells`), where the expression is a polynomial."""
    if name == "abs":
        return E("sqrt", (E("powi", (a[0],), q=2),))
    if name == "minmod":
        zero = lit(0)
        return E("add", (piecewise("max", zero, piecewise("min", *a)), piecewise("min", zero, piecewise("max", *a))))
    s = E("add" if name == "max" else "sub", (E("add", a), piecewise("abs", E("sub", a))))
    return E("div", (s, lit(2)))


def parse(s: str) -> E:
    p = _Parser(s)
    node = p.expr()
    if p.peek() is not None:
        raise ValueError(f"trailing input in {s!r}: {p.t[p.i:]}")
    return node


# ---------------------------------------------------------------- utilities

def variables(e: E) -> set[str]:
    if e.kind == "var":
        return {e.name}
    out: set[str] = set()
    for a in e.args:
        out |= variables(a)
    return out


def to_str(e: E) -> str:
    k, a = e.kind, e.args
    if k == "var": return e.name
    if k == "lit": return str(e.q)
    if k == "pi": return "pi"
    if k == "neg": return f"-({to_str(a[0])})"
    if k in ("add", "sub", "mul", "div"):
        op = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[k]
        return f"({to_str(a[0])} {op} {to_str(a[1])})"
    if k in ("powi", "rpow"): return f"({to_str(a[0])})^({e.q})"
    if k == "sqrt": return f"sqrt({to_str(a[0])})"
    if k == "app": return f"{e.name}({to_str(a[0])})"
    raise ValueError(k)


def substitute(e: E, env: dict[str, E]) -> E:
    if e.kind == "var":
        return env.get(e.name, e)
    if not e.args:
        return e
    return E(e.kind, tuple(substitute(x, env) for x in e.args), e.name, e.q)


def _is(e: E, v) -> bool:
    return e.kind == "lit" and e.q == v


def simplify(e: E) -> E:
    """Constant folding for 0 and 1 (keeps derivative expressions small)."""
    if not e.args:
        return e
    a = tuple(simplify(x) for x in e.args)
    k = e.kind
    if k == "mul":
        if _is(a[0], 0) or _is(a[1], 0): return lit(0)
        if _is(a[0], 1): return a[1]
        if _is(a[1], 1): return a[0]
    if k == "add":
        if _is(a[0], 0): return a[1]
        if _is(a[1], 0): return a[0]
    if k == "sub" and _is(a[1], 0): return a[0]
    if k == "sub" and _is(a[0], 0): return simplify(E("neg", (a[1],)))
    if k == "div" and _is(a[0], 0): return lit(0)
    if k == "neg":
        if _is(a[0], 0): return lit(0)
        if a[0].kind == "neg": return a[0].args[0]
    if k == "powi" and e.q == 1: return a[0]
    if k == "powi" and e.q == 0: return lit(1)
    if all(x.kind == "lit" for x in a) and k in ("add", "sub", "mul", "neg"):
        q = [x.q for x in a]
        return lit({"add": lambda: q[0] + q[1], "sub": lambda: q[0] - q[1],
                    "mul": lambda: q[0] * q[1], "neg": lambda: -q[0]}[k]())
    return E(k, a, e.name, e.q)


def diff(e: E, x: str) -> E:
    """Simplified symbolic derivative d e / d x (used by the validated integrator)."""
    return simplify(_diff(e, x))


def _diff(e: E, x: str) -> E:
    k, a = e.kind, e.args
    zero, one = lit(0), lit(1)
    if k == "var": return one if e.name == x else zero
    if k in ("lit", "pi"): return zero
    if k == "neg": return E("neg", (_diff(a[0], x),))
    if k in ("add", "sub"): return E(k, (_diff(a[0], x), _diff(a[1], x)))
    if k == "mul":
        return E("add", (E("mul", (_diff(a[0], x), a[1])), E("mul", (a[0], _diff(a[1], x)))))
    if k == "div":
        num = E("sub", (E("mul", (_diff(a[0], x), a[1])), E("mul", (a[0], _diff(a[1], x)))))
        return E("div", (num, E("powi", (a[1],), q=2)))
    if k == "powi":
        return E("mul", (E("mul", (lit(e.q), E("powi", (a[0],), q=e.q - 1))), _diff(a[0], x)))
    if k == "rpow":
        return E("mul", (E("mul", (lit(e.q), E("rpow", (a[0],), q=e.q - 1))), _diff(a[0], x)))
    if k == "sqrt":
        return E("div", (_diff(a[0], x), E("mul", (lit(2), e))))
    if k == "app":
        u, du = a[0], _diff(a[0], x)
        outer = {"sin": E("app", (u,), name="cos"),
                 "cos": E("neg", (E("app", (u,), name="sin"),)),
                 "exp": e,
                 "log": E("div", (one, u))}[e.name]
        return E("mul", (outer, du))
    raise ValueError(k)


# ---------------------------------------------------------------- Lean serialization

def _lean_rat(q: Fraction) -> str:
    q = Fraction(q)
    return f"({q.numerator} : ℚ)" if q.denominator == 1 else f"(({q.numerator} : ℚ) / {q.denominator})"


def to_lean(e: E, index: dict[str, int]) -> str:
    """Serialize to a `PhysVerify.Expr` literal; variables become `.var i`."""
    k, a = e.kind, e.args
    if k == "var": return f"(.var {index[e.name]})"
    if k == "lit": return f"(.lit {_lean_rat(e.q)})"
    if k == "pi": return ".pi"
    if k == "neg": return f"(.neg {to_lean(a[0], index)})"
    if k in ("add", "sub", "mul", "div"):
        return f"(.{k} {to_lean(a[0], index)} {to_lean(a[1], index)})"
    if k == "powi": return f"(.powi {to_lean(a[0], index)} ({e.q}))"
    if k == "rpow": return f"(.rpow {to_lean(a[0], index)} {_lean_rat(e.q)})"
    if k == "sqrt": return f"(.sqrt {to_lean(a[0], index)})"
    if k == "app": return f"(.app .{e.name} {to_lean(a[0], index)})"
    raise ValueError(k)
