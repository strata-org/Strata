# Benchmark bodies — a cross-section of program kinds, one function per
# scenario. Type placeholders (__INT__, __REAL__, __STR__, __BOOL__) are
# instantiated by run_benchmarks.py at native types and at `Any`. Functions are
# verified over their symbolic parameters, so the solver reasons abstractly —
# where boxing into the `Any` datatype is expensive and native types pay off.
from typing import Any


# --- arithmetic ---

def arith_distrib(a: __INT__, b: __INT__, c: __INT__) -> None:
    assert (a + b) * c == a * c + b * c, "distributivity"


def arith_square(a: __INT__, b: __INT__) -> None:
    assert (a + b) * (a + b) == a * a + 2 * a * b + b * b, "binomial"


def arith_sumsq(a: __INT__, b: __INT__, c: __INT__, d: __INT__) -> None:
    assert a * a + b * b + c * c + d * d >= 0, "sum of squares non-negative"


# --- strings ---

def str_assoc(s: __STR__, t: __STR__, u: __STR__) -> None:
    assert (s + t) + u == s + (t + u), "concat associative"


def str_empty(s: __STR__) -> None:
    assert s + "" == s, "empty identity"


# --- boolean logic ---

def bool_demorgan(a: __BOOL__, b: __BOOL__) -> None:
    assert (not (a and b)) == ((not a) or (not b)), "de morgan"


# --- comparisons ---

def cmp_trichotomy(a: __INT__, b: __INT__) -> None:
    assert (a < b) or (a == b) or (a > b), "trichotomy"


# --- control flow ---

def control_max(a: __INT__, b: __INT__) -> None:
    m: __INT__ = a if a >= b else b
    assert m >= a and m >= b, "max bounds both"


# --- reals ---

def real_normsq(x: __REAL__, y: __REAL__) -> None:
    assert x * x + y * y >= 0.0, "norm non-negative"
