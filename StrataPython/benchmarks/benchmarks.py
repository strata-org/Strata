# Benchmark bodies — a cross-section of program kinds, one type-annotated
# function per scenario. The SAME source is verified on two strata builds
# (see run_benchmarks.py): a baseline where annotated values are boxed in the
# `Any` datatype, and this branch where they lower to native SMT sorts. The
# proposition proved is identical on both; only the encoding differs.
# Functions are verified over their symbolic parameters, so the solver reasons
# abstractly — where the boxed encoding compounds with expression depth.


# --- arithmetic ---

def arith_distrib(a: int, b: int, c: int) -> None:
    assert (a + b) * c == a * c + b * c, "distributivity"


def arith_square(a: int, b: int) -> None:
    assert (a + b) * (a + b) == a * a + 2 * a * b + b * b, "binomial"


def arith_sumsq(a: int, b: int, c: int, d: int) -> None:
    assert a * a + b * b + c * c + d * d >= 0, "sum of squares non-negative"


# --- strings ---

def str_assoc(s: str, t: str, u: str) -> None:
    assert (s + t) + u == s + (t + u), "concat associative"


def str_empty(s: str) -> None:
    assert s + "" == s, "empty identity"


# --- boolean logic ---

def bool_demorgan(a: bool, b: bool) -> None:
    assert (not (a and b)) == ((not a) or (not b)), "de morgan"


# --- comparisons ---

def cmp_trichotomy(a: int, b: int) -> None:
    assert (a < b) or (a == b) or (a > b), "trichotomy"


# --- control flow ---

def control_max(a: int, b: int) -> None:
    m: int = a if a >= b else b
    assert m >= a and m >= b, "max bounds both"


# --- reals ---

def real_normsq(x: float, y: float) -> None:
    assert x * x + y * y >= 0.0, "norm non-negative"
