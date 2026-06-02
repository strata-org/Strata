# strata-args: --typed-python --check-mode bugFinding --check-level full
# Function composition — `f(f(f(...)))` chains compound the boundary
# cost: every call wraps its argument in `from_int` and unwraps the
# result with `as_int!`, and each layer hides the previous bound from
# the solver. Under `--typed-python` the calls stay in native sorts
# and the boundary shim collapses adjacent wrap/unwrap pairs.
def f(x: int) -> int:
    return x + 1


def f2(x: int) -> int:
    return f(f(x))


def f3(x: int) -> int:
    return f(f(f(x)))
