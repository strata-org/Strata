# strata-args: --check-mode bugFinding --check-level full
# Default-mode counterpart for function composition.
def f(x: int) -> int:
    return x + 1


def f2(x: int) -> int:
    return f(f(x))


def f3(x: int) -> int:
    return f(f(f(x)))
