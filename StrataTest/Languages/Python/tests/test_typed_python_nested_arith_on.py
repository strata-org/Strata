# strata-args: --typed-python --check-mode bugFinding --check-level full
# Nested arithmetic — long chains of `+` and `*` are where the typed
# encoding wins most: each `Any` operand wraps a `from_int` and each
# operator unwraps with `as_int!`, so the solver spends its time
# peeling tags. Under `--typed-python` the same expression stays in
# `TInt` end-to-end.
def add3(a: int, b: int, c: int) -> int:
    return a + b + c


def add4(a: int, b: int, c: int, d: int) -> int:
    return a + b + c + d
