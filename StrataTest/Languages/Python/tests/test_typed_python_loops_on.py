# strata-args: --typed-python --check-mode bugFinding --check-level full
# Loops with typed counters. The while loop's condition is a native
# int comparison; the loop body mutates a typed int counter.
def count_up(n: int) -> int:
    assert n >= 0
    i: int = 0
    while i < n:
        i = i + 1
    return i


def sum_to(n: int) -> int:
    assert n >= 0
    assert n <= 100
    total: int = 0
    i: int = 0
    while i <= n:
        total = total + i
        i = i + 1
    return total


def product(n: int) -> int:
    assert n >= 1
    assert n <= 10
    p: int = 1
    i: int = 1
    while i <= n:
        p = p * i
        i = i + 1
    return p
