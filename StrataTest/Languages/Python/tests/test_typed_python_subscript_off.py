# strata-args: --check-mode bugFinding --check-level full
# Default-mode counterpart. Subscripts go through `Any_get_slice` /
# `Any..get` (the universal Any-tag accessor); the result keeps the
# Any tag.
def first(xs: list) -> int:
    return xs[0]


def at_index(xs: list, i: int) -> int:
    assert i >= 0
    return xs[i]


def lookup(m: dict, k: str) -> int:
    return m[k]
