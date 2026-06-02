# strata-args: --typed-python --check-mode bugFinding --check-level full
# Native subscript dispatch over typed containers. `xs[i]` on a
# `list[int]` lowers to `Sequence.select`; `m[k]` on `dict[str, int]`
# lowers to native `select`. The index is unwrapped via fromAny so the
# peephole cancels with the wrap from the local Name read.
def first(xs: list) -> int:
    return xs[0]


def at_index(xs: list, i: int) -> int:
    assert i >= 0
    return xs[i]


def lookup(m: dict, k: str) -> int:
    return m[k]
