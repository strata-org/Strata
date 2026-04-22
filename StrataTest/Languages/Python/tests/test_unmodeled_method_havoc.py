# strata-args: --check-mode bugFinding --check-level full
def main() -> None:
    # Receiver havoc: xs.append() is unmodeled, so xs must not stay empty
    xs: list[int] = []
    xs.append(1)
    if xs:
        x: int = xs[0]
    # Argument havoc: d.update(other) is unmodeled and iterates over other,
    # which is an observable side effect abstracted away by the hole.
    other: dict[str, int] = {}
    d: dict[str, int] = {"a": 1}
    d.update(other)
    if other:
        v: int = other["b"]
