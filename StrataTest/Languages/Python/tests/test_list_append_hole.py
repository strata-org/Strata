# strata-args: --check-mode bugFinding --check-level full
def main() -> None:
    xs: list[int] = []
    xs.append(1)
    if xs:
        x: int = xs[0]
    ys: list[int] = []
    xs.extend(ys)
    if ys:
        y: int = ys[0]
