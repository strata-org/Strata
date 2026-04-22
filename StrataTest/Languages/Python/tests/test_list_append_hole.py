# strata-args: --check-mode bugFinding --check-level full
def main() -> None:
    xs: list[int] = []
    xs.append(1)
    if xs:
        x: int = xs[0]
