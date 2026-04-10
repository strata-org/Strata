# strata-args: --check-mode bugFinding --check-level full
def inc(x: int) -> int:
    return x + 1

def double_inc(x: int) -> int:
    y: int = inc(x)
    return y * 2

def triple_apply(x: int) -> int:
    a: int = double_inc(x)
    b: int = inc(a)
    return b

def main():
    r: int = triple_apply(3)
    # triple_apply(3) = inc(double_inc(3)) = inc(inc(3) * 2) = inc(4 * 2) = inc(8) = 9
    assert r == 9, "triple_apply(3) should be 9"
    assert r == 10, "triple_apply(3) should not be 10"

if __name__ == "__main__":
    main()
