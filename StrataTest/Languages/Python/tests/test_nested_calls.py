def double(x: int) -> int:
    return x * 2

def add_one(x: int) -> int:
    return x + 1

def main():
    a: int = double(3)
    b: int = double(a)
    assert b == 12, "double(double(3)) should be 12"

    c: int = double(5)
    d: int = add_one(c)
    assert d == 11, "add_one(double(5)) should be 11"

    e: int = add_one(4)
    f: int = double(e)
    assert f == 10, "double(add_one(4)) should be 10"

if __name__ == "__main__":
    main()
