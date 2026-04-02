def main():
    # Integer exponentiation
    x: int = 8 ** 2
    assert x == 64, "8 ** 2 should be 64"

    y: int = 2 ** 10
    assert y == 1024, "2 ** 10 should be 1024"

    # Bool base with int exponent
    z: int = True ** 5
    assert z == 1, "True ** 5 should be 1"

    w: int = False ** 3
    assert w == 0, "False ** 3 should be 0"

    # Negative exponent returns a float (uninterpreted via float_pow)
    r: float = 2 ** -1
    assert r > 0, "2 ** -1 should be positive"

if __name__ == "__main__":
    main()
