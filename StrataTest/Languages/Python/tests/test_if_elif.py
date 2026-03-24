def classify(x: int) -> str:
    if x < 0:
        return "negative"
    elif x == 0:
        return "zero"
    elif x < 10:
        return "small"
    else:
        return "large"

def main():
    r1: str = classify(-5)
    assert r1 == "negative", "should be negative"

    r2: str = classify(0)
    assert r2 == "zero", "should be zero"

    r3: str = classify(7)
    assert r3 == "small", "should be small"

    r4: str = classify(100)
    assert r4 == "large", "should be large"

if __name__ == "__main__":
    main()
