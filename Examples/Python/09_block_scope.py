def main():
    x: int = 10
    if x > 0:
        y: int = x + 1
        x = y
    assert x == 11, "x should be 11"
