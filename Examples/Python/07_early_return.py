def abs_value(x: int) -> int:
    if x < 0:
        return -x
    return x

def main():
    a: int = abs_value(-7)
    assert a == 7, "abs(-7) should be 7"
