def main():
    # Simple for loop
    n: int = 0
    for x in [1, 2, 3]:
        n = n + 1
    assert n > 0, "simple loop incremented"

    # Tuple unpacking in for loop
    n2: int = 10
    for a, b in [(1, 2), (3, 4)]:
        n2 = n2 - 1
    assert n2 < 10, "tuple unpacking decremented"

    # Nested tuple unpacking in for loop
    n3: int = 0
    for x, (y, z) in [(1, (2, 3))]:
        n3 = n3 + 1
    assert n3 > 0, "nested unpacking incremented"

    # While loop
    n4: int = 5
    while n4 > 0:
        n4 = n4 - 1
    assert n4 <= 5, "while loop did not increase n4"
