def test_nested_while():
    i: int = 0
    total: int = 0
    while i < 3:
        j: int = 0
        while j < 3:
            total = total + 1
            j = j + 1
        i = i + 1
    assert total == 9, "nested while"

test_nested_while()
