def test_list_len():
    xs = [10, 20, 30, 40]
    n: int = 0
    for _ in xs:
        n = n + 1
    assert n == 4, "list length via loop"

test_list_len()
