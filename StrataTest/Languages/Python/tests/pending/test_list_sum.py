def test_list_sum():
    xs = [1, 2, 3, 4, 5]
    s: int = 0
    for x in xs:
        s = s + x
    assert s == 15, "list sum"

test_list_sum()
