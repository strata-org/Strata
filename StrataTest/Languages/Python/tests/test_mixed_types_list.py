def test_mixed_types_list():
    xs = [1, "two", 3]
    assert xs[0] == 1, "int element"
    assert xs[1] == "two", "str element"

test_mixed_types_list()
