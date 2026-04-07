def test_reverse_list():
    xs = [1, 2, 3, 4, 5]
    rev = []
    i: int = 4
    while i >= 0:
        rev.append(xs[i])
        i = i - 1
    assert rev[0] == 5, "first reversed"
    assert rev[4] == 1, "last reversed"

test_reverse_list()
