def test_list_assign():
    xs = [1, 2, 3]
    xs[1] = 99
    assert xs[1] == 99, "list element assignment"

test_list_assign()
