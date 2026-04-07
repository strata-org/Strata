def test_list_slice():
    xs = [1, 2, 3, 4, 5]
    ys = xs[1:4]
    assert ys[0] == 2, "slice start"
    assert ys[2] == 4, "slice end"

test_list_slice()
