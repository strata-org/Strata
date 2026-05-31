def test():
    xs = [1, 2, 3, 4, 5]
    del xs[1:3]
    assert xs[0] == 1, "first unchanged"
    assert xs[1] == 4, "fourth shifted"
    assert xs[2] == 5, "fifth shifted"


# reverse slice is a no-op in CPython
def test_del_list_reverse_slice():
    xs = [1, 2, 3, 4, 5]
    del xs[3:1]
    assert xs[0] == 1, "first unchanged"
    assert xs[3] == 4, "fourth unchanged"  # would fail today (xs has 7 elements)
    assert xs[4] == 5, "fifth unchanged"

# test_del_list_slice_to_end.py — omit stop
def test_del_list_slice_to_end():
    xs = [1, 2, 3, 4, 5]
    del xs[2:]
    assert xs[0] == 1 and xs[1] == 2, "head preserved"

# test_del_list_slice_from_start — omit start
def test_del_list_slice_from_start():
    xs = [1, 2, 3, 4, 5]
    del xs[:2]
    assert xs[0] == 3 and xs[2] == 5, "tail preserved"

# test_del_list_slice_all — del xs[:] empties the list
def test_del_list_slice_all():
    xs = [1, 2, 3]
    del xs[:]
    assert xs == [], "emptied"
