def test_augadd_list():
    xs = [1, 2]
    xs += [3, 4]
    assert xs[2] == 3, "augmented add list"
    assert xs[3] == 4, "augmented add list last"

test_augadd_list()
