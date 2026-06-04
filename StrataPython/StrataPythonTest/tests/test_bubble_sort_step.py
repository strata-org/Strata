def test_bubble_sort_step():
    xs = [3, 1, 2]
    if xs[0] > xs[1]:
        t: int = xs[0]
        xs[0] = xs[1]
        xs[1] = t
    if xs[1] > xs[2]:
        t2: int = xs[1]
        xs[1] = xs[2]
        xs[2] = t2
    if xs[0] > xs[1]:
        t3: int = xs[0]
        xs[0] = xs[1]
        xs[1] = t3
    assert xs[0] == 1, "sorted first"
    assert xs[1] == 2, "sorted second"
    assert xs[2] == 3, "sorted third"

test_bubble_sort_step()
