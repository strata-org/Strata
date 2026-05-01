def linear_search(xs, target: int) -> int:
    i: int = 0
    for x in xs:
        if x == target:
            return i
        i = i + 1
    return -1

def test_linear_search():
    assert linear_search([5, 3, 8, 1], 8) == 2, "found"
    assert linear_search([5, 3, 8, 1], 9) == -1, "not found"

test_linear_search()
