def test_list_empty():
    xs = []
    count: int = 0
    for _ in xs:
        count = count + 1
    assert count == 0, "empty list"

test_list_empty()
