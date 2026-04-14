def test_dict_empty():
    d = {}
    count: int = 0
    for k in d:
        count = count + 1
    assert count == 0, "empty dict"

test_dict_empty()
