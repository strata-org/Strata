def test_list_build():
    result = []
    i: int = 0
    while i < 5:
        result.append(i * 2)
        i = i + 1
    assert result[0] == 0, "first"
    assert result[4] == 8, "last"

test_list_build()
