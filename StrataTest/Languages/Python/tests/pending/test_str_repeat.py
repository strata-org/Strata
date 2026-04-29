def test_str_repeat():
    a: str = "ab"
    b: str = a * 3
    assert b == "ababab", "string repeat"

test_str_repeat()
