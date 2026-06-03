def test_str_multiline():
    s: str = "line1\nline2"
    assert "\n" in s, "contains newline"

test_str_multiline()
