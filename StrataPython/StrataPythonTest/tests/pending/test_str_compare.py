def test_str_compare():
    assert "abc" < "abd", "string lt"
    assert "xyz" > "abc", "string gt"
    assert "abc" <= "abc", "string le"

test_str_compare()
