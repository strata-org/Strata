def test_countdown_wrong() -> int:
    n: int = 5
    total: int = 0
    while n > 0:
        total = total + n
        n = n - 1
    assert total == 99, "FALSE: total is 15 not 99"
    return total
test_countdown_wrong()
