def compute(x: int) -> int:
    return x * 2

def test_walrus_like():
    r: int = compute(5)
    assert r == 10, "assign from call"

test_walrus_like()
