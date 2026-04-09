def inc(x: int) -> int:
    return x + 1

def test_func_call_chain():
    r: int = inc(inc(inc(0)))
    assert r == 3, "chained calls"

test_func_call_chain()
