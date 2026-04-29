def test_chained_compare_eval_once():
    a: int = 1
    x: int = 5
    b: int = 10
    assert a < x + 0 < b, "chained with non-simple intermediate"

test_chained_compare_eval_once()
