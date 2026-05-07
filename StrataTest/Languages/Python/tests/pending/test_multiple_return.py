def classify(x: int) -> str:
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        return "zero"

def test_multiple_return():
    assert classify(5) == "positive", "positive"
    assert classify(-3) == "negative", "negative"
    assert classify(0) == "zero", "zero"

test_multiple_return()
