# Soundness bug: raise in try is dropped, so r=2 executes after raise
# In Python, raise stops execution within the try block.
# Strata drops raise, so r=2 executes, and the except handler is skipped.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    r: int = 0
    try:
        r = 1
        raise ValueError("stop")
        r = 2
    except ValueError:
        pass
    assert r == 2, "unsound: Python gives 1"
test()
