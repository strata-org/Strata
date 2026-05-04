# strata-pending: soundness
# Soundness bug: try/else clause is silently ignored
# In Python, the else clause of try/except runs when no exception occurs.
# Strata drops the else clause entirely.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    r: int = 0
    try:
        pass
    except Exception:
        r = -1
    else:
        r = 42
    assert r == 0, "unsound: Python gives 42"
test()
