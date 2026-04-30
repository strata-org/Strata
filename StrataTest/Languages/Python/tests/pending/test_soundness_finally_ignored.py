# Soundness bug: finally clause is silently ignored
# In Python, finally always runs. Strata drops it entirely.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    f: int = 0
    try:
        pass
    finally:
        f = 99
    assert f == 0, "unsound: Python gives 99"
test()
