# strata-pending: soundness
# Soundness bug: finally clause ignored even with try/except/finally
# In Python, finally always runs after try/except.
# Strata drops the finally clause entirely.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = 0
    f: int = 0
    try:
        x = 1
    except Exception:
        x = 2
    finally:
        f = 1
    assert f == 0, "unsound: Python gives 1"
test()
