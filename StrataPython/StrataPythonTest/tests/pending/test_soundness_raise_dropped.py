# strata-pending: soundness
# Soundness bug: raise is silently dropped, so code after raise executes
# In Python, raise stops execution. Strata drops raise entirely.
# This assertion is FALSE in Python (unreachable) but Strata verifies it.
def test() -> None:
    x: int = 1
    raise ValueError("stop")
    x = 2
    assert x == 2, "unsound: unreachable in Python"
test()
