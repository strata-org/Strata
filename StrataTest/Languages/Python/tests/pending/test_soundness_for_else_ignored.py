# Soundness bug: for/else clause is silently ignored
# In Python, the else clause runs when the loop completes without break.
# Strata drops the else clause entirely.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    r: int = 0
    for x in [1, 2, 3]:
        pass
    else:
        r = 42
    assert r == 0, "unsound: Python gives 42"
test()
