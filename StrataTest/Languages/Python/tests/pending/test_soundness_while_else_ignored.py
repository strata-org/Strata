# Soundness bug: while/else clause is silently ignored
# In Python, the else clause runs when the loop completes without break.
# Strata drops the else clause entirely.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    i: int = 0
    r: int = 0
    while i < 3:
        i = i + 1
    else:
        r = 42
    assert r == 0, "unsound: Python gives 42"
test()
