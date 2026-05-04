# strata-pending: soundness
# Soundness bug: two containers sharing a sub-list
# a and b both contain shared as their first element. Mutating through
# a[0][0] changes shared, which is visible through b[0][0].
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    shared: list = [10, 20]
    a: list = [shared, 1]
    b: list = [shared, 2]
    a[0][0] = 99
    assert b[0][0] == 10, "unsound: Python gives 99"
test()
