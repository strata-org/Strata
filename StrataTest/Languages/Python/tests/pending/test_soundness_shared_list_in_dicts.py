# strata-pending: soundness
# Soundness bug: same list stored as value in two different dicts
# Both d1 and d2 hold a reference to items. Mutating through d1
# is visible through d2. Strata copies the list value into each dict.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    items: list = [1, 2, 3]
    d1: dict = {"data": items}
    d2: dict = {"data": items}
    d1["data"][0] = 99
    assert d2["data"][0] == 1, "unsound: Python gives 99"
test()
