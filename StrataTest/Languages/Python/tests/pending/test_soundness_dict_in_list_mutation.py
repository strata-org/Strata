# Soundness bug: dict stored in list, mutated through list access
# d is stored in lst. Mutating lst[0]["val"] should change d["val"]
# because they are the same object. Strata doesn't model this sharing.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    d: dict = {"val": 10}
    lst: list = [d]
    lst[0]["val"] = 99
    assert d["val"] == 10, "unsound: Python gives 99"
test()
