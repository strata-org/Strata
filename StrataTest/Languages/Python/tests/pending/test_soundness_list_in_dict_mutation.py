# Soundness bug: list stored in dict, mutated through dict access
# lst is stored as a value in d. Mutating d["items"][0] should change lst[0]
# because they are the same object. Strata doesn't model this sharing.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    lst: list = [1, 2, 3]
    d: dict = {"items": lst}
    d["items"][0] = 99
    assert lst[0] == 1, "unsound: Python gives 99"
test()
