# Soundness bug: shared dict referenced from two different lists
# config is stored in both users[0] and admins[0]. Mutating through
# one list is visible through the other. Strata copies the dict value.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    config: dict = {"val": 0}
    users: list = [config]
    admins: list = [config]
    users[0]["val"] = 42
    assert admins[0]["val"] == 0, "unsound: Python gives 42"
test()
