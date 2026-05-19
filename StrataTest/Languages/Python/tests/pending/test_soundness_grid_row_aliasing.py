# strata-pending: soundness
# Soundness bug: grid built from repeated row reference
# All three elements of grid are the same list object. Mutating
# grid[0][0] changes all rows. Classic Python "gotcha" with [[0]*n]*m.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    row: list = [0, 0]
    grid: list = [row, row, row]
    grid[0][0] = 99
    assert grid[1][0] == 0, "unsound: Python gives 99"
test()
