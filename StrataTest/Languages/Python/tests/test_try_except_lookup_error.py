l: list[int] = [1, 2, 3]
d: dict[str, int] = {"a": 1}
r: int = 0

try:
    x: int = l[10]
except LookupError:
    r = 1
assert r == 1, "caught LookupError from IndexError"

try:
    y: int = d["missing"]
except LookupError:
    r = 2
assert r == 2, "caught LookupError from KeyError"
