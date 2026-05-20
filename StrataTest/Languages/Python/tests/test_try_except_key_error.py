d: dict[str, int] = {"a": 1}
r: int = 0
try:
    x: int = d["b"]
except KeyError:
    r = 1
assert r == 1, "caught KeyError"
