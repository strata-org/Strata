r: int = 0
try:
    x: int = "abc" + 1
except TypeError:
    r = 1
assert r == 1, "caught TypeError from invalid add"
