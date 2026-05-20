s: str = "hello"
r: int = 0
try:
    c: str = s[100]
except IndexError:
    r = 1
assert r == 1, "caught IndexError from string index"
