r: int = 0
try:
    x: int = 10 // 0
except ArithmeticError:
    r = 1
assert r == 1, "caught ArithmeticError from ZeroDivisionError"
