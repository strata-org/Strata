# Test: BinOp, UnaryOp, CompareOp, AugAssign

x: int = 10
y: int = 3

# BinOp
a = x + y
b = x - y
c = x * y
d = x / y
e = x // y
f = x % y
g = x ** y

# UnaryOp
neg = -x
flip = not True

# CompareOp
eq = x == y
ne = x != y
lt = x < y
le = x <= y
gt = x > y
ge = x >= y
is_none = x is None
is_not_none = x is not None
in_list = x in [1, 2, 3]
not_in_list = x not in [1, 2, 3]

# AugAssign
x += 1
x -= 2
x *= 3
