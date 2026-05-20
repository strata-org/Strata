# Test catching KeyError from dict access with missing key
branch = 0
d = {"a": 1, "b": 2}

try:
    val = d["c"]
except KeyError:
    branch = 1

assert branch == 1, "KeyError caught"

# Test catching IndexError from list out-of-bounds
branch = 0
lst = [10, 20, 30]

try:
    val = lst[5]
except IndexError:
    branch = 2

assert branch == 2, "IndexError caught"

# Test catching ZeroDivisionError from modulo
branch = 0

try:
    val = 10 % 0
except ZeroDivisionError:
    branch = 3

assert branch == 3, "ZeroDivisionError from mod caught"

# Test LookupError catches KeyError (parent class)
branch = 0

try:
    val = d["missing"]
except LookupError:
    branch = 4

assert branch == 4, "LookupError catches KeyError"

# Test LookupError catches IndexError (parent class)
branch = 0

try:
    val = lst[99]
except LookupError:
    branch = 5

assert branch == 5, "LookupError catches IndexError"

# Test ArithmeticError catches ZeroDivisionError (parent class)
branch = 0

try:
    val = 5 // 0
except ArithmeticError:
    branch = 6

assert branch == 6, "ArithmeticError catches ZeroDivisionError"
