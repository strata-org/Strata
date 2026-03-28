# Negative test: walrus operator (NamedExpr) → unsupported expression
# Expected: warning, unsupported instruction

data = [1, 2, 3, 4, 5]
filtered = [y for x in data if (y := x * 2) > 4]
