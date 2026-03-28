# Negative test: lambda → unsupported expression
# Expected: warning, unsupported instruction

f = lambda x, y: x + y
result = f(1, 2)
