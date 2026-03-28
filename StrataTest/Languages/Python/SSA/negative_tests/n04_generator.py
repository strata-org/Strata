# Negative test: generator expression → unsupported expression
# Expected: warning, unsupported instruction

nums = [1, 2, 3]
total = sum(x * x for x in nums)
