# Negative test: dict comprehension → unsupported expression
# Expected: warning, unsupported instruction

keys = ["a", "b", "c"]
d = {k: len(k) for k in keys}
