# Test: except SomeError as e, type matching with isinstance

def risky() -> int:
    raise ValueError("bad input")

# Typed except with binding
try:
    result = risky()
except ValueError as e:
    result = -1
    msg = str(e)

# Multiple typed except clauses
try:
    value = risky()
except ValueError as e:
    value = 0
except KeyError as e:
    value = -1
except Exception as e:
    value = -2
