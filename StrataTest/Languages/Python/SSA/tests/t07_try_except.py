# Test: Try/except, exception handler fan-in with undef

def risky():
    raise ValueError("bad")

# Basic try/except
try:
    x = risky()
except:
    x = 0

# Multiple raising instructions in try body (fan-in with undef)
try:
    a = risky()
    b = risky()
except:
    pass
    # a is undef if first call raised
    # b is always undef (never completes if except entered)

# Multiple except clauses
try:
    c = risky()
except ValueError:
    c = -1
except TypeError:
    c = -2
