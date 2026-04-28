# Test: Nested try/except, handler chaining

def inner_risky():
    raise ValueError("inner")

def outer_risky():
    raise TypeError("outer")

# Inner handler re-raises to outer handler
try:
    try:
        x = inner_risky()
    except ValueError:
        raise  # re-raise propagates to outer handler
except:
    y = 0

# Inner try inside except of outer try
try:
    outer_risky()
except TypeError:
    try:
        inner_risky()
    except ValueError:
        pass
