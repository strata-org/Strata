# Test: Raise, bare re-raise in handler

# Explicit raise
def fail_hard():
    raise ValueError("bad input")

# Bare re-raise inside typed handler
def reraise_example():
    try:
        fail_hard()
    except ValueError:
        raise  # re-raise the caught exception

# Raise with constructed exception
def raise_with_msg(msg: str):
    raise RuntimeError(msg)

# Bare raise with named exception
def reraise_named():
    try:
        fail_hard()
    except ValueError as e:
        print(e)
        raise

# Bare raise in bare except (no type filter)
def reraise_bare():
    try:
        fail_hard()
    except:
        raise

# Bare raise after work in handler
def reraise_after_work():
    try:
        x = fail_hard()
    except ValueError:
        y = 1
        raise
