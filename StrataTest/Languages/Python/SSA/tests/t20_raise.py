# Test: Raise, bare re-raise in handler

# Explicit raise
def fail_hard():
    raise ValueError("bad input")

# Bare re-raise inside handler
def reraise_example():
    try:
        fail_hard()
    except ValueError:
        raise  # re-raise the caught exception

# Raise with constructed exception
def raise_with_msg(msg: str):
    raise RuntimeError(msg)
