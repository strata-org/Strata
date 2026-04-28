# Test: With statement, __enter__/__exit__, exception path

class MyCtx:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False

# Basic with
with MyCtx() as ctx:
    x = 1

# With that may raise in body
def risky():
    raise ValueError("fail")

with MyCtx() as ctx:
    risky()
