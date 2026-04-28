# Test: With statement where body uses the `as` variable
# Regression test for enterBlock demand: ctx must be threaded as a block param

class MyCtx:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False

with MyCtx() as ctx:
    print(ctx)
