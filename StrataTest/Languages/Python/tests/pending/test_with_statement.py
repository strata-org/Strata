class FakeCtx:
    entered: bool
    exited: bool

    def __init__(self):
        self.entered = False
        self.exited = False

    def __enter__(self):
        self.entered = True
        return self

    def __exit__(self, *args):
        self.exited = True

def test():
    ctx = FakeCtx()
    with ctx as c:
        assert c.entered == True, "entered"
    assert ctx.exited == True, "exited"
test()
