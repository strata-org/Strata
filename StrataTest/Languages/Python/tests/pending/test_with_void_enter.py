class VoidManager:
    def __init__(self):
        self.active: bool = True

    def __enter__(self):
        self.active = True

    def __exit__(self):
        self.active = False

def test_void_enter():
    mgr: VoidManager = VoidManager()
    with mgr as val:
        x: int = 1
    assert x == 1
