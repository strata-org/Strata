import servicelib

class SimpleClient:
    active: bool

    def __init__(self) -> None:
        self.active = True

def use_class_init_noargs() -> bool:
    client: SimpleClient = SimpleClient()
    return True
