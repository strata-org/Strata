class Config:
    debug: bool
    level: int

    def __init__(self):
        self.debug = False
        self.level = 0

def test_class_init_default():
    c = Config()
    assert c.debug == False, "default bool"
    assert c.level == 0, "default int"

test_class_init_default()
