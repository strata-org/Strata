class Flag:
    active: bool

    def __init__(self, active: bool):
        self.active = active

def test_oop_constructor_bool_field():
    f = Flag(True)
    assert f.active == True, "bool field"

test_oop_constructor_bool_field()
