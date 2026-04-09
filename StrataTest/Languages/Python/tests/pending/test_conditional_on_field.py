class Switch:
    on: bool

    def __init__(self):
        self.on = False

    def flip(self):
        if self.on:
            self.on = False
        else:
            self.on = True

def test_oop_conditional_on_field():
    s = Switch()
    assert s.on == False, "initially off"
    s.flip()
    assert s.on == True, "flipped on"
    s.flip()
    assert s.on == False, "flipped off"

test_oop_conditional_on_field()
