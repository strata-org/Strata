# strata-args: --check-mode bugFinding --check-level full
class Bag:
    def __init__(self, item):
        self.item = item

def test_untyped_field_ok():
    b = Bag(42)
    assert b.item == 42, "untyped field"

def test_untyped_field_ko():
    b = Bag(44)
    assert b.item == 42, "untyped field must fail"

test_untyped_field_ok()
test_untyped_field_ko()
