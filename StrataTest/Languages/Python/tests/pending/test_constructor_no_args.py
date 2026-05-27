class Empty:
    def __init__(self):
        pass

def test_oop_constructor_no_args():
    e = Empty()
    assert e is not None, "constructor returns object"

test_oop_constructor_no_args()
