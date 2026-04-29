class Named:
    name: str

    def __init__(self, name: str):
        self.name = name

def test_oop_constructor_str_field():
    n = Named("hello")
    assert n.name == "hello", "string field"

test_oop_constructor_str_field()
