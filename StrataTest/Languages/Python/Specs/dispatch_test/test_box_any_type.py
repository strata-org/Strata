import servicelib

class Session:
    data: Any
    name: str

    def __init__(self, name: str) -> None:
        self.data = None
        self.name = name

    def set_data(self, value: Any) -> None:
        self.data = value

    def get_name(self) -> str:
        return self.name

def use_box_any() -> bool:
    """Class with Any-typed field going through heap — Box..Any undefined type."""
    s: Session = Session(name="test")
    s.set_data(value="hello")
    n: str = s.get_name()
    client: Storage = servicelib.connect("storage")
    client.put_item(Bucket="b", Key=n, Data="v")
    return True
