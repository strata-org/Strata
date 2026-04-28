import servicelib

class MyService:
    def __init__(self):
        self.store = servicelib.connect("storage")

    def save(self) -> bool:
        self.store.put_item(Bucket="b", Key="k", Data="v")
        return True
