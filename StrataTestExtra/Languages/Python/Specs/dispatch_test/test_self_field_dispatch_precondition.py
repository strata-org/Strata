import servicelib

class MyService:
    def __init__(self):
        self.store: Storage = servicelib.connect("storage")

    def save_empty_bucket(self) -> bool:
        self.store.put_item(Bucket="", Key="k", Data="v")
        return True

def trigger() -> bool:
    svc: MyService = MyService()
    return svc.save_empty_bucket()
