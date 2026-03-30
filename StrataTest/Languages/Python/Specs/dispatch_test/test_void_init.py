import servicelib

def init_void() -> bool:
    client: Storage = servicelib.connect("storage")
    x: str = client.put_item(Bucket="b", Key="k", Data="d")
    return True
