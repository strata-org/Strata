import servicelib

def assign_void() -> bool:
    client: Storage = servicelib.connect("storage")
    result = client.put_item(Bucket="b", Key="k", Data="d")
    return True
