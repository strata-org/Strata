import servicelib

def create_and_check() -> bool:
    client: Storage = servicelib.connect("storage")
    client.put_item(Bucket="b", Key="k", Data="v")
    return True
