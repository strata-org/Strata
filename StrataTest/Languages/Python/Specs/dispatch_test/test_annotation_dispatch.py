import servicelib

def annotated_client() -> bool:
    client: Storage = servicelib.connect("storage")
    client.put_item(Bucket="b", Key="k", Data="d")
    return True
