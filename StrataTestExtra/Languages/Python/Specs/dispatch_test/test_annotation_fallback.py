import servicelib

def with_annotation() -> bool:
    client: StorageClient = servicelib.connect("storage")
    client.put_item(Bucket="b", Key="k", Data="v")
    return True
