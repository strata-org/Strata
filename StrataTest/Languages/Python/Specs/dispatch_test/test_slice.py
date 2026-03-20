import servicelib

def use_slice() -> bool:
    client: Storage = servicelib.connect("storage")
    items: list = client.list_items(Bucket="mybucket")
    subset: list = items[1:]
    return True
