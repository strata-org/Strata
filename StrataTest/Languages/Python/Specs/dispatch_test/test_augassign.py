import servicelib

def use_augassign() -> bool:
    client: Storage = servicelib.connect("storage")
    count: int = 0
    items: list = client.list_items(Bucket="mybucket")
    count += 1
    return True
