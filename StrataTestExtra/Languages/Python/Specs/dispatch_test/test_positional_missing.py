import servicelib

def positional_missing() -> bool:
    client = servicelib.connect("storage")
    client.delete_item("mybucket")
    return True
