import servicelib

def optional_missing_required() -> bool:
    client = servicelib.connect("storage")
    client.list_items(MaxResults=10)
    return True
