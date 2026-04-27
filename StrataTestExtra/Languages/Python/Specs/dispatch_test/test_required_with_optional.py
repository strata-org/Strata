import servicelib

def optional_only() -> bool:
    client = servicelib.connect("storage")
    client.list_items(Bucket="mybucket", MaxResults=10)
    return True
