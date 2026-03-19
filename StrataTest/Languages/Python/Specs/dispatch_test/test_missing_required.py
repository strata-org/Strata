import servicelib

def missing_key() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Bucket="mybucket")
    return True
