import servicelib

def fetch_item() -> bool:
    client = servicelib.connect("storage")
    # FIXME: Assign return value to avoid Core arity mismatch for non-void methods
    result = client.get_item(Bucket="mybucket", Key="mykey")
    return True
