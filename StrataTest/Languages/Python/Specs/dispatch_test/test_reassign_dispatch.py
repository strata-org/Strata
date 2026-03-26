import servicelib

def reassign_client() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Bucket="a", Key="k1", Data="d1")
    client = servicelib.connect("storage")
    # FIXME: Assign return value to avoid Core arity mismatch for non-void methods
    result = client.get_item(Bucket="a", Key="k2")
    return True
