import servicelib

def procedure_as_param(x: Storage_put_item) -> bool:
    client = servicelib.connect("storage")
    result = client.put_item(Bucket="b", Key="k", Data="d")
    return True
