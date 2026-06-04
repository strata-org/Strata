import servicelib

def violate_precondition() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Bucket="", Key="k", Data="d")
    return True
