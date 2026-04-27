import servicelib

def bad_service() -> bool:
    client = servicelib.connect("invalid")
    client.put_item(Bucket="b", Key="k", Data="v")
    return True
