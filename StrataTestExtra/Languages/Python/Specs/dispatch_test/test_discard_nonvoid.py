import servicelib

def discard_result() -> bool:
    client: Storage = servicelib.connect("storage")
    client.get_item(Bucket="b", Key="k")
    return True
