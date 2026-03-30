import servicelib

def get_and_return() -> str:
    client: Storage = servicelib.connect("storage")
    result = client.get_item(Bucket="b", Key="k")
    msg: str = result
    return msg
