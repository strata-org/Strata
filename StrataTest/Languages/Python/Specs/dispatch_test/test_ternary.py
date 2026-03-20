import servicelib

def use_ternary() -> bool:
    client: Storage = servicelib.connect("storage")
    flag: bool = True
    bucket: str = "a" if flag else "b"
    client.put_item(Bucket=bucket, Key="k", Data="v")
    return True
