import servicelib

def use_fstring() -> bool:
    client: Storage = servicelib.connect("storage")
    name: str = "backup"
    bucket: str = f"{name}_bucket"
    client.put_item(Bucket=bucket, Key="k", Data="v")
    return True
