import servicelib

def try_scope() -> bool:
    client: Storage = servicelib.connect("storage")
    try:
        result: Any = client.get_item(Bucket="b", Key="k")
    except Exception as e:
        result: Any = "default"
    return result == "default"
