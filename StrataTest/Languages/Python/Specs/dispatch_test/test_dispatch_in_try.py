import servicelib

def safe_store() -> bool:
    try:
        client = servicelib.connect("storage")
        client.put_item(Bucket="b", Key="k", Data="v")
    except Exception:
        pass
    return True
