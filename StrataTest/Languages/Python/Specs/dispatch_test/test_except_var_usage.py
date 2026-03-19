import servicelib

def except_var_usage() -> bool:
    client: Storage = servicelib.connect("storage")
    try:
        client.put_item(Bucket="b", Key="k", Data="v")
    except Exception as e:
        msg: str = str(e)
        return False
    return True
