import servicelib

def nested_try() -> bool:
    client: Storage = servicelib.connect("storage")
    try:
        client.put_item(Bucket="b", Key="k1", Data="v1")
        try:
            client.put_item(Bucket="b", Key="k2", Data="v2")
        except Exception as e:
            pass
    except Exception as e:
        pass
    return True
