import servicelib

def conditional_connect(flag: bool) -> bool:
    if flag:
        client = servicelib.connect("storage")
        client.put_item(Bucket="b", Key="k", Data="v")
    else:
        msg = servicelib.connect("messaging")
        msg.send(Topic="t", Body="b")
    return True
