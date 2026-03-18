import servicelib

def process() -> bool:
    store = servicelib.connect("storage")
    msg = servicelib.connect("messaging")
    store.put_item(Bucket="b", Key="k", Data="value")
    msg.send(Topic="notifications", Body="stored")
    return True
