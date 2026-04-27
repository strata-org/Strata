import servicelib

def bad_args() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Wrong="value")
    return True
