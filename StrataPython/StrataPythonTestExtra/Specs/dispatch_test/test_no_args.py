import servicelib

def no_args() -> bool:
    client = servicelib.connect("storage")
    client.put_item()
    return True
