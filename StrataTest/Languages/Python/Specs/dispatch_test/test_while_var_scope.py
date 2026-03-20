import servicelib

def while_var_scope() -> str:
    client: Storage = servicelib.connect("storage")
    done: bool = False
    while not done:
        result: Any = client.get_item(Bucket="b", Key="status")
        status: str = result
        if status == "done":
            done = True
    return status
