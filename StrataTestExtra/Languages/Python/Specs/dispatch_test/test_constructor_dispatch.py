def construct_and_call() -> bool:
    store = Storage()
    store.put_item(Bucket="b", Key="k", Data="d")
    return True
