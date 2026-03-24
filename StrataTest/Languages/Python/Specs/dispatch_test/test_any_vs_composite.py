import servicelib

def composite_to_any() -> bool:
    """Service client (Composite after heap param) passed where Any expected."""
    try:
        client: Storage = servicelib.connect("storage")
        client.put_item(Bucket="b", Key="k", Data="d")
        return True
    except Exception as e:
        msg: str = str(e)
        return False
