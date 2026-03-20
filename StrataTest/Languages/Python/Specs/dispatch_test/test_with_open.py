import servicelib

def use_with_statement() -> bool:
    """with statement on unmodeled context manager — __enter__/__exit__ not found."""
    client: Storage = servicelib.connect("storage")
    result = client.get_item(Bucket="b", Key="k")
    with open("output.json", "w") as f:
        f.write("done")
    return True
