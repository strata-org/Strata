import servicelib

def procedure_as_annotation() -> bool:
    client = servicelib.connect("storage")
    # Storage_put_item is a procedure name, not a type.
    # Using it as a type annotation should NOT create a UserDefined type.
    x: Storage_put_item
    return True
