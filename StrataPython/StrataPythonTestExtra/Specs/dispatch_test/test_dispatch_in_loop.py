import servicelib

def loop_connect() -> bool:
    names = ["storage", "messaging"]
    for name in names:
        client = servicelib.connect(name)
    return True
