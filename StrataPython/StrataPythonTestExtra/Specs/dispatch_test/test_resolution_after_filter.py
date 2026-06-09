import servicelib

def lookup() -> str:
    db = servicelib.connect("database")
    result = db.query(Table="users", Key="alice")
    return result
