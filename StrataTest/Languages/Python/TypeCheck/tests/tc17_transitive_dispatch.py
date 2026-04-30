import cloudkit

def f():
    db = cloudkit.client("database")
    result = db.query("SELECT 1")
