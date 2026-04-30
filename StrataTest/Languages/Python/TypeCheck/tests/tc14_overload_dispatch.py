import cloudkit

def f():
    db_client = cloudkit.client("database")
    cache_client = cloudkit.client("cache")
