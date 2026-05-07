config: dict = {
    "host": "localhost",
    "port": 8080,
    "debug": True
}

assert config["host"] == "localhost"
assert config["port"] == 8080

config["timeout"] = 30
assert config["timeout"] == 30

assert "host" in config
assert "missing" not in config

nested: dict = {
    "database": {
        "primary": {"host": "db1", "port": 5432},
        "replica": {"host": "db2", "port": 5433}
    }
}

assert nested["database"]["primary"]["host"] == "db1"
assert nested["database"]["replica"]["port"] == 5433

nested["database"]["primary"]["host"] = "db3"
assert nested["database"]["primary"]["host"] == "db3"
