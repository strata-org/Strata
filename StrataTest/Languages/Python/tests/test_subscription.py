company = {
    "engineering": {
        "backend": {"lead": "Alice", "members": ["David", "Eve", "Frank"]},
        "frontend": {"lead": "Bob", "members": ["Charlie", "Diana", "Frank"]}
    },
    "sales": {
        "north": {"lead": "Charlie", "members": 4},
        "south": {"lead": "Diana", "members": 6}
    }
}

company["engineering"]["frontend"]["members"][0] = "Peter"

company["management"] = {"CEO": "Grant"}

assert company["engineering"]["frontend"]["members"][0] == "Peter"

assert "Frank" in company["engineering"]["frontend"]["members"]

assert "management" in company

