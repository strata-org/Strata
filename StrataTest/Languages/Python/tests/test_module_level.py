from typing import Dict, Any

data: Dict[str, Any] = {
    "name": "test",
    "version": 1,
    "active": True
}

assert data["name"] == "test"
assert data["version"] == 1

data["status"] = "running"
assert data["status"] == "running"
assert "name" in data
assert "missing" not in data
