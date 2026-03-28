# Test: Realistic example combining multiple features
# Modeled after patterns seen in the Kiro corpus

import json
from typing import Optional

class ResourceManager:
    def __init__(self, name: str):
        self.name = name
        self.resources = {}

    def add_resource(self, key: str, value: str) -> bool:
        if key in self.resources:
            return False
        self.resources[key] = value
        return True

    def get_resource(self, key: str) -> Optional[str]:
        if key in self.resources:
            return self.resources[key]
        return None

def process_items(items: list, manager: ResourceManager) -> int:
    count: int = 0
    for item in items:
        try:
            key = item["key"]
            value = item["value"]
            success = manager.add_resource(key, value)
            if success:
                count += 1
        except KeyError as e:
            continue
    return count

mgr = ResourceManager("test")
data = [{"key": "a", "value": "1"}, {"key": "b", "value": "2"}]
total = process_items(data, mgr)
result = mgr.get_resource("a")
