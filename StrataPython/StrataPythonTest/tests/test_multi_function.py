import test_helper
from typing import Dict, Any

def create_config(name: str, value: int) -> Dict[str, Any]:
    config: Dict[str, Any] = {"name": name, "value": value, "active": True}
    return config

def validate_config(config: Dict[str, Any]) -> bool:
    if "name" not in config:
        return False
    if "value" not in config:
        return False
    return True

def process_config(name: str, value: int) -> Any:
    config: Dict[str, Any] = create_config(name, value)
    valid: bool = validate_config(config)
    if not valid:
        return None
    return config["value"]

def main():
    result: Any = process_config("test", 100)
    assert result == 100, "process_config should return value"

    test_helper.procedure("foo")

if __name__ == "__main__":
    main()
