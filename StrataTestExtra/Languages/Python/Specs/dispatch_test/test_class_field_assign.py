import servicelib

class Config:
    def __init__(self, name: str, count: int):
        self.name: str = name
        self.count: int = count

def use_config() -> str:
    cfg: Config = Config("test", 42)
    return cfg.name
