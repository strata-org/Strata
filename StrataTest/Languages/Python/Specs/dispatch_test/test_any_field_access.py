import servicelib

class Config:
    region: Any
    name: str

    def __init__(self, region: str, name: str) -> None:
        self.region = region
        self.name = name

def access_any_field() -> str:
    """Class with Any-typed field — wrapFieldInAny fails for TCore 'Any'."""
    cfg: Config = Config(region="us-east-1", name="test")
    r: str = cfg.region
    return r
