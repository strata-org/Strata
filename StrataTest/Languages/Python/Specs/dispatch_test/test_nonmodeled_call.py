import servicelib
from datetime import datetime, timezone

def use_nonmodeled_call() -> bool:
    """Non-modeled function call (datetime.now) produces arity mismatch."""
    now: datetime = datetime.now(timezone.utc)
    client: Storage = servicelib.connect("storage")
    client.put_item(Bucket="b", Key="ts", Data="val")
    return True
