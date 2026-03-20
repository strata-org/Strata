import servicelib
from datetime import datetime

def use_unlifted_hole() -> bool:
    """Hole (datetime.utcnow()) nested inside kwarg — not lifted before Core."""
    client: Storage = servicelib.connect("storage")
    client.put_item(Bucket="b", Key=str(datetime.utcnow()), Data="val")
    return True
