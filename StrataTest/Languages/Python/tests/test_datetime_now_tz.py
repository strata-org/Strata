from datetime import datetime, timezone, timedelta

now: datetime = datetime.now(timezone.utc)
delta: timedelta = timedelta(days=7)
start: datetime = now - delta
assert start <= now
