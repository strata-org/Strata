from datetime import datetime, timedelta

now: datetime = datetime.now()
delta: timedelta = timedelta(days=7)
start: datetime = now - delta
assert start <= now
