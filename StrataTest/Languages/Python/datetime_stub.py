"""Datetime module stub for Resolution."""

class datetime:
    @staticmethod
    def now() -> 'datetime':
        pass

    @staticmethod
    def strptime(date_string: str, format: str) -> 'datetime':
        pass

class date:
    @staticmethod
    def today() -> 'date':
        pass

def timedelta(days: int = 0, hours: int = 0) -> int:
    pass
