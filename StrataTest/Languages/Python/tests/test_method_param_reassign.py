class Validator:
    def __init__(self):
        pass

    def process(self, account_id: Any) -> Any:
        """Reassigning a method parameter inside try must not produce
        a duplicate 'var account_id' declaration in the Laurel output."""
        try:
            account_id = account_id
        except Exception as e:
            return False
        return account_id
