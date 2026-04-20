# strata-args: --check-mode bugFinding --check-level full
import test_helper

class Account:
    def __init__(self, owner: str, balance: int):
        self.owner: str = owner
        self.balance: int = balance

    def get_owner(self) -> str:
        return self.owner

    def get_balance(self) -> int:
        return self.balance

    def set_balance(self, amount: int) -> None:
        self.balance = amount

def main():
    acc: Account = Account("Alice", 100)

    name: str = acc.get_owner()
    assert name == "Alice", "get_owner should return Alice"

    bal: int = acc.get_balance()
    assert bal == 100, "get_balance should return 100"

    acc.set_balance(200)
    bal2: int = acc.get_balance()
    assert bal2 == 200, "set_balance should update balance"

    test_helper.procedure("foo")

if __name__ == "__main__":
    main()
