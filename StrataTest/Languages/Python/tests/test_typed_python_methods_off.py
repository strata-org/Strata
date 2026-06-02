# strata-args: --check-mode bugFinding --check-level full
# Default-mode counterpart. Method calls and field reads all go
# through Any.
class Wallet:
    balance: int

    def deposit(self, amount: int) -> int:
        assert amount >= 0
        assert self.balance >= 0
        return self.balance + amount

    def withdraw(self, amount: int) -> int:
        assert amount >= 0
        assert self.balance >= amount
        return self.balance - amount


def use_wallet(w: Wallet, amt: int) -> int:
    assert amt >= 0
    assert amt <= 100
    assert w.balance >= 100
    return w.deposit(amt)
