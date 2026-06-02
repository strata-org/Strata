# strata-args: --typed-python --check-mode bugFinding --check-level full
# Methods on a typed receiver. `self.balance` reads a native int field;
# calls between methods on the same class use the Any-boundary shim
# so the method body stays Any-internal but native fields and operators
# fire when types line up.
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
