# strata-args: --check-mode bugFinding --check-level full
# Default-mode counterpart. Field reads go through Any.
class Account:
    balance: int
    is_open: bool


def deposit(a: Account, amount: int) -> int:
    assert a.balance >= 0
    assert amount >= 0
    return a.balance + amount


def status(a: Account) -> bool:
    return a.is_open
