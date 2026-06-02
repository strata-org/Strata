# strata-args: --typed-python --check-mode bugFinding --check-level full
# Class fields with native primitive types. Under --typed-python the
# field type lookup returns TInt/TBool/...; reads of `self.balance`
# wrap into Any (so the surrounding Any-bodied method stays
# well-typed), and the fromAny peephole cancels the wrap when the
# consumer is itself a typed operator (e.g. `>=`).
class Account:
    balance: int
    is_open: bool


def deposit(a: Account, amount: int) -> int:
    assert a.balance >= 0
    assert amount >= 0
    return a.balance + amount


def status(a: Account) -> bool:
    return a.is_open
