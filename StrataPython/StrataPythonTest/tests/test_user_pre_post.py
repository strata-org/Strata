# strata-args: --check-mode bugFinding --check-level full
# Two user-written preconditions on `withdraw` (the `assert` statements at the
# top of the body). After lowering, each becomes a separate precondition with
# its own message; at the call site `withdraw(100, 30)`, ContractPass emits one
# `.Assume` per precondition, all sharing the call source. The translator's
# per-procedure label tracker disambiguates them so the path-condition
# tracker no longer warns about clashes.
def withdraw(balance: int, amount: int) -> int:
    assert balance >= amount, "insufficient funds"
    assert amount > 0, "amount must be positive"
    return balance - amount

def main() -> None:
    new_balance: int = withdraw(100, 30)
    assert new_balance == 70
