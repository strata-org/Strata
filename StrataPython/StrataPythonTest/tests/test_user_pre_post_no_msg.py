# strata-args: --check-mode bugFinding --check-level full
# Two user-written `assert` statements WITHOUT messages on `withdraw`. After
# lowering each becomes a precondition with `summary := none`, which means
# the call-site .Assume both have NO propertySummary and historically
# collapsed to a single `assert(<call-pos>)` label — the path-condition
# tracker emitted a `Label clash detected` warning and `vcResultGroupKey`
# merged the obligations under one entry, hiding one from the report.
# After the per-procedure label tracker fix, the two assumes get distinct
# labels (`assert(N)` and `assert(N)♯1`) and both appear in the report.
def withdraw(balance: int, amount: int) -> int:
    assert balance >= amount
    assert amount > 0
    return balance - amount

def main() -> None:
    new_balance: int = withdraw(100, 30)
