"""Banking with safe withdrawals."""
import icontract


@icontract.require(lambda a: a >= 0)
@icontract.require(lambda b: b >= 0)
@icontract.ensure(lambda a, b, result: result >= 0)
@icontract.ensure(lambda a, result: result <= a)
@icontract.ensure(lambda b, result: result >= b)
def cap(a: int, b: int) -> int:
    """Return the smaller of a and b."""
    if a <= b:
        return a
    return b


@icontract.require(lambda balance: balance >= 0)
@icontract.require(lambda amount: amount >= 0)
@icontract.ensure(lambda result: result >= 0)
def withdraw(balance: int, amount: int) -> int:
    """Withdraw at most what's available."""
    safe_amount = cap(amount, balance)
    return balance - safe_amount


@icontract.ensure(lambda result: result >= 0)
def test_good() -> int:
    return withdraw(100, 50)


@icontract.ensure(lambda result: result >= 0)
def test_good2() -> int:
    return withdraw(100, 200)


@icontract.ensure(lambda result: result >= 0)
def test_bad() -> int:
    return withdraw(-10, 5)
