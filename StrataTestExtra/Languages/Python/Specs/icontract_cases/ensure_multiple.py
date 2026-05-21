# Stacked @ensure decorators produce multiple postconditions.
import icontract


@icontract.ensure(lambda result: result >= 0)
@icontract.ensure(lambda result: result >= 1)
def f() -> int:
    ...
