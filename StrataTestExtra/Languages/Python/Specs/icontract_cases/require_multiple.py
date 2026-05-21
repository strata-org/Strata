# Stacked @require decorators produce multiple preconditions.
import icontract


@icontract.require(lambda a: a >= 0)
@icontract.require(lambda b: b >= 1)
def g(a: int, b: int) -> int:
    ...
