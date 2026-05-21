# @require lambda binder unknown to the function: vacuous-predicate warning.
import icontract


@icontract.require(lambda nope: nope >= 0)
def h(x: int) -> int:
    ...
