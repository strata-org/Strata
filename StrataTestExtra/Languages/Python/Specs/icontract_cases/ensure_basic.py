# Single @ensure binding `result`.
import icontract


@icontract.ensure(lambda result: result >= 0)
def f() -> int:
    ...
