# OLD.<name> with no matching @snapshot warns.
import icontract


class C:
    x: int

    @icontract.ensure(lambda OLD: OLD.foo >= 0)
    def step(self) -> None:
        ...
