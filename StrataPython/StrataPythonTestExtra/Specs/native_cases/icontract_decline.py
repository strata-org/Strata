# Qualified @icontract.requires must NOT be absorbed as a native precondition
# (the native scheme only recognizes unqualified markers). It falls through to
# the existing decorator-value path, which does not recognize it.
@icontract.requires(lambda x: x >= 0)
def f(x: int) -> int:
    ...
