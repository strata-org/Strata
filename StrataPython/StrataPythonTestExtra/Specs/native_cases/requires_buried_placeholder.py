# A BURIED placeholder: `len("foo")` translates to stringLen(placeholder) with no
# warning, so the top-level node (intGe) is not itself a placeholder. The deep
# containsPlaceholder check must still drop this (with a diagnostic).
@requires(lambda x: len("foo") >= 1)
def f(x: int) -> int:
    ...
