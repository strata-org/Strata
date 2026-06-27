# A bare string-literal predicate body is unsupported: dropped with a warning
# (no precondition), not stored as a content-free placeholder.
@requires(lambda x: "oops")
def f(x: int) -> int:
    ...
