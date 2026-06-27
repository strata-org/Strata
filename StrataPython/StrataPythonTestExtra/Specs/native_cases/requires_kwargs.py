# A contract lambda binder matching the function's **kwargs parameter must NOT be
# flagged as "unbound" (functionParamNames includes it), and kw["a"] translates.
@requires(lambda kw: kw["a"] >= 0)
def f(**kw: int) -> int:
    ...
