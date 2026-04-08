# Support Classes Without Explicit `__init__`

## Key Decisions
- Fixed in `PythonToLaurel.lean` in the `translateClass` function.
- When a class has no `__init__` method, we synthesize a default one: a `PythonFunctionDecl`
  (so the call site resolver finds it) and a `Procedure` with an `.Opaque` body.
- The synthesized `__init__` takes only `self` (typed as the class's composite type) and
  returns `LaurelResult : Any`, matching the convention of explicit `__init__` methods.

## Root Cause
- `translateClass` collects methods and registers them as `ClassName@methodName` procedures.
- Constructor calls (`n = NoInit()`) always emit `mkInstanceMethodCall className "__init__"`,
  producing a `StaticCall "NoInit@__init__"`.
- Without an `__init__`, no procedure with that name exists → type checker error.

## Patterns Discovered
- Method bodies are currently replaced with `.Opaque [] .none []` anyway (line ~1837),
  so the synthesized default `__init__` just needs the right signature.
- The `compositeType` check at the call site (line ~1044) unconditionally emits `__init__`;
  fixing at the definition site (synthesizing the procedure) is cleaner than guarding every call site.

## Pitfalls
- `missing_init.py` (pre-existing test file) uses `f != None` which triggers a separate
  type-unification bug with composite types — unrelated to the `__init__` issue.
- The `is not None` / `!= None` comparison with composite-typed variables fails even for
  classes that DO have `__init__`. This is a separate issue.

## For Next Agent
- 5 new test files added with `.expected` files: `test_class_no_init`, `test_class_empty`,
  `test_class_no_init_with_method`, `test_class_no_init_multi_field`, `test_class_mixed_init`.
- The `missing_init.py` test still has no `.expected` file due to the `!= None` composite bug.
- Composite-type `!= None` / `is not None` comparison is a known separate issue worth fixing.
