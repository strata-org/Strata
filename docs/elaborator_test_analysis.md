# Elaborator Test Divergence Analysis

Comparing old pipeline (`pyAnalyzeLaurel`) vs new pipeline (`pyAnalyzeV2`).
55 tests total. 14 SAME, 2 IMPROVED, 36 DIFF, 2 REGRESSION.

## Root Causes

### A. Import resolution failure
The new Resolution pass doesn't load procedure specifications from imported modules.
When `from datetime import datetime, timedelta` or `import re` appears, the old pipeline
loads full procedure declarations (with requires/ensures) for `datetime_now`, `timedelta_func`,
`re_fullmatch`, `re_match`, `re_search`, etc. The new pipeline marks these as unresolved,
and Translation emits havocs.

### B. Same-file procedure call resolution failure
Even for procedures defined in the same file, the new Resolution sometimes fails to
resolve calls. `test_helper_procedure` defined at the top of a file, called later —
the old pipeline resolves it; the new one emits a havoc.

### C. `new` expansion removes Core translator pattern
The old pipeline emits `my_buf := new CircularBuffer; CircularBuffer@__init__(my_buf, args)`
which the Laurel-to-Core translator recognizes and generates `callElimAssert_requires` VCs for.
The new elaborator correctly expands this to `increment($heap); MkComposite(...); __init__(...)` —
explicit heap semantics per FGCBV. The Core translator doesn't recognize this expanded form.

### D. `propertySummary` / `ensures` not carried through
The old pipeline copies user-written `requires` and `ensures` annotations onto procedure
declarations, with `propertySummary` labels. The new pipeline emits procedure declarations
without these annotations. This causes all precondition-checking VCs and return-type
constraint VCs to disappear.

### E. Type erasure too aggressive (DictStrAny -> Composite)
The new elaborator erases `DictStrAny` annotations to `Composite` (because user-defined types
erase to Composite). This inserts `from_Composite(...)`/`Any..as_Composite!(...)` wrapping
around dict operations that cvc5 can't see through, making previously-provable asserts go unknown.

---

## Per-Test Analysis

### test_arithmetic — SAME
No divergence.

### test_augmented_assign — SAME
No divergence.

### test_boolean_logic — SAME
No divergence.

### test_break_continue — DIFF (more principled)
**Old:** 11 procs, 8 ensures. Each function has `ensures Any..isfrom_None(LaurelResult)`.
Body starts with `LaurelResult := from_None(); var nullcall_ret := from_None(); var maybe_except := NoError()`.

**New:** 7 procs, 3 ensures. Functions return `(LaurelResult: void, ...)`. No boilerplate.
Body is just the logic.

**Verdict: More principled.** The old `ensures Any..isfrom_None(LaurelResult)` is a tautology —
it initializes LaurelResult to from_None and never changes it. The new pipeline correctly types
the return as void and doesn't emit a trivially-true ensures. The missing "Return type constraint"
VCs were vacuous. Loop logic is identical.

### test_class_decl — DIFF (more principled, downstream gap)
**Old:** `my_buf := new CircularBuffer; CircularBuffer@__init__(my_buf, from_int(5))`.
`__init__` has `requires true`. Core translator emits `callElimAssert_requires_4`.

**New:** `heap$0 := increment($heap); my_buf := MkComposite(Heap..nextReference!($heap), CircularBuffer_TypeTag()); CircularBuffer@__init__(from_Composite(my_buf), 5)`.

**Verdict: More principled.** Explicit heap allocation is the correct FGCBV semantics. The old
`new` keyword hides what's actually happening. Lost VC (`callElimAssert_requires_4`) is because
the Core translator pattern-matches on `new` which no longer appears. Root cause C.

### test_class_field_any — DIFF (more principled, downstream gap)
**Old:** 7 procs, `new` present, `callElimAssert_requires_3` emitted.
**New:** 2 procs, `new` expanded to heap ops.

**Verdict: More principled.** Same as test_class_decl — root cause C. The lost VC was for the
`new` + `__init__` pattern. Both old and new fail to prove `assert(133)` (inconclusive in both).

### test_class_field_init — DIFF (more principled, downstream gap)
**Old:** 9 procs, `new` present, `callElimAssert_requires_5` + `postcondition`.
**New:** 5 procs, `new` expanded.

**Verdict: More principled.** Root cause C. Same pattern — heap expansion removes `new` pattern.

### test_class_field_use — DIFF (more principled, downstream gap)
**Old:** 10 procs, `new` present, `callElimAssert_requires_8` + `postcondition`.
**New:** 6 procs, `new` expanded.

**Verdict: More principled.** Root cause C. The assert `assert(301)` is inconclusive in BOTH
pipelines — the lost VCs were only for the class instantiation pattern.

### test_class_methods — DIFF (wrong — specs + resolution)
**Old:** 12 procs, req 8, `callElimAssert_requires_12`, `Origin_test_helper_procedure_Requires` checked.
**New:** 7 procs, req 1. Method calls (`Account@__init__`, `Account@get_owner`, `Account@get_balance`,
`Account@set_balance`) ARE correctly resolved and called with heap threading. But
`test_helper_procedure(from_str("foo"), from_None())` at end of main becomes `havoc$16`.

**Verdict: WRONG.** Root cause B (same-file `test_helper_procedure` not resolved — it's defined
at module level but Resolution can't find it) PLUS root cause C (`new` expanded — correct)
PLUS root cause D (no requires/ensures on any procedure). The method calls work; the standalone
procedure call and all specs are lost.

### test_class_with_methods — DIFF (wrong — specs + resolution)
**Old:** 12 procs, req 8.
**New:** 7 procs, req 1. Only 2 actual havocs: `havoc$0()` for `__name__` (standard) and
`havoc$16` for `test_helper_procedure` (unresolved). All `<?>` are output var declarations.

**Verdict: WRONG.** Same pattern as test_class_methods. Method calls on class instances are
correctly resolved. `test_helper_procedure` standalone call becomes havoc (root cause B).
All specs missing (root cause D). `new` correctly expanded (root cause C, principled).

### test_comparisons — SAME
No divergence.

### test_composite_return — DIFF (more principled, downstream gap)
**Old:** 8 procs, `new` present, `callElimAssert_requires_3` + `postcondition`.
**New:** 3 procs, no `new`, no requires, no ensures.

**Verdict: More principled.** Root cause C. The old pipeline emitted these VCs from the `new`
pattern; the new correctly expands. No functional logic difference.

### test_control_flow — SAME
No divergence.

### test_datetime — DIFF (wrong)
**Old:** 7 procs including `datetime_now()` and `timedelta_func(days, hours)` with full
requires/ensures. `now := datetime_now()` gives cvc5 `ensures Any..isfrom_datetime(ret)`.
**New:** 1 proc. All datetime/timedelta calls become havocs. 0 ensures.

**Verdict: WRONG.** Root cause A. `from datetime import datetime, timedelta` not resolved.
The entire test becomes meaningless — all asserts go unknown because cvc5 has no information
about what `now` or `delta` contain.

### test_default_params — DIFF (wrong — specs only)
**Old:** 7 procs, req 5, ens 3, specs 6. `greet` has `requires Any..isfrom_str(name)` + 
`ensures Any..isfrom_str(LaurelResult)`. `power` same pattern.
**New:** 5 procs, req 1, ens 1, specs 0. `greet` and `power` exist with correct bodies.
Calls `greet("Alice", "Hello")` and `power(3, 2)` are correctly resolved. Only havoc is
the standard `havoc$0()` for `__name__`. No resolution failures.

**Verdict: WRONG.** Root cause D only (NOT A). All calls resolve correctly. The user-written
type constraints and return type ensures are not propagated to output declarations.

### test_dict_operations — DIFF (more principled, less precise)
**Old:** `config: Core(Any)`. Direct `Any_get(config, ...)`.
**New:** `config: Core(Composite)`. `Any_get(from_Composite(config), ...)` with wrapping.

Both have identical structure, same function calls, same asserts. Same requires/ensures counts.
But the new pipeline types `config` as `Composite` (because `dict` annotation erases to it),
then wraps every access in `from_Composite(...)`. cvc5 can't simplify
`Any_get(from_Composite(Any..as_Composite!(from_DictStrAny(...))), key)` because `from_Composite`
and `as_Composite!` are opaque.

**Verdict: More principled but less precise.** Root cause E. The type erasure is technically
correct (dict is a user-defined type → Composite) but produces opaque wrapping that blocks
verification. Fix: don't erase DictStrAny to Composite in `eraseType`.

### test_for_loop — DIFF (more principled)
**Old:** 7 procs, 13 havocs. **New:** 4 procs, 6 havocs.

**Verdict: More principled.** New has FEWER havocs (6 vs 13). Same requires/ensures. The new
pipeline is actually better here — fewer opaque values. The difference is structural (no
boilerplate procs, no `nullcall_ret`/`maybe_except` initialization).

### test_fstrings — SAME
No divergence.

### test_func_input_type_constraints — DIFF (wrong — specs only)
**Old:** 10 procs, req 14, ens 7, specs 10. Full type constraints on function inputs.
**New:** 8 procs, req 7, ens 4, specs 0. All procedures (`Mul`, `Sum`, `List_Dict_index`) exist
with correct bodies. Zero havocs. Calls are correctly resolved.

**Verdict: WRONG.** Root cause D. User-written type constraints (`requires Any..isfrom_str(x)`)
on function parameters are not propagated to the output procedure declarations. The specs
(propertySummary) are entirely lost. This means the verifier can't check type safety at
call sites.

### test_function_def_calls — DIFF (wrong)
**Old:** `test_helper_procedure` with 3 requires, `my_f` with 1 requires. Call site checks generated.
**New:** `test_helper_procedure` doesn't exist. `my_f` body is a single havoc.

**Verdict: WRONG.** Root cause B. Same-file procedure `test_helper_procedure` not resolved.
The call inside `my_f` becomes a havoc. All precondition VCs lost.

### test_if_elif — DIFF (wrong — specs only)
**Old:** `classify` has `requires Any..isfrom_int(x)` + `ensures Any..isfrom_str(LaurelResult)`.
Call `classify(PNeg(from_int(5)))` is resolved. Same in new: `classify(Any..as_int!(PNeg(from_int(5))))`.

**New:** `classify` exists, calls are resolved correctly. But no `requires`/`ensures` on it.
cvc5 can't infer that the return is a string, so downstream asserts go unknown.

**Verdict: WRONG.** Root cause D only (NOT B — I was wrong before). Calls are resolved. Specs not propagated.

### test_ifexpr — DIFF (naming only)
**Old:** `set_result_calls_Any_to_bool_0`. **New:** `ite_cond_calls_Any_to_bool_0`.

**Verdict: Fine.** Same VC, different name. The old pipeline names it after the assignment target,
the new names it after the if-expression condition. Semantically identical.

### test_list_slice — SAME
No divergence.

### test_list — SAME
No divergence.

### test_loops — DIFF (more principled)
**Old:** 8 procs, req 8, ens 4, 13 havocs. **New:** 5 procs, req 8, ens 4, 2 havocs.

**Verdict: More principled.** Same requires/ensures counts. New has FEWER havocs (2 vs 13)
and fewer procs (no boilerplate). The verification results should be equivalent or better.

### test_method_call_with_kwargs — DIFF (more principled, downstream gap)
**Old:** 8 procs, `new` present, `callElimAssert_requires_6`.
**New:** 3 procs, no `new`.

**Verdict: More principled.** Root cause C. Same as other class tests — `new` expanded.

### test_method_param_reassign — SAME
No divergence.

### test_missing_models — DIFF (wrong — import resolution + specs)
**Old:** 9 procs, req 9, ens 5, specs 4. User procs (`math_stuff`, `string_stuff` etc.) present.
**New:** 6 procs, req 6, ens 4, specs 0. No user procs — they use imported types/calls
that aren't resolved. `foo := havoc$0` (class instantiation), `response := havoc$1` (method call).

**Verdict: WRONG.** Root causes A+B+D. The test uses `from foo import Foo` and calls methods
on imported class instances. Resolution doesn't load the import. Plus specs not propagated.

### test_module_level — SAME
No divergence.

### test_multi_function — DIFF (wrong — specs only)
**Old:** 12 procs, req 16, ens 7, specs 11.
**New:** 9 procs, req 8, ens 4, specs 0. `create_config`, `validate_config`, `process_config`
all present as procedures with correct bodies. Calls between them are resolved.

**Verdict: WRONG.** Root cause D only (NOT B). All same-file procedures are resolved.
The requires/ensures/propertySummary annotations are not propagated to the output.

### test_multiple_except — DIFF (more principled)
**Old:** 7 procs, 9 havocs. **New:** 3 procs, 4 havocs. Same req/ens.

**Verdict: More principled.** Fewer procs, fewer havocs, same constraints. The new pipeline
produces tighter output.

### test_nested_calls — DIFF (wrong — specs only)
**Old:** `double` has `requires Any..isfrom_int(x)` + `ensures Any..isfrom_int(LaurelResult)`.
`add_one` same. Call `double(3)`, `add_one(a)` etc. correctly resolved in both.

**New:** `double($in_x: int)` and `add_one($in_x: int)` exist. Calls are `double(3)`,
`add_one(a)` — correctly resolved, NOT havocs. But no requires/ensures.

**Verdict: WRONG.** Root cause D only (NOT B — I was wrong before). All calls resolve
correctly. The issue is purely that specs are not propagated to output declarations.

### test_optional_param_default — DIFF (wrong)
**Old:** 6 procs, req 5, ens 3. `timedelta_func` present with requires.
**New:** 3 procs, req 1, ens 1. No `timedelta_func`.

**Verdict: WRONG.** Root cause A. Import not resolved. `timedelta` calls become havocs.

### test_pin_any — DIFF (more principled)
**Old:** 5 procs, 1 havoc. **New:** 2 procs, 0 havocs. Same req.

**Verdict: More principled.** Fewer procs, zero havocs. Cleaner output.

### test_power — SAME
No divergence.

### test_precondition_verification — DIFF (wrong)
**Old:** 6 procs, req 4, `Origin_test_helper_procedure_Requires` checked at call sites.
**New:** 3 procs, req 1, +3 havocs.

**Verdict: WRONG.** Root cause B. `test_helper_procedure` not resolved. Its preconditions
never get checked at call sites.

### test_procedure_in_assert — DIFF (wrong)
**Old:** 6 procs, req 5, ens 3. `timedelta_func` present.
**New:** 3 procs, req 1, ens 1.

**Verdict: WRONG.** Root cause A. Import not resolved.

### test_regex_negative — DIFF (wrong)
**Old:** 5 procs, req 5, 5 havocs. **New:** 3 procs, req 1, 54 havocs.

**Verdict: WRONG.** Root cause A. `import re` not resolved. Every `re.fullmatch`/`re.search`
call (there are many) becomes a havoc. 5 → 54 havocs.

### test_regex_positive — DIFF (wrong)
**Old:** 5 procs, req 5, 4 havocs. **New:** 3 procs, req 1, 288 havocs.

**Verdict: WRONG.** Root cause A. Same as regex_negative but bigger test. 4 → 288 havocs.
Every regex call is a havoc.

### test_return_types — DIFF (wrong — specs only)
**Old:** 10 procs, req 3, ens 6, specs 7. Each function has `ensures` for return type.
**New:** 8 procs, req 1, ens 1, specs 0. All functions (`get_number`, `get_greeting`,
`get_flag`, `get_nothing`, `add`) exist with correct bodies. Only havoc is `havoc$0()` for `__name__`.

**Verdict: WRONG.** Root cause D only (NOT B). All procedures resolved. Return type ensures
and type constraint requires not propagated.

### test_strings — SAME
No divergence.

### test_subscription — SAME
No divergence.

### test_timedelta_expr — DIFF (wrong)
**Old:** 6 procs, `timedelta_func` with requires/ensures. `now := datetime_now()`.
**New:** 1 proc. Both calls are havocs.

**Verdict: WRONG.** Root cause A. Import not resolved.

### test_try_except_scoping — DIFF (more principled, duplicate emission bug)
**Old:** 7 procs, 6 VCs total. **New:** 3 procs, 27 VCs (same asserts repeated many times).

**Verdict: More principled structure** (same try/except logic, no boilerplate) **BUT has a
duplicate emission bug.** The same `assert(355)` check is emitted 8+ times. This is a
Translation or elaboration bug where try/except block scoping causes repeated VC generation.
Not an architectural problem — just a bug in how labeled blocks are duplicated.

### test_try_except — DIFF (more principled)
**Old:** 7 procs. **New:** 3 procs. Same req.

**Verdict: More principled.** Fewer procs, same constraints. Try/except structure preserved.

### test_unsupported_config — IMPROVED (internal_error -> pass)
Old pipeline crashed. New pipeline succeeds.

### test_user_error_metadata — IMPROVED (user_error -> pass)
Old pipeline reported a user error. New pipeline succeeds.

### test_variable_in_nested_block — SAME
No divergence.

### test_variable_reassign — DIFF (more principled)
**Old:** 5 procs, 6 havocs. **New:** 3 procs, 4 havocs. Same req/ens.

**Verdict: More principled.** Fewer havocs, fewer boilerplate procs.

### test_while_loop — DIFF (more principled)
**Old:** 7 procs, ens 4, 6 havocs. **New:** 4 procs, ens 1, 0 havocs.

**Verdict: More principled.** Zero havocs vs 6. Fewer boilerplate ensures (return type
constraints that were tautologies). Core loop logic identical.

### test_with_statement — DIFF (more principled + downstream gap)
**Old:** 13 procs, `new` x4, req 5, 12 `<?>`.
**New:** 8 procs, no `new`, req 1, 35 `<?>` (all are output var declarations for effectful calls, not unresolved).

`Resource@__init__`, `Resource@__enter__`, `Resource@__exit__`, `Resource@get_value` are all
present in new output. The `with` statement is correctly desugared into `__enter__`/`__exit__`
calls with explicit heap threading. Zero actual havocs in the new output.

The +23 `<?>` are output variable declarations: every `($heap$N, LaurelResult$N, maybe_except$N) := call(...)` 
requires declaring those 3 outputs first. This is the correct elaboration calling convention.

**Verdict: More principled.** Root causes C (new expanded, correct) + D (specs not propagated).
NOT import resolution failure — all calls resolve correctly.

### test_foo_client_folder — REGRESSION (pass -> internal_error)
**Old:** Passes with VCs.
**New:** `Cannot infer the type of this operation: $field.__name__` — type checking error.

The elaborator's `synthValueFieldSelect` can't resolve `__name__` as a field on any class.
`resolveFieldOwner` returns `none`. The old pipeline handled this differently (either through
a different resolution path or by not attempting field-level elaboration on dunder attributes).

**Verdict: REGRESSION.** Bug in elaboration: dunder attributes (`__name__`, `__class__`, etc.)
on objects don't belong to any class in `classFields`. Need a fallback that doesn't crash.

### test_invalid_client_type — REGRESSION (pass -> internal_error)
Same root cause as test_foo_client_folder — `$field.__name__` or similar dunder attribute
access that the elaborator can't resolve.

**Verdict: REGRESSION.** Same fix needed.

### test_with_void_enter — DIFF (more principled + downstream gap)
**Old:** 10 procs, `new` present, `callElimAssert_requires_8/5/2`, `postcondition`.
**New:** 4 procs, no `new`.

**Verdict: More principled.** Root cause C. `new` correctly expanded. Lost VCs are from the
Core translator not recognizing the expanded form.

---

## Summary Table

| Verdict | Count | Tests |
|---------|-------|-------|
| SAME | 14 | arithmetic, augmented_assign, boolean_logic, comparisons, control_flow, fstrings, list_slice, list, method_param_reassign, module_level, power, strings, subscription, variable_in_nested_block |
| More principled | 13 | break_continue, class_decl, class_field_any, class_field_init, class_field_use, composite_return, for_loop, loops, method_call_with_kwargs, multiple_except, pin_any, variable_reassign, while_loop |
| Naming difference only | 1 | ifexpr |
| More principled + downstream gap | 3 | with_void_enter, with_statement, try_except |
| More principled + less precise | 1 | dict_operations |
| More principled + dup bug | 1 | try_except_scoping |
| WRONG (import resolution) | 6 | datetime, timedelta_expr, regex_positive, regex_negative, optional_param_default, procedure_in_assert |
| WRONG (same-file resolution) | 2 | function_def_calls, precondition_verification |
| WRONG (specs not propagated) | 8 | default_params, func_input_type_constraints, return_types, if_elif, nested_calls, multi_function, class_methods, class_with_methods |
| WRONG (multiple causes) | 1 | missing_models (A+B+D) |
| IMPROVED | 2 | unsupported_config, user_error_metadata |
| REGRESSION (internal error) | 2 | foo_client_folder, invalid_client_type |

Note: class_methods and class_with_methods have both same-file resolution failure
(for `test_helper_procedure`) AND spec propagation failure. They're categorized under
specs because that's the dominant issue — the resolution failure affects only one call
at the end of main.

## Priority Fixes

1. **Spec propagation** (9 tests, highest impact): The new pipeline produces correct procedure
   bodies but strips all `requires`/`ensures`/`propertySummary` annotations. This is the single
   largest source of verification precision loss. These specs come from Python type annotations
   and user-written preconditions — the old pipeline's Translation pass emits them. The new
   Translation or Elaboration drops them. Fix: ensure `fullElaborate` preserves
   `preconditions`/`determinism`/output specs from the input Laurel procedures.

2. **Import resolution** (6 tests): Load module procedure specs when processing `import` /
   `from ... import`. Without this, all calls to imported functions become havocs.

3. **Same-file procedure resolution** (3 tests): `test_helper_procedure` defined at module level
   can't be resolved when called from within functions. Resolution likely processes function
   bodies before all top-level defs are registered.

4. **DictStrAny erasure** (1 test): Don't erase `DictStrAny` to `Composite` in `eraseType`.
   Keep it as `DictStrAny`. The round-trip `from_Composite(Any..as_Composite!(...))` is opaque to cvc5.

5. **Try/except duplication** (1 test): Fix duplicate VC emission in labeled block handling.

6. **Core translator pattern** (nice-to-have): Teach the Core translator to emit
   `callElimAssert_requires` for the expanded `increment + MkComposite + __init__` pattern.
   Not required for soundness.
