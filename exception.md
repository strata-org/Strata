# Exception Handling Improvements

## Overview

Two gaps remain in exception handling after corpus validation:

1. **Bare raise** — `raise` with no argument inside an `except` handler should
   re-raise the caught exception. Currently emits `unsupported` + `unreachable`.
   26 occurrences across 6 corpus files.

2. **Instruction-level `exceptArgs`** — The IR supports per-instruction exception
   argument snapshots (`NamedInstr.exceptArgs`), but the translator never populates
   them. This means exception handlers see variables from block entry rather than
   from the exact raise point. The spec (PythonSSA.md lines 627-666) documents the
   intended behavior with `undef` padding for unassigned variables.

This plan covers both, using test-driven development.

## Part 1: Bare Raise

### Current behavior

```lean
-- Translate.lean:1029-1037
| .Raise _ ⟨_, exc⟩ _ =>
  match exc with
  | some e =>
    let (excVal, _) ← translateExpr e fwd
    finishBlockWithTerm (.raise excVal) sr
  | none =>
    let _ ← ssaError sr "bare raise not yet supported"
    finishBlockWithTerm .unreachable sr
  return true
```

### Python semantics

`raise` without an argument re-raises the "current exception" — the one bound
by the enclosing `except` clause. It is only valid inside an `except` handler
(or code called from one). At the SSA level, the handler block receives the
exception as a block parameter (`_exc`), so bare raise just needs to emit
`raise %excVal` using that parameter.

### Required change

Track the in-scope exception variable in `BodyCtx`. The handler translation
code (Translate.lean:1328-1383) already binds the exception as `_exc` in the
var environment. During handler body translation, bare `raise` should look up
that variable and emit `raise` with it.

**Option A: Add `excVar : Option SSAVal` to `BodyCtx`.**

When entering a handler body, set `excVar := some excVal`. When translating
`Raise _ none`, look it up. If `none` (bare raise outside a handler), emit
an error.

**Option B: Look up `_exc` in the var environment.**

The handler already binds the exception parameter. Bare raise could call
`lookupVar "_exc"`. This is fragile — depends on the naming convention and
could conflict with user variables named `_exc`.

Recommendation: **Option A.** Explicit state is clearer and doesn't depend on
naming conventions.

### Test plan

#### New test: `t27_bare_raise.py`

```python
def risky():
    raise ValueError("fail")

# Basic bare raise
try:
    risky()
except ValueError:
    raise

# Bare raise with named exception
try:
    risky()
except ValueError as e:
    print(e)
    raise

# Bare raise in bare except
try:
    risky()
except:
    raise

# Bare raise after work in handler
try:
    x = risky()
except ValueError:
    y = 1
    raise
```

#### Expected output: `t27_bare_raise.expected`

Each bare `raise` should emit `raise %N` where `%N` is the handler's exception
parameter (or a value derived from it via block params). The `unsupported` +
`unreachable` pattern should not appear.

Key things to verify:
- Handler's `_exc` parameter is used as the raise operand
- Named exception (`as e`) — the named binding is a rename of `_exc`, raise
  uses the same underlying SSA val
- Bare except (no type filter) — exception routes directly to handler body
- Work before bare raise — instructions before `raise` execute normally, then
  the raise terminates the block

### Implementation steps

1. Write `t27_bare_raise.py` and draft `t27_bare_raise.expected`
2. Add test to `positiveTests` list in `SSATest.lean`
3. Add `excVar : Option SSAVal` field to `BodyCtx`
4. Set `excVar` when entering handler body (both typed and bare handler paths)
5. In `Raise _ none` case: look up `bodyCtx.excVar`, emit `raise excVal`
6. Run tests, iterate on expected output
7. Re-run corpus validation to confirm 26 bare-raise warnings eliminated

## Part 2: Instruction-Level `exceptArgs`

### Current behavior

The translator sets `block.except := some { target := handlerBlock }` on blocks
inside try bodies. But every `NamedInstr` has `exceptArgs := none`. This means
exception handlers receive block-entry values for all variables, regardless of
which instruction raised.

### Spec behavior (PythonSSA.md)

```
block bb_try() [except: bb_handler]:
  %0 = call @do_something()  [exceptArgs: exc, undef("x"), undef("y")]
  %1:x = call @f()           [exceptArgs: exc, %1,         undef("y")]
  %2:y = call @g()           [exceptArgs: exc, %1,         undef("y")]
```

Each raising instruction carries a snapshot of which variables have been assigned
at that point. The handler's block params receive these values — so if `f()`
raises, the handler sees `x = undef`, but if `g()` raises, the handler sees
`x = f()'s result`.

### Design considerations

This is more complex than bare raise because it requires:
- Tracking which instructions can raise (calls, attribute access, subscript)
- Building per-instruction snapshots of the current variable environment
- Matching snapshot values to the handler's block param order

The handler's block params are: `[demand vars...] ++ [_exc]`. The `exceptArgs`
for each instruction must produce values in that same order, substituting `undef`
for variables not yet assigned.

### Test plan

#### Modify existing test: `t07_try_except.py` (or new `t28_except_args.py`)

```python
def f():
    raise ValueError("f failed")

def g():
    raise ValueError("g failed")

# Handler should see x=undef if f() raises, x=f() result if g() raises
try:
    x = f()
    y = g()
except ValueError as e:
    result = x  # x may be undef here depending on which call raised
```

#### Expected output

The try block's instructions should carry `exceptArgs`:
```
bb0() [except: bb1]:
  %1:x.0 = callQualified mod.f []  [exceptArgs: exc, undef("x"), undef("y")]
  %3:y.0 = callQualified mod.g []  [exceptArgs: exc, %1, undef("y")]
  branch bb2(%1, %3)
```

### Implementation steps

1. Write test file and draft expected output
2. Determine which instructions can raise (conservative: all calls, attr, subscript)
3. After emitting each potentially-raising instruction inside a try block, compute
   `exceptArgs` from current var environment against handler's demand vars
4. Populate `NamedInstr.exceptArgs` field
5. Update `SSAFormat` to print `exceptArgs` when present
6. Run tests, iterate

### Deferral note

Part 2 is lower priority than Part 1. Bare raise is a translation gap (produces
incorrect output). Missing `exceptArgs` is a precision gap (produces correct but
less precise output — the handler still works, it just can't distinguish which
instruction raised). Part 2 can be deferred without affecting correctness.

## Sequencing

1. **Part 1 first** — bare raise. Small, self-contained, eliminates 26 corpus
   warnings. Ship as a separate commit.
2. **Part 2 second** — exceptArgs. More complex, can be deferred. Separate commit.
3. **Re-validate corpus** after each part.
