# PythonSSA Reference Manual

## Overview

PythonSSA is an SSA (Static Single Assignment) intermediate representation for Python
programs. It translates Python source code (via the DDM AST) into a block-based IR
suitable for static analysis, particularly variable initialization analysis and
control flow reasoning.

### Design Goals

- **Precise variable tracking**: SSA form makes every assignment a unique definition,
  enabling exact reasoning about which value a variable holds at any program point.
- **Explicit control flow**: All implicit Python control flow (short-circuit evaluation,
  exception handling, context managers, iteration protocols) is made explicit as
  block-level branches.
- **Faithful semantics**: Desugaring preserves Python's evaluation order, short-circuit
  behavior, and exception semantics. Optimization passes may reconstruct higher-level
  constructs later.
- **Analyzability over completeness**: The IR targets the subset of Python that appears
  in real-world AWS service scripts (the primary corpus), not the full language.

### Scope

**In scope** (46/52 corpus files covered):
- Assignments: `Assign`, `AnnAssign`, `AugAssign`
- Control flow: `If`, `While`, `For`, `Break`, `Continue`, `Return`
- Functions: `FunctionDef`, `Call` (positional + keyword args)
- Exception handling: `Try`/`except`/`finally`, `Raise`
- Context managers: `With`
- Classes: `ClassDef` (methods, `__init__`, class-level assignments)
- Imports: `Import`, `ImportFrom` (resolved to qualified names)
- Expressions: `BinOp`, `UnaryOp`, `Compare`, `BoolOp` (short-circuit), `IfExp`
- Data structures: `Dict`, `List`, `Tuple`, `Subscript`, `Slice`
- Strings: f-strings (`JoinedStr`, `FormattedValue`)
- Attribute access: `Attribute`
- Type annotations: preserved as `Option PyType` on SSA values

**Out of scope**:
- Comprehensions: `ListComp`, `DictComp`, `SetComp`, `GeneratorExp`
- Async: `AsyncFor`, `AsyncFunctionDef`, `AsyncWith`, `Await`
- Advanced: `Lambda`, `Yield`, `YieldFrom`, `NamedExpr` (walrus)
- Rare: `Global`, `Nonlocal`, `Delete`, `Match`, `TypeAlias`, `TryStar`
- Dynamic: `eval`, `exec`, dynamic attribute manipulation
- Starred expressions: `*args` unpacking in assignments

---

## Module Structure

A PythonSSA module is a flat list of functions:

```
module "example":
  func @module_init():       -- top-level code (imports, assignments)
    ...
  func @MyClass_init():      -- class body execution
    ...
  func MyClass.__init__(self: MyClass):
    ...
  func MyClass.method(self: MyClass, x: int):
    ...
  func my_func(x: int) -> str:
    ...
```

### Naming Conventions

- **`@module_init`**: Module-level code (imports, top-level assignments, class
  instantiation calls). The `@` prefix is not a legal Python identifier, preventing
  name collisions.
- **`@ClassName_init`**: Class body execution (class-level assignments, decorator
  evaluation). Called from `@module_init`.
- **`ClassName.method`**: Instance methods with explicit `self` parameter.
- **`func_name`**: Module-level functions.

---

## Type System

### PyType

SSA values carry optional type annotations from the Python source. These are
informational — the IR is single-sorted and does not enforce types.

```
PyType ::=
  -- Primitives
  | any | str | int | bool | float | none | bytes | object
  -- Containers
  | list(PyType)                      -- list[X], Sequence[X]
  | dict(PyType, PyType)              -- dict[K,V], Mapping[K,V]
  | set(PyType)                       -- set[X]
  | tuple(PyType, ...)                -- Tuple[X, Y, ...]
  -- Combinators
  | optional(PyType)                  -- Optional[X]
  | union(PyType, ...)                -- Union[X, Y] or X | Y
  -- Structural
  | typedDict(OrderedMap, total)      -- TypedDict with field names/types
  -- Literal
  | literal(LiteralValue, ...)        -- Literal["a", 1, True]
  -- Nominal
  | named(String)                     -- Logger, BytesIO, S3, RDS, etc.
```

`OrderedMap` is backed by `Array B` + `HashMap A Nat` for O(1) positional
and keyed access. Used for TypedDict fields.

### LiteralValue

```
LiteralValue ::= intVal(Int) | strVal(String) | boolVal(Bool)
```

---

## SSA Value Model

### SSAVal

An SSA value reference. IDs are unique within a block — instructions in different
blocks may reuse the same ID. Use `(BlockId, SSAVal)` for a function-unique reference
(no two blocks in the same function share the same `(BlockId, SSAVal)` pair).

```
SSAVal ::= %<id>            -- e.g., %0, %1, %2
```

### SSAName

Human-readable name for debugging output. The base is the source-level variable name
(if any) and the suffix distinguishes SSA versions.

```
SSAName ::= <base>.<suffix>  -- e.g., x.0, x.1, iter.0, _tmp.3
```

Each block carries an `Array SSAName` mapping `SSAVal.id` to its name.

### BlockId

A block label. IDs are unique within a function.

```
BlockId ::= bb<id>           -- e.g., bb0, bb1, bb2
```

### undef

`undef` represents "this variable has not been assigned on this control flow path."
It is purely a control-flow concept for tracking variable initialization.

The `undef` instruction takes the variable name it represents:

```
%0:x = undef("x")
```

This carries enough information to produce a precise error message:
`NameError: name 'x' is not defined`. The name parameter is the source-level
Python identifier that would trigger the `NameError` if read.

**Restrictions:**
- `undef` MUST NOT be stored inside data structures (dicts, lists, tuples).
- `undef` MUST NOT be passed to calls, operators, or data structure constructors.
- The ONLY valid consumer of a possibly-undef value is `isDefined`.
- Any other use of an `undef` value corresponds to a Python
  `NameError: name '<name>' is not defined`.

---

## Instructions

Instructions are non-terminal operations. Each defines exactly one SSA value.
A block contains a sequence of instructions followed by a terminator.

**Raising convention**: Blocks have one entry and multiple exits. Any instruction that
may raise an exception (calls, operators, subscript access, etc.) is an implicit exit
point — if it raises, control jumps to the block's exception handler; if it succeeds,
execution continues to the next instruction or terminator. A single block may contain
multiple raising instructions.

Each raising instruction carries an `exceptArgs` field — the list of SSA values to
pass to the handler block if that specific instruction raises. This provides
**instruction-level precision**: the handler knows exactly which variables were
defined at the point of exception, without requiring block splitting.

```
block bb1(%x) [except: bb_handler]:
  %0 = call @f()          [exceptArgs: undef("y"), %exc]
  %1 = call @g(%0)        [exceptArgs: %0, %exc]
  branch bb2(%0, %1)

block bb_handler(%y, %exc):
  ...
```

If `@f()` raises, the handler receives `(undef("y"), exc)`. If `@g()` raises, the
handler receives `(%0, exc)` where `%0` is `f()`'s result. Non-raising instructions
have no `exceptArgs`.

### Constants (never raise)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `intLit(v)` | Int value | Integer constant |
| `floatLit(v)` | Float value | Float constant (stored as String for precision) |
| `strLit(v)` | Str value | String constant |
| `boolLit(v)` | Bool value | `True` or `False` |
| `noneLit` | None value | Python `None` |
| `bytesLit(v)` | Bytes value | Bytes constant (stored as String) |

### Control Flow Helpers (never raise)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `undef(name)` | Undef marker | "Variable `name` not assigned on this path" (see undef section) |
| `isDefined(val)` | Bool | Tests whether `val` is defined (not undef) |
| `copy(src)` | Copy of `src` | SSA rename at merge points |

### Calls (potentially raising)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `call(func, args)` | Return value | Call an SSA value as a function |
| `callQualified(module, method, args)` | Return value | Call a fully qualified function (e.g., `boto3.client`) |
| `attr(obj, name)` | Attribute value | `obj.name` (getattr) |
| `setAttr(obj, name, val)` | Updated obj | `obj.name = val` (setattr) |

`CallArg` is either `positional(val)` or `keyword(name, val)`.

### Operators (potentially raising)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `binOp(op, lhs, rhs)` | Result | Binary operation (add, sub, mult, div, floorDiv, mod, pow) |
| `unaryOp(op, operand)` | Result | Unary operation (not, uSub) |
| `compareOp(op, lhs, rhs)` | Bool | Comparison (eq, notEq, lt, ltE, gt, gtE, is, isNot, in, notIn) |

Note: `BoolOp` (`and`/`or`) is not an instruction — it desugars to `condBranch`
for faithful short-circuit semantics.

### Data Structures (potentially raising for access operations)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `mkDict(keys, vals)` | Dict value | Construct a dictionary |
| `mkList(elems)` | List value | Construct a list |
| `mkTuple(elems)` | Tuple value | Construct a tuple |
| `getItem(obj, key)` | Element value | `obj[key]` (can raise KeyError/IndexError) |
| `setItem(obj, key, val)` | Updated obj | `obj[key] = val` |
| `getSlice(obj, lo, hi, step)` | Slice result | `obj[lo:hi:step]` (lo/hi/step are optional) |

### Strings (f-string support)

| Instruction | Produces | Description |
|-------------|----------|-------------|
| `fmtValue(val)` | String | Call `__format__` on val (can raise) |
| `strConcat(parts)` | String | Pure string concatenation |

---

## Terminators

Terminators end a block and transfer control flow. Each block has exactly one.

| Terminator | Description |
|------------|-------------|
| `branch(target, args)` | Unconditional jump to `target`, passing `args` as block parameters |
| `condBranch(cond, thenB, thenArgs, elseB, elseArgs)` | Branch on `cond`: true → `thenB`, false → `elseB` |
| `ret(val)` | Return from function. `val` is optional (None return). |
| `raise(exc)` | Raise an exception. Jumps to the block's `except` target if present; otherwise propagates to caller. |
| `unreachable` | Marks a block end that should never be reached. |

---

## Blocks

A basic block has one entry point and multiple exit points.

```
block <BlockId>(<params...>) [except: <handler>]:
  <NamedInstr>...
  <Terminator>
```

### Fields

- **`id`**: Unique label within the function.
- **`params`**: Block parameters (Crucible/SWIFT style, replaces phi nodes). Each
  incoming branch passes values that bind to these parameters.
- **`names`**: `Array SSAName` mapping each `SSAVal.id` to its human-readable name.
- **`instrs`**: Sequence of `NamedInstr`. May contain multiple raising instructions.
- **`term`**: The terminator.
- **`termSr`**: Source range for the terminator.
- **`except`**: Optional exception handler target. If present and any instruction
  raises, control transfers to the handler block.

### NamedInstr

Each instruction defines one SSA value, with an optional `exceptArgs` field for
raising instructions:

```
%<id>:<name> : <type> = <instruction>                    @ <source_range>
%<id>:<name> : <type> = <instruction>  [exceptArgs: ...]  @ <source_range>
```

Fields:
- **`result`**: The SSA value defined by this instruction.
- **`type`**: Optional type annotation from the source.
- **`instr`**: The instruction.
- **`sr`**: Source range.
- **`exceptArgs`**: `Option (Array SSAVal)` — present for raising instructions.
  Contains the values to pass to the block's exception handler if this instruction
  raises. `none` for non-raising instructions.

Example: `%1:x : int = call @f(%0)  [exceptArgs: undef("y"), %exc]  @ 5:3-5:10`

### Exception Handler Contract

When a block with `except = some(handler)` has a raising instruction with
`exceptArgs = some(args)`:

1. If the instruction raises, control transfers to the handler block with `args`
   as the block arguments.
2. Each raising instruction independently specifies its `exceptArgs` — this is how
   the handler knows which variables were defined at the point of the specific raise.
3. The handler block has a fixed parameter list. All raising instructions in the
   block must pass the same number of arguments (matching the handler's parameter
   count), using `undef` for variables not yet assigned at that point.

**Well-formedness**: Every instruction with `exceptArgs = some _` must be in a block
with `except = some _`. The `exceptArgs` array length must match the handler block's
parameter count.

---

## Functions

```
func <name>(<params...>) -> <retType>:
  <Block>...
```

- **`name`**: Function name (`@module_init`, `@ClassName_init`, `ClassName.method`,
  or bare function name).
- **`params`**: Function parameters (same as entry block parameters).
- **`retType`**: Optional return type annotation.
- **`blocks`**: Array of blocks. The first block is the entry point.
- **`sr`**: Source range of the function definition.

---

## Desugaring Rules

### Assignment (`Assign`, `AnnAssign`)

```python
x: int = expr
```

Translates to evaluating `expr` into an SSA value. The type annotation `int` is
attached to the resulting `NamedInstr`.

```python
x = y = expr
```

Multiple assignment targets: evaluate `expr` once, then `copy` for each target.

### Augmented Assignment (`AugAssign`)

```python
x += expr
```

Desugars to `x = x + expr`:

```
%1 = binOp add %x.0 %expr
-- %1 becomes x.1
```

### If/Else

```python
if cond:
    x = 1
else:
    x = 2
use(x)
```

```
block bb0():
  %0:cond = ...
  condBranch %0 bb_then() bb_else()

block bb_then():
  %0:x = intLit 1
  branch bb_join(%0)

block bb_else():
  %0:x = intLit 2
  branch bb_join(%0)

block bb_join(%0:x):
  call @use(%0)
```

When a variable is assigned in only one branch:

```python
if cond:
    x = 1
use(x)      # NameError if cond is False
```

```
block bb_then():
  %0:x = intLit 1
  branch bb_join(%0)

block bb_else():
  %0:x = undef
  branch bb_join(%0)

block bb_join(%0:x):        -- possibly undef
  call @use(%0)             -- NameError if undef
```

### While Loop

```python
while cond:
    body
```

```
block bb_loop_header():
  %0:cond = ...
  condBranch %0 bb_loop_body() bb_after_loop()

block bb_loop_body():
  -- body...
  branch bb_loop_header()

block bb_after_loop():
  ...
```

`break` → `branch bb_after_loop(...)`, `continue` → `branch bb_loop_header(...)`

### For Loop (Iterator Protocol)

```python
for x in items:
    body(x)
```

Desugars to the Python iterator protocol:

```
block bb_iter_init():
  %0:iter = call @iter(%items)
  branch bb_loop_header(%0)

block bb_loop_header(%0:iter) [except: bb_loop_end]:
  %1:next = call @next(%0)           -- raises StopIteration at end
  branch bb_loop_body(%0, %1)

block bb_loop_body(%0:iter, %1:x):
  -- body using %1 as x
  branch bb_loop_header(%0)

block bb_loop_end(%0:iter, %exc):
  -- StopIteration caught, loop done
  branch bb_after_loop()

block bb_after_loop():
  ...
```

`break` → `branch bb_after_loop(...)`, `continue` → `branch bb_loop_header(%iter)`

### Try/Except (Instruction-Level Precision)

```python
try:
    do_something()
    x = f()
    y = g()
except SomeError as e:
    handle(e)
use(x, y)
```

All raising instructions stay in one block. Each carries its own `exceptArgs`
specifying what the handler receives at that point. Earlier instructions pass
`undef` for variables not yet assigned.

```
block bb_try() [except: bb_handler]:
  %0 = call @do_something()  [exceptArgs: undef("x"), undef("y"), %exc]
  %1:x = call @f()           [exceptArgs: undef("x"), undef("y"), %exc]
  %2:y = call @g()           [exceptArgs: %1,         undef("y"), %exc]
  branch bb_after_try(%1, %2)

block bb_handler(%0:x, %1:y, %exc):
  -- %0:x is undef if do_something() or f() raised
  -- %0:x is f()'s result if g() raised
  -- %1:y is always undef (g() never completed successfully)
  -- Type check: isinstance(exc, SomeError)
  %2 = call @isinstance(%exc, positional(@SomeError))
  condBranch %2 bb_handle(%exc) bb_reraise(%exc)

block bb_handle(%exc):
  call @handle(%exc)
  branch bb_after_try_join(...)

block bb_reraise(%exc):
  raise %exc                -- propagates to outer handler or caller
```

### Try/Finally (undef/isDefined Pattern)

```python
try:
    body()
finally:
    cleanup()
```

The finally block takes the exception as a possibly-undef value:

```
-- Normal path:
block bb_try_body() [except: bb_exc_path]:
  call @body()
  branch bb_finally(%undef)          -- no exception

-- Exception path:
block bb_exc_path(%exc):
  branch bb_finally(%exc)            -- has exception

-- Finally: always executes
block bb_finally(%0:maybe_exc):
  call @cleanup()
  %1 = isDefined %0
  condBranch %1 bb_reraise(%0) bb_after()

block bb_reraise(%0:exc):
  raise %0

block bb_after():
  ...
```

### With Statement

```python
with ctx_expr as var:
    body
```

Desugars to `__enter__`/`__exit__` with exception handling:

```
block bb_with_enter():
  %0:mgr = <translate ctx_expr>
  %1:var = call attr(%0, "__enter__")()
  branch bb_with_body(%0, %1)

block bb_with_body(%0:mgr, %1:var) [except: bb_with_exc]:
  -- body instructions using %1 as var...
  branch bb_with_exit_normal(%0)

block bb_with_exc(%0:mgr, %1:var, %exc):
  %2:suppress = call attr(%0, "__exit__")(%exc_type, %exc_val, %exc_tb)
  condBranch %2 bb_after_with() bb_reraise(%exc)

block bb_with_exit_normal(%0:mgr):
  call attr(%0, "__exit__")(noneLit, noneLit, noneLit)
  branch bb_after_with()

block bb_reraise(%exc):
  raise %exc

block bb_after_with():
  ...
```

### BoolOp Short-Circuit

`a and b`:

```
block bb_eval_a():
  %0:a = <translate a>
  condBranch %0 bb_eval_b() bb_short(%0)

block bb_eval_b():
  %0:b = <translate b>
  branch bb_join(%0)

block bb_short(%0:a):
  branch bb_join(%0)

block bb_join(%0:result):
  -- %0 is the value of the whole expression
```

`a or b`: same structure but branches are swapped (short-circuit on true).

### IfExp (Ternary)

```python
x = a if cond else b
```

```
block bb_eval_cond():
  %0:cond = <translate cond>
  condBranch %0 bb_then() bb_else()

block bb_then():
  %0 = <translate a>
  branch bb_join(%0)

block bb_else():
  %0 = <translate b>
  branch bb_join(%0)

block bb_join(%0:x):
  -- %0 is the value of the IfExp
```

### Chained Comparisons

```python
a < b < c
```

Desugars to `(a < b) and (b < c)` with `b` evaluated once, then short-circuit:

```
block bb_start():
  %0:a = <translate a>
  %1:b = <translate b>
  %2 = compareOp lt %0 %1
  condBranch %2 bb_second_cmp(%1) bb_short_false(%2)

block bb_second_cmp(%0:b):
  %1:c = <translate c>
  %2 = compareOp lt %0 %1
  branch bb_join(%2)

block bb_short_false(%0):
  branch bb_join(%0)              -- False (first comparison failed)

block bb_join(%0:result):
  -- %0 is the result of the chained comparison
```

### f-strings

```python
f"Hello {name}, you are {age} years old"
```

Desugars to `fmtValue` + `strConcat`:

```
block bb_fstr():
  %0 = strLit "Hello "
  %1 = fmtValue %name              -- calls __format__(name)
  %2 = strLit ", you are "
  %3 = fmtValue %age               -- calls __format__(age)
  %4 = strLit " years old"
  %5 = strConcat [%0, %1, %2, %3, %4]
```

Note: each `fmtValue` can raise, so in practice each would be the last instruction
in its block with appropriate exception handling if inside a try.

### Imports

Imports are not emitted as SSA instructions. During translation, they update a
binding environment that maps local names to qualified identifiers.

```python
import boto3
from boto3 import client

x = client('s3')           # → callQualified "boto3" "client" [positional(strLit "s3")]
y = boto3.client('iam')    # → callQualified "boto3" "client" [positional(strLit "iam")]
```

### Classes

```python
class MyClass:
    default_value = 10

    def __init__(self, x: int):
        self.x = x

    def get_x(self) -> int:
        return self.x
```

Produces three functions:

```
func @MyClass_init():
  %0 = intLit 10
  -- store default_value (class-level assignment)
  ret

func MyClass.__init__(self: MyClass, x: int):
  setAttr %self "x" %x
  ret

func MyClass.get_x(self: MyClass) -> int:
  %0 = attr %self "x"
  ret %0
```

`@module_init` calls `@MyClass_init`.

### Raise

```python
raise ValueError("bad input")
```

```
%0 = callQualified "builtins" "ValueError" [positional(strLit "bad input")]
raise %0
```

Bare `raise` inside an except handler re-raises the handler's exception parameter:

```
block bb_handler(%exc):
  raise %exc
```

---

## Operator Enums

Only operators observed in the target corpus are included.

### BinOpKind

`add` | `sub` | `mult` | `div` | `floorDiv` | `mod` | `pow`

### UnaryOpKind

`not` | `uSub`

### CmpOpKind

`eq` | `notEq` | `lt` | `ltE` | `gt` | `gtE` | `is` | `isNot` | `in` | `notIn`

---

## Well-Formedness Invariants

1. **undef restriction**: `undef` values may only flow through block parameters and
   `isDefined` checks. All other instructions require defined operands. An `undef`
   reaching any other use is a detected `NameError`.

2. **exceptArgs consistency**: Every instruction with `exceptArgs = some(args)` must
   be in a block with `except = some(target)`. The length of `args` must match the
   handler block's parameter count. Instructions with `exceptArgs = none` are
   non-raising.

3. **Block parameter consistency**: All branches to a block must pass the same number
   of arguments, matching the block's parameter count.

4. **Exception handler contract**: When a block has `except = some(target)`, all
   raising instructions in the block must have `exceptArgs` arrays of the same
   length, matching the handler's parameter count. Each `exceptArgs` array reflects
   the state at that instruction's point of execution, using `undef` for variables
   not yet assigned.

5. **Entry block**: The first block in a function is the entry point. Its parameters
   are the function parameters.

6. **Terminator completeness**: Every block ends with exactly one terminator.

---

## Pretty-Print Notation

The standard textual format for PythonSSA output:

```
module "<name>":

func <name>(<params>) -> <retType>:    @ <sr>
  bb<id>(<params>) [except: bb<id>]:   @ <sr>
    %<id>:<name> : <type> = <instruction>   @ <sr>
    ...
    <terminator>                        @ <sr>
```

Example:

```
module "get_iam_role_arn":

func @module_init():                                   @ 1:1-9:42
  bb0():                                               @ 1:1-1:13
    %0:boto3 = callQualified "boto3" "import" []       @ 1:1-1:13
    branch bb1(%0)                                     @ 1:1
  bb1(%0:boto3):                                       @ 2:1-2:38
    %0:iam = callQualified "boto3" "client" [positional(strLit "iam")]  @ 2:14-2:38
    branch bb2(%0)                                     @ 2:1
  ...
```

Source ranges use `line:col-line:col` format matching the Python source.
