# `--typed-python`: Native Lowering for Annotated Python

By default, Strata's Python verifier lowers every value through a
universal `Any` algebraic datatype. The encoding is sound but loses
precision — ordinary integer arithmetic over `Any` chains a `from_int`
on each input and a `from_int` on each output, and the SMT solver
spends its time peeling those tags instead of doing arithmetic.

`--typed-python` is an opt-in mode that keeps annotated primitives
and containers in their **native Laurel sort** end-to-end. The result
is fewer obligations, cleaner counter-examples, and verifications
that finish in milliseconds where the `Any` encoding times out.

## Quick start

```bash
strata pyAnalyzeLaurel --typed-python my_program.python.st.ion
```

Off by default. Add the flag to opt every annotated value into the
typed encoding for the whole file.

## Supported subset

| Python annotation | Laurel sort |
|---|---|
| `int`, `bool`, `float`, `str` | `TInt`, `TBool`, `TReal`, `TString` |
| `list`, `Sequence`, `List` (no inner type) | `TSeq Any` |
| `list[T]`, `Sequence[T]`, `List[T]` | `TSeq T` (recursive) |
| `dict`, `Mapping`, `Dict` (no inner type) | `TMap Any Any` |
| `dict[K, V]`, `Mapping[K, V]`, `Dict[K, V]` | `TMap K V` (recursive) |
| User-defined classes | `UserDefined ClassName` |
| Class fields of primitive type | `TInt` / `TBool` / `TReal` / `TString` |
| Typed `__init__` parameters | native primitive sorts |

Operators that lower natively when the operand types match:

- Arithmetic: `+`, `-`, `*`, `//`, `%` (integers) and `+` (string concat).
- Unary: `not` on `bool`, `-` on `int`.
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=` on `int`-like or `str`
  operands. Single comparisons only — chained `a < b < c` keeps the
  legacy Any path so evaluate-once semantics is preserved.
- Boolean: `and`, `or` when **all** operands are `bool` (mixed types
  fall through to Any since Python's `bool and int` returns `int`).
- Subscript: `xs[i]` over `list[T]` (→ `Sequence.select`), `m[k]`
  over `dict[K, V]` (→ map `select`).
- Function calls: typed callees take native arguments and return
  native values; the call boundary unwraps and re-wraps once via the
  `fromAny` / `toAny` peephole, which collapses `from_X(Any..as_X!(...))`
  pairs to the inner expression.

## Refused under `--typed-python`

The pyspec layer rejects the following, with a fatal
`typedPythonRefusal` diagnostic:

- `Optional[T]` / `Union[T, None]` and other unions.
- `Literal[...]` types.
- `bytes` (no native sort yet).
- `list[Foo]` where `Foo` is not a recognised primitive or class.

When the flag is off, these collapse silently to `Any` as before.

## Limitations

The following work correctly under `--typed-python` but stay on the
`Any` path (no precision gain):

- Operators not listed above (`**`, `/`, `<<`, `>>`, `&`, `|`, `^`, `~`).
- `len(x)` in user-code expressions (the spec layer does dispatch
  natively over `TSeq` / `TString`).
- Container mutation: `xs.append(...)`, `m[k] = v`, `xs += y`.
- Tuples (`tuple[A, B]`), sets, frozensets, generators.
- Higher-order functions: passing typed functions as arguments.
- Quantifiers (`forall` / `exists`) in user-code preconditions.
- **Class fields of container type** (`self.items: list`). Container
  fields stay `Any` because the heap-parameterization pass can't yet
  box them; subscript on `self.items` routes through `Any_get`. The
  primitive-field path (e.g. `self.balance: int`) lowers natively.

Counter-examples on a typed program are reported in terms of native
Laurel sorts (`TInt`, `TSeq Int`, …) rather than the user's Python
source positions. Mapping back to source is a follow-up.

## Strict mode

`--typed-python` turns refusal of an unsupported type into a hard
error — there is no silent widening for the typed surface.

## Benchmarks

Measured on the `test_typed_python_*` demo pairs (`pyAnalyzeLaurel
--check-mode bugFinding --check-level full`, mean of 3 runs).
"inconclusive" counts the verification obligations the solver could
not decide — the lower the better.

| Pair           | off (ms) | on (ms) | speed-up | off ❓ | on ❓ |
|----------------|---------:|--------:|---------:|------:|-----:|
| nested_arith   |    1475  |     91  |   16.2×  |     0 |    0 |
| compose_calls  |    1374  |    117  |   11.7×  |     0 |    0 |
| nested_scope   |    1318  |    163  |    8.1×  |    10 |    5 |
| loops          |    1053  |    152  |    6.9×  |    13 |    5 |
| methods        |     485  |    207  |    2.3×  |    10 |    7 |
| class_fields   |     278  |    119  |    2.3×  |     6 |    2 |
| mixed_arith    |     460  |    212  |    2.2×  |     9 |    6 |
| subscript      |     260  |    163  |    1.6×  |     7 |    3 |

Reproduce: `cd StrataTest/Languages/Python && ./run_py_analyze.sh
--filter typed_python`.
