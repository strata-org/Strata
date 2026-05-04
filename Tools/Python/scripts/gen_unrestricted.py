# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unrestricted Python program generators for fuzz testing.

This module contains ~60 generators that produce Python code blocks using
constructs that may be beyond what Strata supports today. It is loaded by
gen_random_python.py when the --unrestricted flag is passed.

Each generator function returns a string of indented Python statements
(4-space indent) that can be placed inside a ``def main():`` body. Every
block includes at least one ``assert`` whose expected value is computed by
CPython at generation time. If Strata's verifier disagrees with CPython
on any of these assertions, that indicates a semantic modelling bug.

## Categories of generators

### Operators
  - Bitwise: &, |, ^, ~ (gen_bitwise, gen_bitnot)
  - Shifts: <<, >> (gen_shift)
  - Power: ** (gen_power)
  - Augmented assignment: +=, -=, *= (gen_augmented_assign)

### Expressions
  - Ternary: x if cond else y (gen_ternary)
  - Chained comparisons: a <= b <= c (gen_chained_cmp)
  - F-strings (gen_fstring)
  - Lambda (gen_lambda)
  - Walrus operator := (gen_walrus, gen_walrus_while)

### Data structures
  - Lists: create, index, slice, concat, in, append (gen_list_*)
  - Dicts: create, access, in (gen_dict_*)
  - Sets: union, intersection (gen_set_ops)
  - Tuple unpacking, star unpacking (gen_tuple_unpack, gen_star_unpack)
  - Multiple assignment / swap (gen_multi_assign)

### Strings
  - len, indexing, multiply, methods (upper/lower/strip), format

### Control flow
  - For loops over lists and range (gen_for_sum, gen_for_range)
  - While loops (gen_while_countdown)
  - Break (gen_break)
  - Nested if, elif chains (gen_nested_if, gen_elif)
  - Nested loops (gen_nested_loop)

### Functions
  - Nested calls (gen_nested_call)
  - Default arguments (gen_default_args)
  - *args, **kwargs (gen_varargs, gen_kwargs)
  - Recursion (gen_recursion)
  - Decorators (gen_decorator)
  - Generators / yield (gen_generator)

### Classes
  - Basic class with __init__ (gen_class_basic)
  - Class with methods (gen_class_method)

### Exception handling
  - try/except (gen_try_except)
  - try/except/else (gen_try_except_else)
  - try/finally (gen_try_finally)
  - Multiple except clauses (gen_multi_except)
  - raise (gen_raise)

### Other
  - None checks, Optional type (gen_none_check, gen_optional)
  - isinstance (gen_isinstance)
  - Type conversions: int(), str(), bool(), float(), list() (gen_type_conv)
  - With statement / context managers (gen_with_stmt)
  - Nonlocal (gen_nonlocal)
  - Pass, del (gen_pass, gen_del)
  - Async def / asyncio.run (gen_async_def)
  - Match statement, Python 3.10+ (gen_match)

## Adding new generators

To add a new generator:
1. Write a function that returns a string of 4-space-indented Python
   statements including at least one assert with a CPython-computed
   expected value.
2. Test it: ``python3 -c "exec('def main():\\n' + gen_your_thing() + 'main()')"``
3. Add it to the UNRESTRICTED_GENERATORS list at the bottom.
"""

import random

# ---------------------------------------------------------------------------
# Helpers — shared random value generators
# ---------------------------------------------------------------------------

def _rand_int():
    """Random integer in [-100, 100]."""
    return random.randint(-100, 100)

def _rand_bool():
    """Random boolean."""
    return random.choice([True, False])

def _rand_str():
    """Random short string from a fixed vocabulary."""
    return random.choice(["hello", "world", "foo", "bar", "", "abc", "x"])

def _nonzero():
    """Random non-zero integer in [-10, 10]."""
    return random.choice([x for x in range(-10, 11) if x != 0])

def _rand_var(prefix="v"):
    """Random variable name like v42."""
    return f"{prefix}{random.randint(0, 99)}"

# ---------------------------------------------------------------------------
# Operators
# ---------------------------------------------------------------------------

def gen_bitwise():
    a, b = _rand_int(), _rand_int()
    op, sym = random.choice([("and", "&"), ("or", "|"), ("xor", "^")])
    r = eval(f"{a} {sym} {b}")
    return f"    assert ({a} {sym} {b}) == {r}, \"bitwise {op}\"\n"

def gen_shift():
    a = random.randint(0, 100)
    b = random.randint(0, 8)
    op, sym = random.choice([("lshift", "<<"), ("rshift", ">>")])
    r = eval(f"{a} {sym} {b}")
    return f"    assert ({a} {sym} {b}) == {r}, \"{op}\"\n"

def gen_bitnot():
    """Bitwise NOT (~)."""
    a = _rand_int()
    return f"    assert ~{a} == {~a}, \"bitnot\"\n"

# --- Power ---

def gen_power():
    """Exponentiation (**). Uses non-negative base to avoid precedence issues
    with unary minus (``-2 ** 2`` is ``-(2**2)`` in Python)."""
    base = random.randint(0, 5)
    exp = random.randint(0, 4)
    r = base ** exp
    return f"    assert {base} ** {exp} == {r}, \"power\"\n"

# --- Augmented assignment ---

def gen_augmented_assign():
    a = _rand_int()
    b = _rand_int()
    op, sym = random.choice([("+", "+="), ("-", "-="), ("*", "*=")])
    r = eval(f"{a} {op} {b}")
    return (
        f"    x: int = {a}\n"
        f"    x {sym} {b}\n"
        f'    assert x == {r}, "augmented {sym}"\n'
    )

# --- Ternary expression ---

def gen_ternary():
    cond = _rand_bool()
    a, b = _rand_int(), _rand_int()
    r = a if cond else b
    return f"    assert ({a} if {cond} else {b}) == {r}, \"ternary\"\n"

# --- Multiple assignment / swap ---

def gen_multi_assign():
    a, b = _rand_int(), _rand_int()
    return (
        f"    x: int = {a}\n"
        f"    y: int = {b}\n"
        f"    x, y = y, x\n"
        f'    assert x == {b} and y == {a}, "swap"\n'
    )

# --- List operations ---

def gen_list_create():
    elems = [_rand_int() for _ in range(random.randint(1, 5))]
    return (
        f"    lst: list = {elems}\n"
        f'    assert len(lst) == {len(elems)}, "list len"\n'
    )

def gen_list_index():
    elems = [_rand_int() for _ in range(random.randint(2, 5))]
    idx = random.randint(0, len(elems) - 1)
    return (
        f"    lst: list = {elems}\n"
        f'    assert lst[{idx}] == {elems[idx]}, "list index"\n'
    )

def gen_list_concat():
    a = [_rand_int() for _ in range(random.randint(1, 3))]
    b = [_rand_int() for _ in range(random.randint(1, 3))]
    return (
        f"    a: list = {a}\n"
        f"    b: list = {b}\n"
        f'    assert a + b == {a + b}, "list concat"\n'
    )

def gen_list_slice():
    elems = [_rand_int() for _ in range(random.randint(3, 6))]
    i = random.randint(0, len(elems) - 2)
    j = random.randint(i + 1, len(elems))
    return (
        f"    lst: list = {elems}\n"
        f'    assert lst[{i}:{j}] == {elems[i:j]}, "list slice"\n'
    )

def gen_list_in():
    elems = [_rand_int() for _ in range(random.randint(2, 5))]
    target = random.choice(elems)
    return (
        f"    lst: list = {elems}\n"
        f'    assert {target} in lst, "list in"\n'
    )

def gen_list_append():
    elems = [_rand_int() for _ in range(random.randint(1, 3))]
    v = _rand_int()
    return (
        f"    lst: list = {elems}\n"
        f"    lst.append({v})\n"
        f'    assert lst == {elems + [v]}, "list append"\n'
    )

# --- Dict operations ---

def gen_dict_create():
    keys = random.sample(["a", "b", "c", "d", "e"], random.randint(1, 4))
    d = {k: _rand_int() for k in keys}
    # {len(d)} is evaluated at generation time, producing e.g. "assert len(d) == 3"
    return (
        f"    d: dict = {d}\n"
        f'    assert len(d) == {len(d)}, "dict len"\n'
    )

def gen_dict_access():
    keys = random.sample(["a", "b", "c", "d"], random.randint(2, 4))
    d = {k: _rand_int() for k in keys}
    k = random.choice(keys)
    return (
        f"    d: dict = {d}\n"
        f'    assert d[{k!r}] == {d[k]}, "dict access"\n'
    )

def gen_dict_in():
    keys = random.sample(["a", "b", "c", "d"], random.randint(2, 4))
    d = {k: _rand_int() for k in keys}
    k = random.choice(keys)
    return (
        f"    d: dict = {d}\n"
        f'    assert {k!r} in d, "dict in"\n'
    )

# --- String operations ---

def gen_str_len():
    s = _rand_str()
    return f'    assert len({s!r}) == {len(s)}, "str len"\n'

def gen_str_index():
    s = random.choice(["hello", "world", "foobar", "abc"])
    i = random.randint(0, len(s) - 1)
    return f'    assert {s!r}[{i}] == {s[i]!r}, "str index"\n'

def gen_str_multiply():
    s = random.choice(["ab", "x", "hi"])
    n = random.randint(0, 4)
    return f'    assert {s!r} * {n} == {(s * n)!r}, "str mul"\n'

def gen_str_methods():
    s = random.choice(["Hello", "WORLD", "foo Bar", "abc"])
    method = random.choice(["upper", "lower", "strip"])
    r = getattr(s, method)()
    return f'    assert {s!r}.{method}() == {r!r}, "str {method}"\n'

# --- For loops ---

def gen_for_sum():
    elems = [random.randint(0, 20) for _ in range(random.randint(2, 5))]
    return (
        f"    total: int = 0\n"
        f"    for x in {elems}:\n"
        f"        total = total + x\n"
        f'    assert total == {sum(elems)}, "for sum"\n'
    )

def gen_for_range():
    n = random.randint(1, 10)
    return (
        f"    total: int = 0\n"
        f"    for i in range({n}):\n"
        f"        total = total + i\n"
        f'    assert total == {sum(range(n))}, "for range"\n'
    )

# --- While loops ---

def gen_while_countdown():
    n = random.randint(1, 10)
    return (
        f"    n: int = {n}\n"
        f"    count: int = 0\n"
        f"    while n > 0:\n"
        f"        count = count + 1\n"
        f"        n = n - 1\n"
        f'    assert count == {n}, "while countdown"\n'
    )

# --- Break / continue ---

def gen_break():
    elems = list(range(1, random.randint(4, 8)))
    stop = random.choice(elems[1:])
    expected = sum(x for x in elems if x < stop)
    return (
        f"    total: int = 0\n"
        f"    for x in {elems}:\n"
        f"        if x == {stop}:\n"
        f"            break\n"
        f"        total = total + x\n"
        f'    assert total == {expected}, "break"\n'
    )

# --- Nested if ---

def gen_nested_if():
    a, b = _rand_int(), _rand_int()
    if a > 0:
        if b > 0:
            r = 1
        else:
            r = 2
    else:
        r = 3
    return (
        f"    a: int = {a}\n"
        f"    b: int = {b}\n"
        f"    if a > 0:\n"
        f"        if b > 0:\n"
        f"            r: int = 1\n"
        f"        else:\n"
        f"            r: int = 2\n"
        f"    else:\n"
        f"        r: int = 3\n"
        f'    assert r == {r}, "nested if"\n'
    )

# --- Elif chains ---

def gen_elif():
    a = _rand_int()
    if a > 0:
        r = "pos"
    elif a < 0:
        r = "neg"
    else:
        r = "zero"
    return (
        f"    a: int = {a}\n"
        f"    if a > 0:\n"
        f"        r: str = \"pos\"\n"
        f"    elif a < 0:\n"
        f"        r: str = \"neg\"\n"
        f"    else:\n"
        f"        r: str = \"zero\"\n"
        f'    assert r == {r!r}, "elif"\n'
    )

# --- Multiple return values / tuple unpacking ---

def gen_tuple_unpack():
    a, b, c = _rand_int(), _rand_int(), _rand_int()
    return (
        f"    a, b, c = {a}, {b}, {c}\n"
        f'    assert a == {a} and b == {b} and c == {c}, "tuple unpack"\n'
    )

# --- Chained comparisons ---

def gen_chained_cmp():
    a, b, c = sorted([_rand_int() for _ in range(3)])
    return f'    assert {a} <= {b} <= {c}, "chained cmp"\n'

# --- None checks ---

def gen_none_check():
    use_none = _rand_bool()
    val = "None" if use_none else str(_rand_int())
    is_none = use_none
    return (
        f"    x = {val}\n"
        f'    assert (x is None) == {is_none}, "none check"\n'
    )

# --- Optional type ---

def gen_optional():
    from typing import Optional
    use_none = _rand_bool()
    if use_none:
        return (
            f"    from typing import Optional\n"
            f"    x: Optional[int] = None\n"
            f'    assert x is None, "optional none"\n'
        )
    else:
        v = _rand_int()
        return (
            f"    from typing import Optional\n"
            f"    x: Optional[int] = {v}\n"
            f'    assert x == {v}, "optional value"\n'
        )

# --- Classes ---

def gen_class_basic():
    x = _rand_int()
    return (
        f"    class Pt:\n"
        f"        def __init__(self):\n"
        f"            self.x: int = {x}\n"
        f"    p = Pt()\n"
        f'    assert p.x == {x}, "class field"\n'
    )

def gen_class_method():
    a, b = _rand_int(), _rand_int()
    return (
        f"    class Adder:\n"
        f"        def __init__(self):\n"
        f"            self.val: int = {a}\n"
        f"        def add(self, n: int) -> int:\n"
        f"            return self.val + n\n"
        f"    obj = Adder()\n"
        f'    assert obj.add({b}) == {a + b}, "class method"\n'
    )

# --- Nested function calls ---

def gen_nested_call():
    a, b = _rand_int(), _rand_int()
    return (
        f"    def add(x: int, y: int) -> int:\n"
        f"        return x + y\n"
        f"    def double(x: int) -> int:\n"
        f"        return x * 2\n"
        f'    assert double(add({a}, {b})) == {(a + b) * 2}, "nested call"\n'
    )

# --- Lambda ---

def gen_lambda():
    a, b = _rand_int(), _rand_int()
    return (
        f"    f = lambda x, y: x + y\n"
        f'    assert f({a}, {b}) == {a + b}, "lambda"\n'
    )

# --- List comprehension ---

def gen_list_comp():
    n = random.randint(2, 6)
    return (
        f"    lst = [x * 2 for x in range({n})]\n"
        f'    assert lst == {[x * 2 for x in range(n)]}, "list comp"\n'
    )

def gen_list_comp_filter():
    n = random.randint(3, 8)
    return (
        f"    lst = [x for x in range({n}) if x % 2 == 0]\n"
        f'    assert lst == {[x for x in range(n) if x % 2 == 0]}, "list comp filter"\n'
    )

# --- Dict comprehension ---

def gen_dict_comp():
    n = random.randint(2, 5)
    expected = {str(i): i * i for i in range(n)}
    return (
        f"    d = {{str(i): i * i for i in range({n})}}\n"
        f'    assert d == {expected}, "dict comp"\n'
    )

# --- Try/except ---

def gen_try_except():
    return (
        f"    caught: bool = False\n"
        f"    try:\n"
        f"        x: int = 1 // 0\n"
        f"    except ZeroDivisionError:\n"
        f"        caught = True\n"
        f'    assert caught, "try except"\n'
    )

def gen_try_except_else():
    return (
        f"    result: int = 0\n"
        f"    try:\n"
        f"        result = 42\n"
        f"    except Exception:\n"
        f"        result = -1\n"
        f"    else:\n"
        f"        result = result + 1\n"
        f'    assert result == 43, "try else"\n'
    )

def gen_try_finally():
    return (
        f"    cleanup: bool = False\n"
        f"    try:\n"
        f"        x: int = 10\n"
        f"    finally:\n"
        f"        cleanup = True\n"
        f'    assert cleanup, "try finally"\n'
    )

# --- With statement (context manager) ---

def gen_with_stmt():
    # Use a simple class-based context manager
    return (
        f"    class CM:\n"
        f"        def __enter__(self):\n"
        f"            return 42\n"
        f"        def __exit__(self, *args):\n"
        f"            pass\n"
        f"    with CM() as v:\n"
        f"        r: int = v\n"
        f'    assert r == 42, "with stmt"\n'
    )

# --- Global / nonlocal ---

def gen_nonlocal():
    return (
        f"    x: int = 0\n"
        f"    def inner():\n"
        f"        nonlocal x\n"
        f"        x = 99\n"
        f"    inner()\n"
        f'    assert x == 99, "nonlocal"\n'
    )

# --- Walrus operator ---

def gen_walrus():
    v = _rand_int()
    return (
        f"    lst = [{v}]\n"
        f"    if (n := len(lst)) > 0:\n"
        f'        assert n == 1, "walrus"\n'
    )

# --- F-strings ---

def gen_fstring():
    a = random.randint(0, 50)
    return (
        f"    a = {a}\n"
        f'    assert f"val={{a}}" == "val={a}", "fstring"\n'
    )

# --- Star unpacking ---

def gen_star_unpack():
    elems = [_rand_int() for _ in range(random.randint(3, 5))]
    return (
        f"    first, *rest = {elems}\n"
        f'    assert first == {elems[0]}, "star unpack first"\n'
        f'    assert rest == {elems[1:]}, "star unpack rest"\n'
    )

# --- Nested loops ---

def gen_nested_loop():
    n, m = random.randint(1, 4), random.randint(1, 4)
    return (
        f"    total: int = 0\n"
        f"    for i in range({n}):\n"
        f"        for j in range({m}):\n"
        f"            total = total + 1\n"
        f'    assert total == {n * m}, "nested loop"\n'
    )

# --- Type conversions ---

def gen_type_conv():
    conv = random.choice([
        ("int(3.7)", 3, "float to int"),
        ("str(42)", "42", "int to str"),
        ("int('17')", 17, "str to int"),
        ("bool(0)", False, "int to bool false"),
        ("bool(1)", True, "int to bool true"),
        ("float(5)", 5.0, "int to float"),
        ("list(range(3))", [0, 1, 2], "range to list"),
    ])
    expr, expected, label = conv
    return f'    assert {expr} == {expected!r}, "{label}"\n'

# --- String formatting ---

def gen_str_format():
    a = _rand_int()
    return f'    assert "x={{}}".format({a}) == "x={a}", "str format"\n'

# --- Multiple except clauses ---

def gen_multi_except():
    return (
        f"    result: str = \"\"\n"
        f"    try:\n"
        f"        x = 1 // 0\n"
        f"    except TypeError:\n"
        f"        result = \"type\"\n"
        f"    except ZeroDivisionError:\n"
        f"        result = \"zero\"\n"
        f'    assert result == "zero", "multi except"\n'
    )

# --- Raise / re-raise ---

def gen_raise():
    return (
        f"    caught: bool = False\n"
        f"    try:\n"
        f"        raise ValueError(\"test\")\n"
        f"    except ValueError as e:\n"
        f"        caught = True\n"
        f'        assert str(e) == "test", "raise msg"\n'
        f'    assert caught, "raise caught"\n'
    )

# --- Pass statement ---

def gen_pass():
    return (
        f"    if True:\n"
        f"        pass\n"
        f'    assert True, "pass"\n'
    )

# --- Delete ---

def gen_del():
    return (
        f"    lst = [1, 2, 3]\n"
        f"    del lst[1]\n"
        f'    assert lst == [1, 3], "del"\n'
    )

# --- Set operations ---

def gen_set_ops():
    a = list(set([random.randint(0, 10) for _ in range(4)]))
    b = list(set([random.randint(0, 10) for _ in range(4)]))
    sa, sb = set(a), set(b)
    op = random.choice(["union", "intersection"])
    if op == "union":
        r = sorted(sa | sb)
        return f"    assert sorted(set({a}) | set({b})) == {r}, \"set {op}\"\n"
    else:
        r = sorted(sa & sb)
        return f"    assert sorted(set({a}) & set({b})) == {r}, \"set {op}\"\n"

# --- Isinstance ---

def gen_isinstance():
    return random.choice([
        f'    assert isinstance(42, int), "isinstance int"\n',
        f'    assert isinstance("hi", str), "isinstance str"\n',
        f'    assert isinstance(True, bool), "isinstance bool"\n',
        f'    assert isinstance([1], list), "isinstance list"\n',
        f'    assert not isinstance(42, str), "isinstance neg"\n',
    ])

# --- Recursive function ---

def gen_recursion():
    n = random.randint(1, 8)
    def fact(n):
        return 1 if n <= 1 else n * fact(n - 1)
    return (
        f"    def factorial(n: int) -> int:\n"
        f"        if n <= 1:\n"
        f"            return 1\n"
        f"        return n * factorial(n - 1)\n"
        f'    assert factorial({n}) == {fact(n)}, "recursion"\n'
    )

# --- Default arguments ---

def gen_default_args():
    d = _rand_int()
    return (
        f"    def f(x: int, y: int = {d}) -> int:\n"
        f"        return x + y\n"
        f'    assert f(10) == {10 + d}, "default arg"\n'
        f'    assert f(10, 20) == 30, "override default"\n'
    )

# --- *args / **kwargs ---

def gen_varargs():
    return (
        f"    def f(*args):\n"
        f"        return sum(args)\n"
        f'    assert f(1, 2, 3) == 6, "varargs"\n'
    )

def gen_kwargs():
    return (
        f"    def f(**kwargs):\n"
        f"        return kwargs.get(\"x\", 0)\n"
        f'    assert f(x=42) == 42, "kwargs"\n'
    )

# --- Yield / generator ---

def gen_generator():
    n = random.randint(2, 5)
    return (
        f"    def gen():\n"
        f"        for i in range({n}):\n"
        f"            yield i\n"
        f'    assert list(gen()) == {list(range(n))}, "generator"\n'
    )

# --- Decorator ---

def gen_decorator():
    return (
        f"    def my_dec(fn):\n"
        f"        def wrapper(*a):\n"
        f"            return fn(*a) + 1\n"
        f"        return wrapper\n"
        f"    @my_dec\n"
        f"    def f(x: int) -> int:\n"
        f"        return x\n"
        f'    assert f(10) == 11, "decorator"\n'
    )

# --- Async (syntax only, not awaited) ---

def gen_async_def():
    return (
        f"    import asyncio\n"
        f"    async def coro():\n"
        f"        return 42\n"
        f'    assert asyncio.run(coro()) == 42, "async"\n'
    )

# --- Walrus in while ---

def gen_walrus_while():
    return (
        f"    data = [1, 2, 3, 0, 4]\n"
        f"    total: int = 0\n"
        f"    idx: int = 0\n"
        f"    while (v := data[idx]) != 0:\n"
        f"        total = total + v\n"
        f"        idx = idx + 1\n"
        f'    assert total == 6, "walrus while"\n'
    )

# --- Match statement (Python 3.10+) ---

def gen_match():
    v = random.choice([1, 2, 3, "other"])
    if v == 1:
        r = "one"
    elif v == 2:
        r = "two"
    else:
        r = "other"
    return (
        f"    val = {v!r}\n"
        f"    match val:\n"
        f"        case 1:\n"
        f"            r = \"one\"\n"
        f"        case 2:\n"
        f"            r = \"two\"\n"
        f"        case _:\n"
        f"            r = \"other\"\n"
        f'    assert r == {r!r}, "match"\n'
    )


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------
# All unrestricted generators, imported by gen_random_python.py when
# --unrestricted is passed. The order doesn't matter — generators are
# chosen uniformly at random.

UNRESTRICTED_GENERATORS = [
    gen_bitwise, gen_shift, gen_bitnot, gen_power,
    gen_augmented_assign, gen_ternary, gen_multi_assign,
    gen_list_create, gen_list_index, gen_list_concat, gen_list_slice,
    gen_list_in, gen_list_append,
    gen_dict_create, gen_dict_access, gen_dict_in,
    gen_str_len, gen_str_index, gen_str_multiply, gen_str_methods,
    gen_for_sum, gen_for_range, gen_while_countdown, gen_break,
    gen_nested_if, gen_elif, gen_tuple_unpack, gen_chained_cmp,
    gen_none_check, gen_optional,
    gen_class_basic, gen_class_method, gen_nested_call,
    gen_lambda, gen_list_comp, gen_list_comp_filter, gen_dict_comp,
    gen_try_except, gen_try_except_else, gen_try_finally,
    gen_with_stmt, gen_nonlocal, gen_walrus, gen_fstring,
    gen_star_unpack, gen_nested_loop, gen_type_conv, gen_str_format,
    gen_multi_except, gen_raise, gen_pass, gen_del, gen_set_ops,
    gen_isinstance, gen_recursion, gen_default_args,
    gen_varargs, gen_kwargs, gen_generator, gen_decorator,
    gen_async_def, gen_walrus_while, gen_match,
]
