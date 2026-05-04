# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
"""
Generate random Python programs for fuzz-testing Strata's Python front-end.

This script is the program generator used by hypothesmith.sh. It produces
Python source files that can be fed through Strata's pipeline to find bugs.

## Modes

### Syntax mode (--mode syntax)

Uses the hypothesmith library (https://github.com/Zac-HD/hypothesmith) to
generate syntactically valid Python programs from the Python grammar. The
Hypothesis property-based testing framework drives generation, using its
grammar-inversion strategy to produce programs that pass CPython's
``compile()`` function.

Generated programs are filtered by AST node count (--max-nodes) to keep
them small and debuggable. Programs with fewer than 2 AST nodes (empty
or trivial) are discarded.

### Semantic mode (--mode semantic)

Uses a custom generator to produce typed Python programs with assertions
whose expected values are computed by CPython at generation time. This is
analogous to CSmith computing a checksum: the generated program contains
its own expected output, so any disagreement between CPython and Strata
indicates a semantic modelling bug.

Each program is structured as:

    def main():
        <block 1>
        <block 2>
        ...
    main()

where each block declares typed variables, performs operations, and asserts
the expected result. For example:

    def main():
        a: int = 89
        b: int = -30
        r: int = a + b
        assert r == 59, "int add"
    main()

## Generators

The **base generators** (always included) cover constructs known to work
in Strata today:
  - Integer arithmetic (+, -, *)
  - Integer comparisons (<, <=, >, >=, ==, !=)
  - Boolean logic (and, or, not)
  - String concatenation
  - If/else branching
  - Floor division (//) and modulo (%)
  - Unary negation

The **unrestricted generators** (--unrestricted flag) add ~60 generators
for constructs that may be beyond Strata's current support. See
gen_unrestricted.py for the full list. Programs using unsupported
constructs will be reported as SKIP by hypothesmith.sh, not as failures.

## Reproducibility

Both modes are fully deterministic given the same --seed value:
  - Syntax mode: sets HYPOTHESIS_SEED and uses derandomize=True
  - Semantic mode: seeds Python's random module

## Usage

    python gen_random_python.py --mode syntax --output-dir /tmp/fuzz --seed 42
    python gen_random_python.py --mode semantic --output-dir /tmp/fuzz --seed 42
    python gen_random_python.py --mode semantic --output-dir /tmp/fuzz --seed 42 --unrestricted

## Options

    --mode {syntax,semantic}   Generation mode (required)
    --output-dir DIR           Directory for generated .py files (required)
    --max-examples N           Number of programs to generate (default: 100)
    --max-nodes N              Max AST nodes per program, syntax mode only (default: 50)
    --seed S                   Random seed for reproducibility
    --unrestricted             Include generators beyond what Strata supports today
"""

import argparse
import ast
import os
import random
import sys
from pathlib import Path


# =============================================================================
# Syntax mode
# =============================================================================

def gen_syntax(args):
    """Generate syntactically valid Python via hypothesmith.

    Uses hypothesmith's ``from_grammar()`` strategy, which inverts the Python
    grammar to produce random valid source code. The ``auto_target=True``
    option enables Hypothesis's hill-climbing search to drive toward larger
    and more complex programs over time.

    Programs are filtered to have between 2 and ``max_nodes`` AST nodes.
    This keeps them small enough to debug while still being non-trivial.
    """
    import hypothesmith
    from hypothesis import given, settings, HealthCheck, Phase

    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    count = [0]

    @settings(
        max_examples=args.max_examples,
        suppress_health_check=[HealthCheck.too_slow, HealthCheck.filter_too_much],
        database=None,
        # When a seed is provided, use derandomize mode so that the same
        # seed always produces the same sequence of examples.
        derandomize=args.seed is not None,
        phases=[Phase.generate],
    )
    @given(source_code=hypothesmith.from_grammar(auto_target=True))
    def collect(source_code):
        try:
            tree = ast.parse(source_code)
            nodes = len(list(ast.walk(tree)))
        except SyntaxError:
            return
        # Skip trivial programs (empty files, bare comments).
        if nodes < 2:
            return
        # Skip programs that are too large to debug easily.
        if nodes > args.max_nodes:
            return
        idx = count[0]
        count[0] += 1
        p = out / f"fuzz_syntax_{idx:04d}.py"
        p.write_text(source_code)

    if args.seed is not None:
        os.environ["HYPOTHESIS_SEED"] = str(args.seed)
    collect()
    print(f"Generated {count[0]} syntax-mode programs in {out}")


# =============================================================================
# Semantic mode — base generators
# =============================================================================
# Each generator function returns a string containing one or more indented
# Python statements (at 4-space indent) that declare variables, perform
# operations, and assert the expected result. The expected values are
# computed by CPython at generation time, so any disagreement with Strata
# indicates a bug in Strata's semantic model.

def _rand_int():
    """Random integer in [-100, 100]."""
    return random.randint(-100, 100)

def _rand_bool():
    """Random boolean."""
    return random.choice([True, False])

def _rand_str():
    """Random short string from a fixed vocabulary."""
    return random.choice(["hello", "world", "foo", "bar", "", "abc", "x"])

def _gen_int_arithmetic():
    """Integer addition, subtraction, or multiplication."""
    a, b = _rand_int(), _rand_int()
    op_name, op_sym, result_fn = random.choice([
        ("add", "+", lambda a, b: a + b),
        ("sub", "-", lambda a, b: a - b),
        ("mul", "*", lambda a, b: a * b),
    ])
    result = result_fn(a, b)
    return (
        f"    a: int = {a}\n"
        f"    b: int = {b}\n"
        f"    r: int = a {op_sym} b\n"
        f'    assert r == {result}, "int {op_name}"\n'
    )

def _gen_int_comparison():
    """Integer comparison with all six operators."""
    a, b = _rand_int(), _rand_int()
    op_sym, result = random.choice([
        ("<", a < b), ("<=", a <= b), (">", a > b),
        (">=", a >= b), ("==", a == b), ("!=", a != b),
    ])
    return (
        f"    a: int = {a}\n"
        f"    b: int = {b}\n"
        f'    assert (a {op_sym} b) == {result}, "int cmp"\n'
    )

def _gen_bool_logic():
    """Boolean and/or."""
    a, b = _rand_bool(), _rand_bool()
    op_name, op_sym, result_fn = random.choice([
        ("and", "and", lambda a, b: a and b),
        ("or", "or", lambda a, b: a or b),
    ])
    result = result_fn(a, b)
    return (
        f"    a: bool = {a}\n"
        f"    b: bool = {b}\n"
        f"    r: bool = a {op_sym} b\n"
        f'    assert r == {result}, "bool {op_name}"\n'
    )

def _gen_str_concat():
    """String concatenation."""
    a, b = _rand_str(), _rand_str()
    result = a + b
    return (
        f"    a: str = {a!r}\n"
        f"    b: str = {b!r}\n"
        f"    r: str = a + b\n"
        f'    assert r == {result!r}, "str concat"\n'
    )

def _gen_if_else():
    """If/else with a known branch outcome."""
    cond_val = _rand_bool()
    a, b = _rand_int(), _rand_int()
    expected = a if cond_val else b
    return (
        f"    cond: bool = {cond_val}\n"
        f"    if cond:\n"
        f"        r: int = {a}\n"
        f"    else:\n"
        f"        r: int = {b}\n"
        f'    assert r == {expected}, "if_else"\n'
    )

def _gen_floor_div():
    """Floor division (Python's // operator)."""
    a = _rand_int()
    b = random.choice([x for x in range(-10, 11) if x != 0])
    result = a // b
    return (
        f"    a: int = {a}\n"
        f"    b: int = {b}\n"
        f"    r: int = a // b\n"
        f'    assert r == {result}, "floor div"\n'
    )

def _gen_modulo():
    """Modulo (Python's % operator, which uses floored division)."""
    a = _rand_int()
    b = random.choice([x for x in range(-10, 11) if x != 0])
    result = a % b
    return (
        f"    a: int = {a}\n"
        f"    b: int = {b}\n"
        f"    r: int = a % b\n"
        f'    assert r == {result}, "modulo"\n'
    )

def _gen_negation():
    """Unary negation."""
    a = _rand_int()
    return (
        f"    a: int = {a}\n"
        f"    r: int = -a\n"
        f'    assert r == {-a}, "negation"\n'
    )

def _gen_not():
    """Boolean not."""
    a = _rand_bool()
    return (
        f"    a: bool = {a}\n"
        f"    r: bool = not a\n"
        f'    assert r == {not a}, "bool not"\n'
    )

# The base generator list — only constructs known to work in Strata today.
GENERATORS = [
    _gen_int_arithmetic,
    _gen_int_comparison,
    _gen_bool_logic,
    _gen_str_concat,
    _gen_if_else,
    _gen_floor_div,
    _gen_modulo,
    _gen_negation,
    _gen_not,
]


def _get_generators(unrestricted):
    """Return the list of generators to use.

    With --unrestricted, loads the extended generators from
    gen_unrestricted.py (in the same directory) and appends them to the
    base list. This produces programs using Python constructs that Strata
    may not support yet, which is useful for discovering coverage gaps.
    """
    if not unrestricted:
        return GENERATORS
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "gen_unrestricted",
        os.path.join(os.path.dirname(__file__), "gen_unrestricted.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return GENERATORS + mod.UNRESTRICTED_GENERATORS


# =============================================================================
# Semantic mode — program assembly
# =============================================================================

def gen_semantic(args):
    """Generate typed Python programs with known-true assertions.

    Each program contains 1–5 randomly chosen blocks, wrapped in a
    ``def main(): ... main()`` structure to match Strata's test convention.
    The blocks are independent — each declares its own variables and asserts
    its own expected result.
    """
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    if args.seed is not None:
        random.seed(args.seed)

    generators = _get_generators(args.unrestricted)

    for i in range(args.max_examples):
        # Pick 1–5 random blocks per program.
        n_blocks = random.randint(1, 5)
        blocks = [random.choice(generators)() for _ in range(n_blocks)]

        # Wrap in a function and call it (matches Strata test convention).
        body = "\n".join(blocks)
        program = f"def main():\n{body}\nmain()\n"

        p = out / f"fuzz_semantic_{i:04d}.py"
        p.write_text(program)

    print(f"Generated {args.max_examples} semantic-mode programs in {out}")


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=["syntax", "semantic"], required=True,
                        help="Generation mode: 'syntax' for grammar-based, "
                             "'semantic' for typed programs with assertions")
    parser.add_argument("--output-dir", required=True,
                        help="Directory for generated .py files (created if needed)")
    parser.add_argument("--max-examples", type=int, default=100,
                        help="Number of programs to generate (default: 100)")
    parser.add_argument("--max-nodes", type=int, default=50,
                        help="Max AST nodes per program, syntax mode only (default: 50)")
    parser.add_argument("--seed", type=int, default=None,
                        help="Random seed for reproducibility")
    parser.add_argument("--unrestricted", action="store_true",
                        help="Include generators for Python constructs beyond "
                             "what Strata supports today")
    args = parser.parse_args()

    if args.mode == "syntax":
        gen_syntax(args)
    else:
        gen_semantic(args)


if __name__ == "__main__":
    main()
