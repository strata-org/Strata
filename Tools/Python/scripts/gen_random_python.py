#!/usr/bin/env python3
# Copyright Strata Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""
Generate random Python programs for fuzz-testing Strata's Python front-end.

Two modes:
  --mode syntax   Use hypothesmith to generate syntactically valid Python.
                  Tests the parser pipeline (py_to_strata + Ion round-trip).
  --mode semantic Use a custom generator to produce typed programs with
                  assertions that have known outcomes. Tests that
                  pyAnalyzeLaurel correctly models Python semantics.

Size control:
  --max-examples N   Number of Hypothesis examples to try (default: 100).
  --max-nodes N      Filter: discard programs with more than N AST nodes (default: 50).
  --seed S           Fixed Hypothesis seed for reproducibility.
"""

import argparse
import ast
import os
import random
import sys
from pathlib import Path


def gen_syntax(args):
    """Generate syntactically valid Python via hypothesmith."""
    import hypothesmith
    from hypothesis import given, settings, HealthCheck, Phase

    phases = [Phase.generate]
    if args.seed is not None:
        phases = [Phase.generate]

    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    count = [0]

    health_checks = [HealthCheck.too_slow, HealthCheck.filter_too_much]

    @settings(
        max_examples=args.max_examples,
        suppress_health_check=health_checks,
        database=None,
        derandomize=args.seed is not None,
        phases=phases,
    )
    @given(source_code=hypothesmith.from_grammar(auto_target=True))
    def collect(source_code):
        try:
            tree = ast.parse(source_code)
            nodes = len(list(ast.walk(tree)))
        except SyntaxError:
            return
        if nodes < 2:
            return
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


# ---------------------------------------------------------------------------
# Semantic mode: build programs with typed variables and checkable assertions
# ---------------------------------------------------------------------------

def _rand_int():
    return random.randint(-100, 100)

def _rand_bool():
    return random.choice([True, False])

def _rand_str():
    words = ["hello", "world", "foo", "bar", "", "abc", "x"]
    return random.choice(words)

def _gen_int_arithmetic():
    """Generate an int arithmetic block with a true assertion."""
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
    """Generate an int comparison with a true assertion."""
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
    """Generate a boolean logic block with a true assertion."""
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
    """Generate a string concatenation with a true assertion."""
    a, b = _rand_str(), _rand_str()
    result = a + b
    return (
        f"    a: str = {a!r}\n"
        f"    b: str = {b!r}\n"
        f"    r: str = a + b\n"
        f'    assert r == {result!r}, "str concat"\n'
    )

def _gen_if_else():
    """Generate an if/else with a true assertion about the result."""
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
    """Generate floor division with a true assertion."""
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
    """Generate modulo with a true assertion."""
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
    """Generate unary negation with a true assertion."""
    a = _rand_int()
    return (
        f"    a: int = {a}\n"
        f"    r: int = -a\n"
        f'    assert r == {-a}, "negation"\n'
    )

def _gen_not():
    """Generate boolean not with a true assertion."""
    a = _rand_bool()
    return (
        f"    a: bool = {a}\n"
        f"    r: bool = not a\n"
        f'    assert r == {not a}, "bool not"\n'
    )

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


def gen_semantic(args):
    """Generate typed Python programs with known-true assertions."""
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    if args.seed is not None:
        random.seed(args.seed)

    for i in range(args.max_examples):
        # Pick 1-5 random blocks per program
        n_blocks = random.randint(1, 5)
        blocks = [random.choice(GENERATORS)() for _ in range(n_blocks)]

        # Wrap in a function and call it (matches Strata test convention)
        body = "\n".join(blocks)
        program = f"def main():\n{body}\nmain()\n"

        p = out / f"fuzz_semantic_{i:04d}.py"
        p.write_text(program)

    print(f"Generated {args.max_examples} semantic-mode programs in {out}")


def main():
    parser = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=["syntax", "semantic"], required=True)
    parser.add_argument("--output-dir", required=True, help="Directory for generated .py files")
    parser.add_argument("--max-examples", type=int, default=100)
    parser.add_argument("--max-nodes", type=int, default=50,
                        help="Max AST nodes per program (syntax mode)")
    parser.add_argument("--seed", type=int, default=None,
                        help="Random seed for reproducibility")
    args = parser.parse_args()

    if args.mode == "syntax":
        gen_syntax(args)
    else:
        gen_semantic(args)


if __name__ == "__main__":
    main()
