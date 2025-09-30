# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

#!/usr/bin/env python3

"""
Command line script for exporting Python dialect and program to files.
"""

import argparse
import amazon.ion.simpleion as ion
from strata import Dialect, Program
import strata.pythonast as pythonast
import sys
import strata.pythonssa as pythonssa
from strata.pythonssa import PythonSSA, py_to_ssa
from pathlib import Path

dialect_choices : dict[str, Dialect] = {
    'PythonAST' : pythonast.PythonAST,
    'PythonSSA' : PythonSSA,
}

def write_dialect(dialectName : str, dir : Path):
    dialect = dialect_choices.get(dialectName)
    if dialect is None:
        print(f"Unknown dialect {dialectName}", file=sys.stderr)
        exit(1)

    if not dir.is_dir():
        print(f"Directory {dir} does not exist.", file=sys.stderr)
        exit(1)
    output = dir / f"{dialect.name}.dialect.st.ion"
    with output.open('wb') as w:
        ion.dump(dialect.to_ion(), w, binary=True)
    print(f"Wrote {dialect.name} dialect to {output}")

def parse_ast(contents : bytes, path : Path) -> Program:
    try:
        (_, p) = pythonast.parse_module(contents, path)
    except SyntaxError as e:
        print(f"Error parsing {path}:\n  {e}", file=sys.stderr)
        exit(1)
    return p

def parse_ssa(contents : bytes, path : Path):
    try:
        funs = py_to_ssa(path, contents)
    except SyntaxError as e:
        print(f"Error parsing {path}:\n  {e}", file=sys.stderr)
        exit(1)
    p = Program(PythonSSA.name)
    for f in funs:
        p.add(f.to_strata())
    return p

def py_to_strata_imp(args):
    dialect_name = args.dialect
    match dialect_name:
        case 'PythonAST':
            fn = parse_ast
        case 'PythonSSA':
            fn = parse_ssa
        case _:
            print(f"Unknown dialect {dialect_name}", file=sys.stderr)
            exit(1)
    path = Path(args.python)
    with path.open('rb') as r:
        contents = r.read()
    p = fn(contents, path)
    with open(args.output, 'wb') as w:
        ion.dump(p.to_ion(), w, binary=True)

def check_ssa_imp(args):
    path = Path(args.dir)
    if path.is_dir():
        success = 0
        total = 0
        for p in path.glob('**/*.py'):
            total += 1
            try:
                with p.open('rb') as r:
                    contents = r.read()
                fns = py_to_ssa(p, contents)
            except SyntaxError as e:
                print(f'{p} {type(e).__name__}: {e}')
                total -= 1
                continue
            except Exception as e:
                print(f'{p} {type(e).__name__}: {e}')
                continue
            for fn in fns:
                _ = fn.to_ion()
            success += 1
        print(f'Analyzed {success} of {total} files.')
    else:
        with path.open('rb') as r:
            contents = r.read()
        fns = py_to_ssa(path, contents)
        for fn in fns:
            _ = fn.to_ion()

def debug_ssa_imp(args):
    path = Path(args.python)
    with path.open('rb') as r:
        contents = r.read()

    (c, _) = pythonssa.compile_path(path, contents)

    print(f'Root: {c.co_qualname}')
    globals = pythonssa.Globals()
    pythonssa.find_code(globals, 0, c)

def missing_imp(args):
    dir = Path(args.dir)
    assert dir.is_dir()
    missing = pythonssa.MissingInstructions()
    missing.analyze_dir(dir)

def main():
    parser = argparse.ArgumentParser(
                    prog='strata_python',
                    description='Strata interface to Python parser')
    subparsers = parser.add_subparsers(help="subcommand help")

    write_python_dialect_command = subparsers.add_parser('dialect', help='Write Python Strata dialect to directory.')
    write_python_dialect_command.add_argument('dialect', help='Which dialect to generate.', choices=dialect_choices.keys())
    write_python_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    write_python_dialect_command.set_defaults(
        func=lambda args:
            write_dialect(args.dialect, Path(args.output_dir)))

    py_to_strata_command = subparsers.add_parser('py_to_strata', help='Parse a Python file')
    py_to_strata_command.add_argument('dialect', help='Which dialect to use', choices=dialect_choices.keys())
    py_to_strata_command.add_argument('python', help='Path of file to read.')
    py_to_strata_command.add_argument('output', help='Path to write Strata')
    py_to_strata_command.set_defaults(func=py_to_strata_imp)

    debug_ssa_command = subparsers.add_parser('debug_ssa', help='Disassemble a Python file')
    debug_ssa_command.add_argument('python', help='Path of Python file to translate.')
    debug_ssa_command.set_defaults(func=debug_ssa_imp)

    missing_command = subparsers.add_parser('missing_ssa', help='Check for missing instructions in Python files.')
    missing_command.add_argument('dir', help='Directory with Python files to analyze.')
    missing_command.set_defaults(func=missing_imp)

    checkssa_command = subparsers.add_parser('check_ssa', help='Check SSA conversion doesn\'t crash on Python files.')
    checkssa_command.add_argument('dir', help='Directory with Python files to analyze.')
    checkssa_command.set_defaults(func=check_ssa_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()
