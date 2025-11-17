# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
#!/usr/bin/env python3

"""
Command line script for exporting Python dialect and program to files.
"""
import amazon.ion.simpleion as ion
import argparse
from strata import Dialect, Program
import strata.pythonast as pythonast
import sys
from pathlib import Path

def write_dialect(dir : Path):
    dialect = pythonast.PythonAST

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

def py_to_strata_imp(args):
    path = Path(args.python)
    with path.open('rb') as r:
        contents = r.read()
    p = parse_ast(contents, path)
    with open(args.output, 'wb') as w:
        ion.dump(p.to_ion(), w, binary=True)

def check_ast_imp(args):
    path = Path(args.dir)

    if path.is_dir():
        files = path.glob('**/*.py')
    else:
        files = [path]

    success = 0
    total = 0
    for p in files:
        total += 1
        try:
            with p.open('rb') as r:
                contents = r.read()
            _ = pythonast.parse_module(contents, p)
        except SyntaxError as e:
            print(f'{p} {type(e).__name__}: {e}')
            total -= 1
            continue
        except Exception as e:
            print(f'{p} {type(e).__name__}: {e}')
            continue
        success += 1
    print(f'Analyzed {success} of {total} files.')

def main():
    parser = argparse.ArgumentParser(
                    prog='strata_python',
                    description='Strata interface to Python parser')
    subparsers = parser.add_subparsers(help="subcommand help")

    write_python_dialect_command = subparsers.add_parser('dialect', help='Write Python Strata dialect to directory.')
    write_python_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    write_python_dialect_command.set_defaults(
        func=lambda args:
            write_dialect(Path(args.output_dir)))

    py_to_strata_command = subparsers.add_parser('py_to_strata', help='Parse a Python file')
    py_to_strata_command.add_argument('python', help='Path of file to read.')
    py_to_strata_command.add_argument('output', help='Path to write Strata')
    py_to_strata_command.set_defaults(func=py_to_strata_imp)

    checkast_command = subparsers.add_parser('check_ast', help='Check AST parser doesn\'t crash on Python files.')
    checkast_command.add_argument('dir', help='Directory with Python files to analyze.')
    checkast_command.add_argument('-f', '--features', action='store_true', help='Print out features used in SSA.')
    checkast_command.set_defaults(func=check_ast_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()