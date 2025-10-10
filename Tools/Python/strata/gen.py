# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

#!/usr/bin/env python3

"""
Command line script for exporting Python dialect and program to files.
"""

import argparse
import amazon.ion.simpleion as ion
from strata import Dialect
from strata import python as stratap
import sys
from strata.pythond import InstructionMap, PythonD
import strata.pythonssa as pythonssa
from strata.pythonssa import PythonSSA
from pathlib import Path

import ast
import dis
from dis import Instruction

def write_dialect(dialect : Dialect, dir : Path):
    if not dir.is_dir():
        print(f"Directory {dir} does not exist.", file=sys.stderr)
        exit(1)
    output = dir / f"{dialect.name}.dialect.st.ion"
    with output.open('wb') as w:
        ion.dump(dialect.to_ion(), w, binary=True)
    print(f"Wrote {dialect.name} dialect to {output}")

def gen_dialect_imp(args):
    write_dialect(stratap.Python, Path(args.output_dir))

def parse_python_imp(args):
    path = args.python
    with open(path, 'rb') as r:
        try:
            (_, p) = stratap.parse_module(r.read(), path)
        except SyntaxError as e:
            print(f"Error parsing {path}:\n  {e}", file=sys.stderr)
            exit(1)
    with open(args.output, 'wb') as w:
        ion.dump(p.to_ion(), w, binary=True)

def gen_pythonssa_dialect_imp(args):
    write_dialect(PythonSSA, Path(args.output_dir))

def print_insn_info():
    """
    Prints out dis instruction information including the opcode.
    """
    m = InstructionMap()
    min_instrumentedcode : int = 236
    count = 0
    for i in range(min(len(m.idxmap), min_instrumentedcode)):
        d = m.idxmap[i]
        if d is None:
            continue
        count = count + 1
        print(f'{i}: {d.name} {d.hasarg}')
    print(f'Total: {count}')

def print_ast(bytes, path):
    a = ast.parse(bytes, mode='exec', filename=path)
    print(ast.dump(a, indent=2))

def print_supported_stata():
    """Analyzes dis.opmap to print supported operations."""
    names = pythonssa.Spec.__dict__
    total = 0
    supported = 0
    for (op, idx) in dis.opmap.items():
        if idx > 119:
            continue
        total = total + 1
        if op in names:
            supported = supported + 1
        print(f'{op}: {op in names}')
    print(f"Supports {supported} of {total} operations")

def dis_python_imp(args):
    path = args.python
    with open(path, 'r') as r:
        try:
            bytes = r.read()
        except SyntaxError as e:
            raise e

    (c, _) = pythonssa.compile_path(Path(path))

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

    gen_dialect_command = subparsers.add_parser('dialect', help='Create Strata dialect.')
    gen_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    gen_dialect_command.set_defaults(func=gen_dialect_imp)

    parse_command = subparsers.add_parser('parse', help='Parse a Python file')
    parse_command.add_argument('python', help='Path of file to read.')
    parse_command.add_argument('output', help='Path to write Strata')
    parse_command.set_defaults(func=parse_python_imp)

    gend_dialect_command = subparsers.add_parser('pythonssa', help='Create Strata PythonSSA dialect.')
    gend_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    gend_dialect_command.set_defaults(func=gen_pythonssa_dialect_imp)

    dis_command = subparsers.add_parser('dis', help='Disassemble a Python file')
    dis_command.add_argument('python', help='Path of Python file to translate.')
    dis_command.set_defaults(func=dis_python_imp)

    missing_command = subparsers.add_parser('missing', help='Check for missing instructions in Python files.')
    missing_command.add_argument('dir', help='Directory with Python files to analyze.')
    missing_command.set_defaults(func=missing_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()
