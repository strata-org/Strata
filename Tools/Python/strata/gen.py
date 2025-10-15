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
from dataclasses import dataclass

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
    names = pythonssa.Translator.__dict__
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

@dataclass
class Function:
    name : str
    args : list[str]
    blocks : list[pythonssa.Block]

def extract_functions(prev : list[Function], globals : pythonssa.Globals, code):

    codeType = type(code)

    blocks = pythonssa.generate_blocks(globals, code)

    args = [ code.co_varnames[i] for i in range(code.co_argcount)]

    prev.append(Function(code.co_qualname, args, blocks))

    for c in code.co_consts:
        if isinstance(c, codeType):
            extract_functions(prev, globals, c)


def py_to_ssa(path : Path):

    (code, _) = pythonssa.compile_path(Path(path))
    codeType = type(code)

    globals = pythonssa.Globals()
    prev = []
    extract_functions(prev, globals, code)
    return prev

def print_functions(fns : list[Function]):
    for f in fns:
        args = ', '.join(f.args)
        print(f'{f.name}({args}):')
        for (i, b) in enumerate(f.blocks):
            print(f'  L{i}:')
            for s in b.statements:
                print(f'    {s}')

def check_ssa_imp(args):
    path = Path(args.dir)
    if path.is_dir():
        success = 0
        total = 0
        for p in path.glob('**/*.py'):
            total += 1
            try:
                py_to_ssa(p)
            except SyntaxError as e:
                print(f'{p} {type(e).__name__}: {e}')
                total -= 1
                continue
            except Exception as e:
                print(f'{p} {type(e).__name__}: {e}')
                continue
            success += 1
        print(f'Analyzed {success} of {total} files.')
    else:
        py_to_ssa(path)

def dis_python_imp(args):
    path = Path(args.python)

    funs = py_to_ssa(path)
    print_functions(funs)

def debug_ssa_imp(args):
    path = Path(args.python)
    with path.open('r') as r:
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

    debug_ssa_command = subparsers.add_parser('debug_ssa', help='Disassemble a Python file')
    debug_ssa_command.add_argument('python', help='Path of Python file to translate.')
    debug_ssa_command.set_defaults(func=debug_ssa_imp)

    missing_command = subparsers.add_parser('missing', help='Check for missing instructions in Python files.')
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
