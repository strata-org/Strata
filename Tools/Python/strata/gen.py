# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""
Command line script for exporting Python dialect and program to files.
"""
#!/usr/bin/env python3
import argparse
import os
import amazon.ion.simpleion as ion
from strata import python as stratap
import sys

import ast
import dis

def gen_dialect_imp(args):
    if not os.path.isdir(args.output_dir):
        print(f"Directory {args.output_dir} does not exist.", file=sys.stderr)
        exit(1)
    output = f"{args.output_dir}/Python.dialect.st.ion"
    with open(output, 'wb') as w:
        ion.dump(stratap.Python.to_ion(), w, binary=True)
    print(f"Wrote Python dialect to {output}")

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

def find_code(indent0 : str, co):
    codeType = type(co)
    consts = co.co_consts
    assert isinstance(consts, tuple)
    print(f'{indent0}Constants:')
    indent = indent0 + '  '
    for i, c in enumerate(consts):
        if isinstance(c, codeType):
            print(f'{indent}{i}: code({c.co_name})')
            find_code(indent, c)
        elif isinstance(c, str):
            print(f'{indent}{i}: str({repr(c)})')
        elif isinstance(c, int):
            print(f'{indent}{i}: int({repr(c)})')
        elif isinstance(c, tuple):
            for v in c:
                assert isinstance(v, str)
            tp = ','.join([repr(v) for v in c])
            print(f'{indent}{i}: tuple({tp})')
        elif c is None:
            print(f'{indent}{i}: None')
        else:
            print(f'{indent}{i}: {type(c)}')
    print(f'{indent0}Instructions:')
    for i, instr in enumerate(dis.get_instructions(co)):
        lbl = "" if instr.label is None else f'L{instr.label}: '
        print(f'{indent0}  {lbl}{instr.opname} {instr.arg} ({instr.argval})')
#        print(f'{indent0}{instr}', end=None)

def print_insn_info():
    size = max(v for (_, v) in dis.opmap.items()) + 1
    idxmap : list = [None] * size
    for (name, code) in dis.opmap.items():
        assert isinstance(code, int)
        assert idxmap[code] is None
        idxmap[code] = (name, False)

    for hasarg in dis.hasarg:
        assert isinstance(hasarg, int)
        assert 0 <= hasarg and hasarg < len(idxmap)
        (name, h) = idxmap[hasarg]
        assert h == False
        idxmap[hasarg] = (name, True)

    min_instrumentedcode : int = 236
    count = 0
    for i in range(min(len(idxmap), min_instrumentedcode)):
        r = idxmap[i]
        if r is None:
            continue
        (name, hasarg) = r
        count = count + 1
        print(f'{i}: {name} {hasarg}')

    print(f'Total: {count}')


def dis_python_imp(args):
    path = args.python
    with open(path, 'r') as r:
        try:
            bytes = r.read()
        except SyntaxError as e:
            print(f"Error parsing {path}:\n  {e}", file=sys.stderr)
            exit(1)
    a = ast.parse(bytes, mode='exec', filename=path)
    print(ast.dump(a, indent=2))
    return
    c = compile(bytes, mode='exec', filename=path)
#    for i in c.co_lines ():
#        print(i)
#    print(c.co_code)
    bc = dis.Bytecode(bytes)
    print(f'Root: {bc.codeobj.co_name}')
    find_code('', bc.codeobj)
    return
    for c in consts:
        if c is None:
            pass
        elif isinstance(c, int) or isinstance(c, str):
            pass
        elif isinstance(c, codeType):
            print(c.co_name)
            print(c.co_flags)
        else:
            pass

    #for k in type(c).__dict__.keys():
    #    print(k)
#    help(bc)

    resumeIdx = dis.opmap['RESUME']
    loadConst = dis.opmap['LOAD_CONST']

    for i in bc:
        assert isinstance(i, dis.Instruction)
        if i.opcode == resumeIdx:
            pass
        elif i.opcode == loadConst:
            print(f'{i.opname} {i.argrepr}')
            print('')
        else:
            pass
#        assert i.opcode == resumeIdx, f'Bad op {i.opname} {i}'

#        print(instr.opname)


#    r = dis.dis(bytes)
    #print(ast.dump(a, indent=4))

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

    dis_command = subparsers.add_parser('dis', help='Disassemble a Python file')
    dis_command.add_argument('python', help='Path of Python file to translate.')
    dis_command.set_defaults(func=dis_python_imp)


    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()
