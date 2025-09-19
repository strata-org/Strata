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

def gen_dialect_imp(args):
    if not os.path.isdir(args.output_dir):
        print(f"Directory {args.output_dir} does not exist.", file=sys.stderr)
        exit(1)
    output = f"{args.output_dir}/Python.dialect.st.ion"
    with open(output, 'wb') as w:
        ion.dump(stratap.Python.to_ion(), w, binary=True)
    print(f"Wrote Python dialect to {output}")

def parse_python_imp(args):
    with open(args.python, 'r') as r:
        (_, p) = stratap.parse_module(r.read(), args.python)
    with open(args.output, 'wb') as w:
        ion.dump(p.to_ion(), w, binary=True)

def main():
    parser = argparse.ArgumentParser(
                    prog='strata_python',
                    description='Strata interface to Python parser')
    subparsers = parser.add_subparsers(help="subcommand help")

    gen_dialect_command = subparsers.add_parser('dialect', help='Create Strata dialect.')
    gen_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    gen_dialect_command.set_defaults(func=gen_dialect_imp)

    parse_command = subparsers.add_parser('parse', help='Parse a Python file')
    parse_command.add_argument('python', help='Path ')
    parse_command.add_argument('output', help='Path to write Strata')
    parse_command.set_defaults(func=parse_python_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()