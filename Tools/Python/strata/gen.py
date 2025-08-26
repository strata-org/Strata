#!/usr/bin/env python3
import argparse
import ast
from dataclasses import dataclass
import os
import typing
import types
import amazon.ion.simpleion as ion
import strata
from strata import ArgDecl, QualifiedIdent, SyntaxCat
import sys

init_num_cat = SyntaxCat(QualifiedIdent("Init.Num"))
init_str_cat = SyntaxCat(QualifiedIdent("Init.Str"))
init_option = QualifiedIdent("Init.Option")
init_seq = QualifiedIdent("Init.Seq")

dialect_name = "Python"
python_int_cat = SyntaxCat(QualifiedIdent(dialect_name, "int"))
python_constant_cat = SyntaxCat(QualifiedIdent(dialect_name, "constant"))
python_IntPos = QualifiedIdent(dialect_name, "IntPos")
python_IntNeg = QualifiedIdent(dialect_name, "IntNeg")

python_ConTrue = QualifiedIdent(dialect_name, "ConTrue")
python_ConFalse = QualifiedIdent(dialect_name, "ConFalse")
python_ConPos = QualifiedIdent(dialect_name, "ConPos")
python_ConNeg = QualifiedIdent(dialect_name, "ConNeg")
python_ConString = QualifiedIdent(dialect_name, "ConString")
python_ConNone = QualifiedIdent(dialect_name, "ConNone")

@dataclass
class OpArg:
    name : str
    ddm_name : str
    cat : SyntaxCat

class Op:
    name : str
    args: list[tuple[str, type]]
    category: SyntaxCat

    def __init__(self, cats, name : str, op : type, category : SyntaxCat):
        def as_atom_type(tp) -> SyntaxCat:
            if tp is int:
                return python_int_cat
            elif tp is str:
                return init_str_cat
            elif tp is object:
                return python_constant_cat
            else:
                return cats[tp]

        self.name = name
        try:
            field_types = op._field_types
        except AttributeError:
            field_types = dict()
        used_names = { "category", "op", "type", "fn", "metadata" }
        op_args = []
        for (f, tp) in field_types.items():
            if f in used_names:
                idx = 0
                while f"{f}{idx}" in used_names:
                    idx += 1
                ddm_name = f"{f}{idx}"
            else:
                ddm_name = f
            if isinstance(tp, types.UnionType):
                args = typing.get_args(tp)
                assert len(args) == 2
                opt_cat = as_atom_type(args[0])
                assert args[1] is types.NoneType
                cat = SyntaxCat(init_option, [ opt_cat ])
            elif isinstance(tp, types.GenericAlias):
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                cat = SyntaxCat(init_seq, [ as_atom_type(args[0])])
            else:
                cat = as_atom_type(tp)
            op_args.append(OpArg(f, ddm_name, cat))
        self.args = op_args
        self.category = category

    def op_decl(self) -> strata.OpDecl:
        op_args = [ ArgDecl(a.ddm_name, a.cat) for a in self.args ]
        return strata.OpDecl(self.name, op_args, self.category)

def gen_cats() -> dict[type, SyntaxCat]:
    cats = {}
    for c in ast.AST.__subclasses__():
        name = c.__name__
        assert name not in { "int", "constant" }

        if c is ast.mod:
            cat = SyntaxCat(QualifiedIdent("Init.Command"))
        else:
            cat = SyntaxCat(QualifiedIdent(dialect_name, name))
        cats[c] = cat
    return cats

def gen_ops(cats : dict[type, SyntaxCat]) -> dict[type, Op]:
    ops = {}
    for (cat, cat_ref) in cats.items():
        cat_ops = [ (op, Op(cats, op.__name__, op, cat_ref)) for op in cat.__subclasses__() ]

        try:
            field_types = cat._field_types
            assert len(cat_ops) == 0
            op_name = f"mk_{cat.__name__}"
            cat_ops = [ (cat, Op(cats, op_name, cat, cat_ref)) ]
        except AttributeError:
            assert len(cat_ops) > 0

        for (op, opd) in cat_ops:
            ops[op] = opd
    return ops

def gen_dialect(cats : dict[type, SyntaxCat], ops : dict[type, Op]):
    d = strata.Dialect(dialect_name)
    d.add_import("Init")
    d.add(strata.SynCatDecl("int"))
    d.add(strata.OpDecl("IntPos", [ArgDecl("v", init_num_cat)], python_int_cat))
    d.add(strata.OpDecl("IntNeg", [ArgDecl("v", init_num_cat)], python_int_cat))
    d.add(strata.SynCatDecl("constant"))
    d.add(strata.OpDecl("ConTrue", [], python_constant_cat))
    d.add(strata.OpDecl("ConFalse", [], python_constant_cat))
    d.add(strata.OpDecl("ConPos", [ArgDecl("v", init_num_cat)], python_constant_cat))
    d.add(strata.OpDecl("ConNeg", [ArgDecl("v", init_num_cat)], python_constant_cat))
    d.add(strata.OpDecl("ConString", [ArgDecl("v", init_str_cat)], python_constant_cat))
    d.add(strata.OpDecl("ConNone", [], python_constant_cat))

    for c in cats:
        if c is ast.mod:
            continue
        d.add(strata.SynCatDecl(c.__name__, []))
    for op in ops.values():
        d.add(op.op_decl())

    return d

def recurse_atom(ops : dict[type, Op], t : object, cat : SyntaxCat) -> strata.Arg:
    if cat == python_int_cat:
        assert isinstance(t, int)
        if t >= 0:
            return strata.Operation(python_IntPos, [strata.NumLit(t)])
        else:
            return strata.Operation(python_IntNeg, [strata.NumLit(-t)])
    elif cat == init_str_cat:
        assert isinstance(t, str)
        return strata.StrLit(t)
    elif cat == python_constant_cat:
        if isinstance(t, bool):
            if t:
                return strata.Operation(python_ConTrue)
            else:
                return strata.Operation(python_ConFalse)
        if isinstance(t, int):
            if t >= 0:
                return strata.Operation(python_ConPos, [strata.NumLit(t)])
            else:
                return strata.Operation(python_ConNeg, [strata.NumLit(-t)])
        if isinstance(t, str):
            return strata.Operation(python_ConString, [strata.StrLit(t)])
        if t is None:
            return strata.Operation(python_ConNone)
        raise ValueError(f"Unsupported constant type {type(t)}")
    else:
        return recurse(ops, t)

    assert False

def recurse(ops : dict[type, Op], t : object) -> strata.Operation:
    tp = type(t)

    op = ops[type(t)]
    args = []
    for a in op.args:
        v = getattr(t, a.name)
        cat = a.cat
        if cat.ident == init_option:
            if v is None:
                r = None
            else:
                r = strata.SomeArg(recurse_atom(ops, v, cat.args[0]))
        elif cat.ident == init_seq:
            assert isinstance(v, list)
            arg_cat = cat.args[0]
            r = strata.Seq([ recurse_atom(ops, e, arg_cat) for e in v])
        else:
            r = recurse_atom(ops, v, cat)
        args.append(r)
    return strata.Operation(strata.QualifiedIdent(dialect_name, op.name), args)

def gen_dialect_imp(args):
    cats = gen_cats()
    ops = gen_ops(cats)
    d = gen_dialect(cats, ops)
    if not os.path.isdir(args.output_dir):
        print(f"Directory {args.output_dir} does not exist.", file=sys.stderr)
        exit(1)
    output = f"{args.output_dir}/{dialect_name}.dialect.st.ion"
    with open(output, 'wb') as w:
        ion.dump(d.to_ion(), w, binary=True)
    print(f"Wrote Python dialect to {output}")

def parse_python_imp(args):
    cats = gen_cats()
    ops = gen_ops(cats)
    with open(args.python, 'r') as r:
        t = ast.parse(r.read())
        cmd = recurse(ops, t)
    p = strata.Program(dialect_name)
    p.add(cmd)
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