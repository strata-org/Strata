# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""
Strata Python dialect and `parse_ast` function for creating Strata programs.
"""
import ast
from dataclasses import dataclass
from os import PathLike
import typing
import types
import strata
from .base import ArgDecl, FileMapping, Init, SourceRange, SyntaxCat, reserved

@dataclass
class OpArg:
    name : str
    cat : SyntaxCat

class Op:
    decl : strata.OpDecl
    args: list[OpArg]

    def __init__(self, decl : strata.OpDecl, args : list[OpArg]):
        self.decl = decl
        self.args = args

PythonAST : typing.Any = strata.Dialect('Python')
PythonAST.add_import("Init")
PythonAST.add_syncat("int")
PythonAST.add_op("IntPos", ArgDecl("v", Init.Num()), PythonAST.int())
PythonAST.add_op("IntNeg", ArgDecl("v", Init.Num()), PythonAST.int())
PythonAST.add_syncat("constant")
PythonAST.add_op("ConTrue", PythonAST.constant())
PythonAST.add_op("ConFalse", PythonAST.constant())
PythonAST.add_op("ConPos", ArgDecl("v", Init.Num()), PythonAST.constant())
PythonAST.add_op("ConNeg", ArgDecl("v", Init.Num()), PythonAST.constant())
PythonAST.add_op("ConString", ArgDecl("v", Init.Str()), PythonAST.constant())
# JHx: FIXME:  Support floating point literals
PythonAST.add_op("ConFloat", ArgDecl("v", Init.Str()), PythonAST.constant())
PythonAST.add_op("ConComplex", ArgDecl("real", Init.Str()), ArgDecl("imag", Init.Str()), PythonAST.constant())
PythonAST.add_op("ConNone", PythonAST.constant())
PythonAST.add_op("ConEllipsis", PythonAST.constant())
PythonAST.add_op("ConBytes", ArgDecl("v", Init.ByteArray()), PythonAST.constant())

# Map python AST types to the syntax cat
Python_catmap : dict[type, SyntaxCat] = {}
for c in ast.AST.__subclasses__():
    name = c.__name__
    assert name not in { "int", "constant" }
    if c is ast.mod:
        decl = Init.Command
    else:
        decl = PythonAST.add_syncat(name)
    Python_catmap[c] = decl()

PythonAST.add_syncat("opt_expr")
some_expr = PythonAST.add_op("some_expr", ArgDecl("x", PythonAST.expr()), PythonAST.opt_expr())
missing_expr = PythonAST.add_op("missing_expr", PythonAST.opt_expr())

op_renamings = {
    'op': 'mk_op',
    'type': 'mk_type'
}

Python_opmap : dict[type, Op] = {}

def translate_op(name : str, op : type, category : SyntaxCat):
    def as_atom_type(tp) -> SyntaxCat:
        if tp is int:
            return PythonAST.int()
        elif tp is str:
            return Init.Str()
        elif tp is object:
            return PythonAST.constant()
        else:
            return Python_catmap[tp]

    used_names = set(reserved)

    op_args : list[OpArg]= []
    op_argDecls : list[ArgDecl] = []

    try:
        field_types : dict[str, object] = op._field_types
        for (f, tp) in field_types.items():
            ddm_name : str = op_renamings.get(f, f)
            assert ddm_name not in used_names, f'{ddm_name} is used.'
            used_names.add(ddm_name)
            if op is ast.arguments and f == 'kw_defaults':
                assert isinstance(tp, types.GenericAlias)
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                assert args[0] is ast.expr
                cat = Init.Seq(PythonAST.opt_expr())
            elif op is ast.Dict and f == 'keys':
                assert isinstance(tp, types.GenericAlias)
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                assert args[0] is ast.expr
                cat = Init.Seq(PythonAST.opt_expr())
            elif isinstance(tp, types.UnionType):
                args = typing.get_args(tp)
                assert len(args) == 2
                opt_cat = as_atom_type(args[0])
                assert args[1] is types.NoneType
                cat = Init.Option(opt_cat)
            elif isinstance(tp, types.GenericAlias):
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                cat = Init.Seq(as_atom_type(args[0]))
            else:
                cat = as_atom_type(tp)

            op_args.append(OpArg(f, cat))
            op_argDecls.append(ArgDecl(ddm_name, cat))
    except AttributeError:
        op_args = []
        op_argDecls = []
    decl = PythonAST.add_op(name, *op_argDecls, category)
    Python_opmap[op] = Op(decl, op_args)

# Add all operators to Python dialect and op_map.
for (cat, cat_ref) in Python_catmap.items():
    if cat.__subclasses__():
        for op in cat.__subclasses__():
            translate_op(op.__name__, op, cat_ref)
    else:
        translate_op(f"mk_{cat.__name__}", cat, cat_ref)

def source_range(mapping : FileMapping, t : object) -> SourceRange|None:
    lineno = getattr(t, 'lineno', None)
    col_offset = getattr(t, 'col_offset', None)
    end_lineno = getattr(t, 'end_lineno', None)
    end_col_offset = getattr(t, 'end_col_offset', None)
    if lineno is None:
        assert col_offset is None
        assert end_lineno is None
        assert end_col_offset is None
        return None
    else:
        assert col_offset is not None
        assert end_lineno is not None
        assert end_col_offset is not None
        off = mapping.byte_offset(lineno, col_offset)
        end_off = mapping.byte_offset(end_lineno, end_col_offset)
        return SourceRange(off, end_off)

def ast_to_arg(mapping : FileMapping, v : object, cat : SyntaxCat) -> strata.Arg:
    match cat.name:
        case Init.Option.ident:
            if v is None:
                return strata.OptionArg(None)
            else:
                return strata.OptionArg(ast_to_arg(mapping, v, cat.args[0]))
        case PythonAST.int.ident:
            assert isinstance(v, int)
            if v >= 0:
                return PythonAST.IntPos(strata.NumLit(v))
            else:
                return PythonAST.IntNeg(strata.NumLit(-v))
        case Init.Str.ident:
            assert isinstance(v, str)
            return strata.StrLit(v)
        case PythonAST.constant.ident:
            if isinstance(v, bool):
                if v:
                    return PythonAST.ConTrue()
                else:
                    return PythonAST.ConFalse()
            elif isinstance(v, int):
                if v >= 0:
                    return PythonAST.ConPos(strata.NumLit(v))
                else:
                    return PythonAST.ConNeg(strata.NumLit(-v))
            elif isinstance(v, str):
                return PythonAST.ConString(strata.StrLit(v))
            elif v is None:
                return PythonAST.ConNone()
            elif isinstance(v, float):
                return PythonAST.ConFloat(strata.StrLit(str(v)))
            elif isinstance(v, types.EllipsisType):
                return PythonAST.ConEllipsis()
            elif isinstance(v, bytes):
                return PythonAST.ConBytes(strata.BytesLit(v))
            elif isinstance(v, complex):
                r = strata.StrLit(str(v.real))
                i = strata.StrLit(str(v.imag))
                return PythonAST.ConComplex(r, i)
            else:
                raise ValueError(f"Unsupported constant type {type(v)}")
        case PythonAST.opt_expr.ident:
            if v is None:
                return PythonAST.missing_expr()
            else:
                assert isinstance(v, ast.expr)
                return PythonAST.some_expr(ast_to_arg(mapping, v, PythonAST.expr()))
        case Init.Option.ident:
            if v is None:
                return strata.OptionArg(None)
            else:
                return strata.OptionArg(ast_to_arg(mapping, v, cat.args[0]))
        case Init.Seq.ident:
            assert isinstance(v, list)
            arg_cat = cat.args[0]
            return strata.Seq(tuple(ast_to_arg(mapping, e, arg_cat) for e in v))
        case ident:
            assert v is not None, f'None passed to {ident}'
            return ast_to_op(mapping, v)

def ast_to_op(mapping : FileMapping, t : object) -> strata.Operation:
    assert t is not None
    op = Python_opmap[type(t)]
    src = source_range(mapping, t)
    decl = op.decl
    args = []
    for a in op.args:
        v = getattr(t, a.name)
        args.append(ast_to_arg(mapping, v, a.cat))
    return decl(*args, ann=src)

def parse_module(source : bytes, filename : str | PathLike = "<unknown>") -> tuple[FileMapping, strata.Program]:
    """
    Parse the Python source into a Strata program.
    The Strata program will contain a single top-level
    """
    m = FileMapping(source)
    a = ast.parse(source, mode='exec', filename=filename)
    assert isinstance(a, ast.Module)

    p = strata.Program(PythonAST)
    p.add(ast_to_op(m, a))
    return (m, p)