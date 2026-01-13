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
from typing import Any
import types
import strata.base as strata
from .base import ArgDecl, FileMapping, Init, SourceRange, SyntaxCat, reserved

@dataclass
class OpArg:
    name : str | None
    """
    Python AST name of argument or none if this argument is not in the AST
    for this version of Python.

    Note that missing must be set if name is None.
    """
    cat : SyntaxCat
    """
    Category for this argument.
    """
    missing : strata.Arg | None
    """
    Value to use if name is not set.
    """

class Op:
    decl : strata.OpDecl
    args: list[OpArg]

    def __init__(self, decl : strata.OpDecl, args : list[OpArg]):
        self.decl = decl
        self.args = args

op_renamings = {
    'op': 'mk_op',
    'type': 'mk_type'
}

def gen_dialect() -> strata.Dialect:
    """
    Create the Python dialect.

    Note that this requires Python 3.13 and later due to use of AST `_field_types`
    """
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
    PythonAST.add_op("some_expr", ArgDecl("x", PythonAST.expr()), PythonAST.opt_expr())
    PythonAST.add_op("missing_expr", PythonAST.opt_expr())

    def as_atom_type(tp) -> SyntaxCat:
        if tp is int:
            return PythonAST.int()
        elif tp is str:
            return Init.Str()
        elif tp is object:
            return PythonAST.constant()
        else:
            return Python_catmap[tp]

    def translate_op(name : str, op : type, category : SyntaxCat):

        used_names = set(reserved)

        op_argDecls : list[ArgDecl] = []

        # We get the field type map.
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
            op_argDecls.append(ArgDecl(ddm_name, cat))
        PythonAST.add_op(name, *op_argDecls, category)

    # Add all operators to Python dialect and op_map.
    for (cat, cat_ref) in Python_catmap.items():
        if cat.__subclasses__():
            for op in cat.__subclasses__():
                translate_op(op.__name__, op, cat_ref)
        else:
            translate_op(f"mk_{cat.__name__}", cat, cat_ref)

    return PythonAST

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

# Note these are all deprecated.
ignored_cats : set[type] = set([
    ast.AugLoad, ast.AugStore, ast.ExtSlice, ast.Index, ast.Param, ast.Suite
])

def create_opmap(PythonAST : strata.Dialect) -> dict[type, Op]:
    def populate_op(name : str, op : type) -> Op:
        decl = getattr(PythonAST, name)
        op_decl : strata.OpDecl = getattr(PythonAST, name)
        assert isinstance(decl, strata.OpDecl)

        op_args : list[OpArg]= []
        for f in op._fields:
            assert isinstance(f, str)
            ddm_name : str = op_renamings.get(f, f)
            idx = op_decl.arg_name_map[ddm_name]
            cat = op_decl.args[idx].kind
            assert isinstance(cat, SyntaxCat)
            op_args.append(OpArg(f, cat, missing=None))

        for idx in range(len(op._fields), len(decl.args)):
            arg = decl.args[idx]
            cat = arg.kind
            assert isinstance(cat, SyntaxCat)
            missing = strata.OptionArg(None)
            op_args.append(OpArg(None, cat, missing=missing))

        return Op(decl, op_args)

    # Add all operators to Python dialect and op_map.
    Python_opmap = {}
    for cat in ast.AST.__subclasses__():
        if cat.__subclasses__():
            for op in cat.__subclasses__():
                if op in ignored_cats:
                    continue

                Python_opmap[op] = populate_op(op.__name__, op)
        else:
            Python_opmap[cat] = populate_op(f"mk_{cat.__name__}", cat)
    return Python_opmap

import sys

new_args : list[tuple[type, str]]
if sys.version_info >= (3, 13):
    new_args = []
else:
    assert sys.version_info >= (3, 12)
    new_args = [
        (ast.TypeVar, "default_value"),
        (ast.ParamSpec, "default_value"),
        (ast.TypeVarTuple, "default_value"),
    ]

def check_op(d : strata.Dialect, name, op : type):
    opd = getattr(d, name)
    assert isinstance(opd, strata.OpDecl)
    fields = op._fields
    assert len(fields) <= len(opd.args), f'Field Length mismatch {len(fields)} {len(opd.args)}'
    for (i, f) in enumerate(fields):
        assert type(f) is str
        ddm_name : str = op_renamings.get(f, f)
        arg = opd.args[i]
        assert arg.name == ddm_name, f'Name mismatch {arg.name} {ddm_name}'
    l = len(fields)
    while l < len(opd.args):
        arg = opd.args[l]
        assert (op, arg.name) in new_args, f"Extra field name {arg.name} in {opd.name}"
        k = arg.kind
        assert isinstance(k, SyntaxCat)
        assert k.name == Init.Option.ident, f"Bad type for {op} {arg.name}"
        l += 1

def check_ast(d : strata.Dialect):
    for cat in ast.AST.__subclasses__():
        if cat.__subclasses__():
            for op in cat.__subclasses__():
                if op in ignored_cats:
                    continue
                check_op(d, op.__name__, op)
        else:
            check_op(d, f"mk_{cat.__name__}", cat)


class Parser:
    PythonAST : Any
    opmap : dict[type, Op]

    def __init__(self, PythonAST):
        self.PythonAST = PythonAST
        self.opmap = create_opmap(PythonAST)
        check_ast(PythonAST)

    def ast_to_arg(self, mapping : FileMapping, v : object, cat : SyntaxCat) -> strata.Arg:
        match cat.name:
            case Init.Option.ident:
                if v is None:
                    return strata.OptionArg(None)
                else:
                    return strata.OptionArg(self.ast_to_arg(mapping, v, cat.args[0]))
            case self.PythonAST.int.ident:
                assert isinstance(v, int)
                if v >= 0:
                    return self.PythonAST.IntPos(strata.NumLit(v))
                else:
                    return self.PythonAST.IntNeg(strata.NumLit(-v))
            case Init.Str.ident:
                assert isinstance(v, str)
                return strata.StrLit(v)
            case self.PythonAST.constant.ident:
                if isinstance(v, bool):
                    if v:
                        return self.PythonAST.ConTrue()
                    else:
                        return self.PythonAST.ConFalse()
                elif isinstance(v, int):
                    if v >= 0:
                        return self.PythonAST.ConPos(strata.NumLit(v))
                    else:
                        return self.PythonAST.ConNeg(strata.NumLit(-v))
                elif isinstance(v, str):
                    return self.PythonAST.ConString(strata.StrLit(v))
                elif v is None:
                    return self.PythonAST.ConNone()
                elif isinstance(v, float):
                    return self.PythonAST.ConFloat(strata.StrLit(str(v)))
                elif isinstance(v, types.EllipsisType):
                    return self.PythonAST.ConEllipsis()
                elif isinstance(v, bytes):
                    return self.PythonAST.ConBytes(strata.BytesLit(v))
                elif isinstance(v, complex):
                    r = strata.StrLit(str(v.real))
                    i = strata.StrLit(str(v.imag))
                    return self.PythonAST.ConComplex(r, i)
                else:
                    raise ValueError(f"Unsupported constant type {type(v)}")
            case self.PythonAST.opt_expr.ident:
                if v is None:
                    return self.PythonAST.missing_expr()
                else:
                    assert isinstance(v, ast.expr)
                    return self.PythonAST.some_expr(self.ast_to_arg(mapping, v, self.PythonAST.expr()))
            case Init.Option.ident:
                if v is None:
                    return strata.OptionArg(None)
                else:
                    return strata.OptionArg(self.ast_to_arg(mapping, v, cat.args[0]))
            case Init.Seq.ident:
                assert isinstance(v, list)
                arg_cat = cat.args[0]
                return strata.Seq(tuple(self.ast_to_arg(mapping, e, arg_cat) for e in v))
            case ident:
                assert v is not None, f'None passed to {ident}'
                return self.ast_to_op(mapping, v)

    def ast_to_op(self, mapping : FileMapping, t : object) -> strata.Operation:
        assert t is not None
        op = self.opmap[type(t)]
        src = source_range(mapping, t)
        decl = op.decl
        args = []
        for a in op.args:
            if a.name is None:
                v = a.missing
            else:
                v = getattr(t, a.name)
                v = self.ast_to_arg(mapping, v, a.cat)
            args.append(v)
        return decl(*args, ann=src)

    def parse_module(self, source : bytes, filename : str | PathLike = "<unknown>") ->  tuple[FileMapping, strata.Program]:
        mapping = FileMapping(source)
        a = ast.parse(source, mode='exec', filename=filename)
        p = strata.Program(self.PythonAST)
        p.add(self.ast_to_op(mapping, a))
        return (mapping, p)
