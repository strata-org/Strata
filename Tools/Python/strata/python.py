"""
Description: Strata Python dialect and `parse_ast` function for creating Strata programs.
"""
import ast
from dataclasses import dataclass
import typing
import types
import strata
from strata import ArgDecl, Init, SyntaxCat

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


Python : typing.Any = strata.Dialect('Python')
Python.add_import("Init")
Python.add_syncat("int")
Python.add_op("IntPos", [ArgDecl("v", Init.Num())], Python.int())
Python.add_op("IntNeg", [ArgDecl("v", Init.Num())], Python.int())
Python.add_syncat("constant")
Python.add_op("ConTrue", [], Python.constant())
Python.add_op("ConFalse", [], Python.constant())
Python.add_op("ConPos", [ArgDecl("v", Init.Num())], Python.constant())
Python.add_op("ConNeg", [ArgDecl("v", Init.Num())], Python.constant())
Python.add_op("ConString", [ArgDecl("v", Init.Str())], Python.constant())
# JHx: FIXME:  Support floating point literals
Python.add_op("ConFloat", [ArgDecl("v", Init.Str())], Python.constant())
Python.add_op("ConNone", [], Python.constant())
Python.add_op("ConEllipsis", [], Python.constant())

# Map python AST types to the syntax cat
Python_catmap : dict[type, SyntaxCat] = {}
for c in ast.AST.__subclasses__():
    name = c.__name__
    assert name not in { "int", "constant" }
    if c is ast.mod:
        decl = Init.Command
    else:
        decl = Python.add_syncat(name)
    Python_catmap[c] = decl()


op_renamings = {
    'op': 'mk_op',
    'type': 'mk_type'
}


Python_opmap : dict[type, Op] = {}

def translate_op(name : str, op : type, category : SyntaxCat):
    def as_atom_type(tp) -> SyntaxCat:
        if tp is int:
            return Python.int()
        elif tp is str:
            return Init.Str()
        elif tp is object:
            return Python.constant()
        else:
            return Python_catmap[tp]

    used_names = { "category", "op", "type", "fn", "metadata" }
    op_args : list[OpArg]= []
    op_argDecls : list[ArgDecl] = []

    try:
        field_types : dict[str, object] = op._field_types
        for (f, tp) in field_types.items():
            ddm_name : str = op_renamings.get(f, f)
            assert ddm_name not in used_names, f"{f} in {used_names}"
            used_names.add(ddm_name)
            if op is ast.arguments and f == 'kw_defaults':
                assert isinstance(tp, types.GenericAlias)
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                cat = Init.Seq(Init.Option(as_atom_type(args[0])))
            elif op is ast.Dict and f == 'keys':
                assert isinstance(tp, types.GenericAlias)
                origin = typing.get_origin(tp)
                assert origin is list
                args = typing.get_args(tp)
                assert len(args) == 1
                cat = Init.Seq(Init.Option(as_atom_type(args[0])))
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
    decl = Python.add_op(name, op_argDecls, category)
    Python_opmap[op] = Op(decl, op_args)

# Add all operators to Python dialect and op_map.
for (cat, cat_ref) in Python_catmap.items():
    if cat.__subclasses__():
        for op in cat.__subclasses__():
            translate_op(op.__name__, op, cat_ref)
    else:
        translate_op(f"mk_{cat.__name__}", cat, cat_ref)

def ast_to_arg(t : object, cat : SyntaxCat) -> strata.Arg:
    match cat.ident:
        case Init.Option.ident:
            if t is None:
                return None
            else:
                return strata.SomeArg(ast_to_arg(t, cat.args[0]))
        case Python.int.ident:
            assert isinstance(t, int)
            if t >= 0:
                return Python.IntPos(strata.NumLit(t))
            else:
                return Python.IntNeg(strata.NumLit(-t))
        case Init.Str.ident:
            assert isinstance(t, str)
            return strata.StrLit(t)
        case Python.constant.ident:
            if isinstance(t, bool):
                if t:
                    return Python.ConTrue()
                else:
                    return Python.ConFalse()
            elif isinstance(t, int):
                if t >= 0:
                    return Python.ConPos(strata.NumLit(t))
                else:
                    return Python.ConNeg(strata.NumLit(-t))
            elif isinstance(t, str):
                return Python.ConString(strata.StrLit(t))
            elif t is None:
                return Python.ConNone()
            elif isinstance(t, float):
                return Python.ConFloat(strata.StrLit(str(t)))
            elif isinstance(t, types.EllipsisType):
                return Python.ConEllipsis()
            elif isinstance(t, bytes):
                return Python.ConEllipsis() # FIXME
            else:
                raise ValueError(f"Unsupported constant type {type(t)}")
        case ident:
            assert t is not None, f'None passed to {ident}'
            return ast_to_op(t)

def ast_to_op(t : object) -> strata.Operation:
    assert t is not None
    op = Python_opmap[type(t)]
    decl = op.decl
    args = []
    for a in op.args:
        v = getattr(t, a.name)
        cat = a.cat
        match cat.ident:
            case Init.Option.ident:
                if v is None:
                    r = None
                else:
                    r = strata.SomeArg(ast_to_arg(v, cat.args[0]))
            case Init.Seq.ident:
                assert isinstance(v, list)
                arg_cat = cat.args[0]
                if arg_cat.ident != Init.Option.ident:
                    assert None not in v, f'{type(t).__name__}.{a.name}: : {v} passed to ast_to_arg {str(arg_cat)}'
                r = strata.Seq([ ast_to_arg(e, arg_cat) for e in v])
            case _:
                r = ast_to_arg(v, cat)
        args.append(r)
    return decl(*args)

def parse_ast(ast : object) -> strata.Program:
    p = strata.Program(Python.name)
    p.add(ast_to_op(ast))
    return p
