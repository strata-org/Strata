# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""
Description: Core Strata AST datatypes.
"""
from bisect import bisect_right
from dataclasses import dataclass
from decimal import Decimal
import sys
import typing
from typing import Any, Callable, Iterable, TypeVar, Generic, Union

import amazon.ion.simpleion as ion

def ion_symbol(s : str):
    return ion.IonPySymbol(s, None, None)

def ion_sexp(*args):
    h : typing.Any = ion.IonPyList(a for a in args)
    h.ion_type = ion.IonType.SEXP
    return h

@dataclass
class SourceRange:
    offset : int
    end_offset : int

    def to_ion(self):
        return ion_sexp(self.offset, self.end_offset)

class SourcePos:
    line : int
    col : int

    def __init__(self, line : int, col : int):
        self.line = line
        self.col = col

    def __str__(self) -> str:
        return f'{self.line}:{self.col}'

class FileMapping:
    line_offsets : list[int]

    def __init__(self, bytes : bytes):
        self.line_offsets = [0]
        for i, b in enumerate(bytes):
            if b == ord('\n'):
                self.line_offsets.append(i + 1)

    def byte_offset(self, line : int, col : int) -> int:
        assert line > 0
        assert line - 1 < len(self.line_offsets)
        return self.line_offsets[line - 1] + col

    def position(self, index : int) -> SourcePos:
        lineno = bisect_right(self.line_offsets, index)

        off = self.line_offsets[lineno - 1]
        assert index >= off
        col_offset = index - off
        return SourcePos(lineno, col_offset + 1)

def ann_to_ion(ann : Any):
    if ann is None:
        return None
    assert isinstance(ann, SourceRange)
    return ann.to_ion()

@dataclass
class QualifiedIdent:
    dialect: str
    name: str

    def __init__(self, *args):
        if len(args) == 1:
            assert isinstance(args[0], str)
            (dialect, sep, name) = args[0].partition('.')
            if sep != '.':
                raise ValueError(f"Missing separator in {args[0]}")
            assert '.' not in name
            self.name = name
            self.dialect = dialect
        else:
            assert len(args) == 2
            self.dialect = args[0]
            self.name = args[1]
            assert '.' not in self.dialect
            assert '.' not in self.name

    def __hash__(self) -> int:
        return hash((self.dialect, self.name))

    def __str__(self) -> str:
        return f"{self.dialect}.{self.name}"

    def to_ion(self):
        return ion_symbol(f"{self.dialect}.{self.name}")

@dataclass
class SyntaxCat:
    ann : Any
    name : QualifiedIdent
    args: tuple['SyntaxCat', ...]

    def __init__(self, name: QualifiedIdent, args: tuple['SyntaxCat', ...] | None = None, *, ann = None):
        assert isinstance(name, QualifiedIdent)
        assert args is None or isinstance(args, tuple) and all(isinstance(a, SyntaxCat) for a in args)
        self.ann = ann
        self.name = name
        self.args = () if args is None else args

    def strPrec(self, prec: int) -> str:
        args = ''.join(' ' + a.strPrec(10) for a in self.args)
        s = f'{str(self.name)}{args}'
        return f'({s})' if prec > 0 else s

    def __str__(self) -> str:
        return self.strPrec(0)

    def to_ion(self):
        return ion_sexp(ann_to_ion(self.ann), self.name.to_ion(), *(a.to_ion() for a in self.args))

class TypeExpr:
    ann : Any

    def __init__(self, *, ann=None) -> None:
        self.ann = ann

    def to_ion(self):
        raise NotImplementedError

class TypeIdent(TypeExpr):
    ident: QualifiedIdent
    args: list[TypeExpr]

    def __init__(self, ident: QualifiedIdent, args: list[TypeExpr] | None = None, *, ann = None):
        super().__init__(ann=ann)
        self.ident = ident
        self.args = [] if args is None else args

    identSym = ion_symbol("ident")

    def to_ion(self):
        return ion_sexp(
            self.identSym, ann_to_ion(self.ann), self.ident.to_ion(),
            *(a.to_ion() for a in self.args)
        )

class TypeBVar(TypeExpr):
    index: int

    def __init__(self, index : int, *, ann=None) -> None:
        super().__init__(ann=ann)
        self.index = index

    bvarSym = ion_symbol("bvar")

    def to_ion(self):
        return ion_sexp(self.bvarSym, ann_to_ion(self.ann), self.index)

class TypeFVar(TypeExpr):
    index: int
    args: list[TypeExpr]

    def __init__(self, index: int, args: list[TypeExpr] | None = None, *, ann = None):
        super().__init__(ann=ann)
        self.index = index
        self.args = [] if args is None else args

    fvarSym = ion_symbol("fvar")

    def to_ion(self):
        return ion_sexp(self.fvarSym, ann_to_ion(self.ann), self.index, *(a.to_ion() for a in self.args))

class TypeArrow(TypeExpr):
    arg: TypeExpr
    res: TypeExpr

    def __init__(self, arg: TypeExpr, res: TypeExpr, *, ann = None):
        super().__init__(ann=ann)
        self.arg = arg
        self.res = res

    arrowSym = ion_symbol("arrow")

    def to_ion(self):
        return ion_sexp(self.arrowSym, ann_to_ion(self.ann), self.arg, self.res)

class TypeFunMacro(TypeExpr):
    bindingsIndex: int
    res: TypeExpr

    def __init__(self, bindingsIndex: int, res: TypeExpr, *, ann = None):
        super().__init__(ann=ann)
        self.bindingsIndex = bindingsIndex
        self.res = res

    funMacroSym = ion_symbol("funMacro")

    def to_ion(self):
        return ion_sexp(
            self.funMacroSym,
            ann_to_ion(self.ann),
            self.bindingsIndex,
            self.res)

class Expr:
    ann : Any

    def __init__(self, *, ann=None):
        self.ann = ann

    def to_ion(self):
        raise NotImplementedError

class ExprBVar(Expr):
    idx : int

    def __init__(self, idx : int, *, ann=None):
        super().__init__(ann=ann)
        self.idx = idx

    sym = ion_symbol("bvar")

    def to_ion(self):
        return ion_sexp(self.sym, ann_to_ion(self.ann), self.idx)

class ExprFVar(Expr):
    level : int

    def __init__(self, level : int, *, ann=None):
        super().__init__(ann=ann)
        self.level = level

    fvarSym = ion_symbol("fvar")
    def to_ion(self):
        return ion_sexp(self.fvarSym, ann_to_ion(self.ann), self.level)

class ExprFn(Expr):
    ident : QualifiedIdent

    def __init__(self, ident : QualifiedIdent, *, ann=None):
        super().__init__(ann=ann)
        self.ident = ident

    def to_ion(self):
        return ion_sexp(ion_symbol("fn"), ann_to_ion(self.ann), self.ident.to_ion())

class OperationArgs:
    _decls : tuple['ArgDecl', ...]
    _arg_indices : dict[str, int]
    _args : tuple['Arg', ...]

    def __init__(self, decls : tuple['ArgDecl', ...], arg_indices : dict[str, int], *args : 'Arg'):
        assert len(args) == len(decls)
        self._decls = decls
        self._arg_indices = arg_indices
        self._args = args

    def __getitem__(self, field : str|int) -> 'Arg':
        if type(field) is int:
            return self._args[field]
        if type(field) is str:
            return self._args[self._arg_indices[field]]
        raise ValueError(f'Expected int or str, got {type(field)}')

    def items(self) -> Iterable[tuple[str, 'Arg']]:
        return ((d.name, a) for (d, a) in zip(self._decls, self._args))

    def __len__(self) -> int:
        return len(self._args)

class Operation:
    ann : Any
    decl : 'OpDecl'
    args : OperationArgs

    def __init__(self, decl : 'OpDecl', args : list['Arg']|None = None, *, ann = None):
        self.ann = ann
        self.decl = decl
        if args is None:
            assert len(decl.args) == 0
            self.args = OperationArgs(decl.args, decl.arg_name_map)
        else:
            self.args = OperationArgs(decl.args, decl.arg_name_map, *args)

    def __str__(self) -> str:
        t = ', '.join(f'{n}={str(v)}' for (n,v) in self.args.items())
        return f'{str(self.decl.ident)}({t})'

    def to_ion(self) -> object:
        return ion_sexp(
            self.decl.ident.to_ion(),
            ann_to_ion(self.ann),
            *(arg_to_ion(a) for a in self.args)
        )

@dataclass
class Ident:
    ann : Any
    value: str

    def __init__(self, value: str, *, ann = None):
        self.ann = ann
        self.value = value

@dataclass
class NumLit:
    ann : Any
    value: int

    def __init__(self, value: int, *, ann = None):
        # This is to avoid bool values sneaking in
        assert type(value) is int
        assert value >= 0
        self.ann = ann
        self.value = value

@dataclass
class DecimalLit:
    value: Decimal
    ann : Any

    def __init__(self, value: Decimal, *, ann = None):
        assert type(value) is int
        assert value >= 0
        self.value = value
        self.ann = ann

@dataclass
class BytesLit:
    ann : Any
    value: bytes

    def __init__(self, value: bytes, *, ann = None):
        self.value = value
        self.ann = ann

    def __str__(self):
        return f'BytesLit({repr(self.value)})'

@dataclass
class StrLit:
    ann : Any
    value: str

    def __init__(self, value: str, *, ann = None):
        self.ann = ann
        self.value = value

    def __str__(self):
        return f'StrLit({repr(self.value)})'

T = TypeVar('T', bound='Arg')

@dataclass
class OptionArg(Generic[T]):
    value: Union[T, None]
    ann : Any

    def __init__(self, value: Union[T, None], *, ann = None):
        self.value = value
        self.ann = ann

    def __bool__(self) -> bool:
        return self.value is not None

    def __str__(self):
        if self.value is None:
            return 'None'
        else:
            return f'Some({self.value})'

@dataclass
class Seq(Generic[T]):
    values: tuple[T, ...]
    ann : Any

    def __init__(self, values: tuple[T, ...], *, ann = None):
        for v in values:
            assert not isinstance(v, OpDecl), f'Unexpected value {type(v)}'
        self.values = values
        self.ann = ann

    def __getitem__(self, index: int):
        return self.values[index]

    def __len__(self):
        return len(self.values)

    def __str__(self) -> str:
        return f"Seq([{', '.join(str(a) for a in self.values)}])"

@dataclass
class CommaSepBy:
    values: list['Arg']
    ann : Any

    def __init__(self, values: list['Arg'], *, ann = None):
        self.values = values
        self.ann = ann

Arg = Union[SyntaxCat, Operation, TypeExpr, Expr, Ident, BytesLit, NumLit, DecimalLit, StrLit, OptionArg['Arg'], Seq['Arg'], CommaSepBy]

strlitSym = ion_symbol("strlit")
numSym = ion_symbol("num")

optionSym = ion_symbol("option")
_typeSym = ion_symbol("type")

def is_surrogate(c : str) -> bool:
    return '\ud800' <= c and c <= '\udfff'

def arg_to_ion(a : Arg) -> object:
    if isinstance(a, Operation):
        return ion_sexp(ion_symbol("op"), a.to_ion())
    elif isinstance(a, Expr):
        return ion_sexp(ion_symbol("expr"), a.to_ion())
    elif isinstance(a, SyntaxCat):
        return ion_sexp(ion_symbol("cat"), a.to_ion())
    elif isinstance(a, TypeExpr):
        return ion_sexp(ion_symbol("type"), a.to_ion())
    elif isinstance(a, Ident):
        return ion_sexp(ion_symbol("ident"), ann_to_ion(a.ann), a.value)
    elif isinstance(a, NumLit):
        return ion_sexp(numSym, ann_to_ion(a.ann), a.value)
    elif isinstance(a, DecimalLit):
        return ion_sexp(ion_symbol("decimal"), ann_to_ion(a.ann), a.value)
    elif isinstance(a, StrLit):
        assert isinstance(a.value, str)
        val : object
        # N.B.  The Amazon ion library will write out null if any of the characters
        # in a string contain surrogate characters.  The Strata library escapes them
        # for now, but we should likely figure out as better solution as the Lean
        # library does not unescape them.
        if any(is_surrogate(c) for c in a.value):
            val = ""
            for c in a.value:
                if is_surrogate(c):
                    val += f"\\u{ord(c):04x}"
                else:
                    val += c
            val = ion.IonPyText(val)
        else:
            val = ion.IonPyText(a.value)
        return ion_sexp(strlitSym, ann_to_ion(a.ann), val)
    elif isinstance(a, BytesLit):
        return ion_sexp(ion_symbol("bytes"), ann_to_ion(a.ann), a.value)
    elif isinstance(a, OptionArg):
        if a.value is None:
            return ion_sexp(optionSym, ann_to_ion(a.ann))
        else:
            return ion_sexp(optionSym, ann_to_ion(a.ann), arg_to_ion(a.value))
    elif isinstance(a, Seq):
        return ion_sexp(ion_symbol("seq"), ann_to_ion(a.ann), *(arg_to_ion(e) for e in a.values))
    else:
        assert isinstance(a, CommaSepBy), f'Expected {type(a)} to be a CommaSepBy.'
        return ion_sexp(ion_symbol("commaSepList"), ann_to_ion(a.ann), *(arg_to_ion(e) for e in a.values))

def metadata_arg_to_ion(value):
    if value is None:
        return "none"
    elif value is int:
        return value
    elif value is bool:
        return value
    else:
        return value.to_ion()

@dataclass
class MetadataCat:
    index: int

    categorySym = ion_symbol("category")

    def to_ion(self):
        return ion_sexp(self.categorySym, self.index)

@dataclass
class MetadataSome:
    value: object

    someSym = ion_symbol("some")
    def to_ion(self):
        return ion_sexp(self.someSym, metadata_arg_to_ion(self.value))

@dataclass
class MetadataAttr:
    ident : QualifiedIdent
    args : list[object]

    def to_ion(self):
        return ion_sexp(self.ident.to_ion(), *(metadata_arg_to_ion(a) for a in self.args))

Metadata = list[MetadataAttr]

def metadata_to_ion(values):
    return [ v.to_ion() for v in values ]

def argdecl_kind(v: SyntaxCat|TypeExpr):
    if isinstance(v, SyntaxCat):
        return ion_sexp(ion_symbol("category"), v.to_ion())
    else:
        assert isinstance(v, TypeExpr)
        return ion_sexp(ion_symbol("type"), v.to_ion())

class SyntaxDefAtomBase:
    def to_ion(self):
        raise NotImplementedError()

@dataclass
class SyntaxDefIdent(SyntaxDefAtomBase):
    level: int
    prec: int

    def to_ion(self):
        return ion_sexp(ion_symbol("ident"), self.level, self.prec)

@dataclass
class SyntaxDefIndent(SyntaxDefAtomBase):
    indent: int
    args : tuple['SyntaxDefAtom', ...]

    def __init__(self, indent: int, args: tuple['SyntaxDefAtom', ...]):
        self.indent = indent
        self.args = args
        for a in args:
            assert not isinstance(a, SyntaxDefIndent)

    def to_ion(self):
        return ion_sexp(ion_symbol("indent"), self.indent, *(syntaxdef_atom_to_ion(a) for a in self.args))

SyntaxDefAtom = Union[SyntaxDefAtomBase, str]

def syntaxdef_atom_to_ion(atom : SyntaxDefAtom) -> object:
    if isinstance(atom, str):
        return atom
    else:
        assert isinstance(atom, SyntaxDefAtomBase)
        return atom.to_ion()

@dataclass
class SyntaxDef:
    atoms: list[SyntaxDefAtom]
    prec: int

    def to_ion(self):
        return {
            "atoms": [ syntaxdef_atom_to_ion(a) for a in self.atoms ],
            "prec": self.prec
        }

reserved = { "category", "fn", "import", "metadata", "op", "type" }

_syncat = ion.SymbolToken(u'syncat', None, None)

class SynCatDecl:
    dialect : str
    name : str
    ident : QualifiedIdent
    argNames : tuple[str, ...]

    def __init__(self, dialect : str, name : str, args: tuple[str, ...]|None = None):
        assert name not in reserved, f'{name} is a reserved word.'
        self.dialect = dialect
        self.name = name
        self.ident = QualifiedIdent(dialect, name)
        self.argNames = () if args is None else args

    def __call__(self, *args):
        assert len(args) == len(self.argNames)
        return SyntaxCat(self.ident, args)

    def to_ion(self):
        d = ion.IonPyDict()
        d.add_item("type", _syncat)
        d.add_item("name", self.name)
        if len(self.argNames) > 0:
            d.add_item("args", self.argNames)
        return d

@dataclass
class ArgDecl:
    "Argument declaration in operator or function"
    name: str
    kind : SyntaxCat|TypeExpr
    metadata: Metadata

    def __init__(self, name: str, kind : SyntaxCat|TypeExpr|SynCatDecl, metadata: Metadata|None = None):
        assert name not in reserved, f'{name} is a reserved word.'
        if isinstance(kind, SynCatDecl):
            assert len(kind.argNames) == 0, f'Missing arguments to syntax category'
            kind = kind()
        assert isinstance(kind, SyntaxCat) or isinstance(kind, TypeExpr), f'Unexpected kind {type(kind)}'

        self.name = name
        self.kind = kind
        self.metadata = [] if metadata is None else metadata

    def to_ion(self):
        flds = {
            "name": self.name,
            "type": argdecl_kind(self.kind),
        }
        if len(self.metadata) > 0:
            flds["metadata"] = metadata_to_ion(self.metadata)
        return flds

maxPrec = 1024

class SyntaxArg:
    """Argument in syntax expression."""
    name : str
    prec : int

    def __init__(self, name : str):
        (f, s, e) = name.partition(':')
        prec = maxPrec
        if len(s) == 0:
            prec = 0
        else:
            prec = int(e)
        self.name = f
        self.prec = prec

    def resolve(self, args : dict[str, int]) -> SyntaxDefAtom:
        level = args.get(self.name, None)
        if level is None:
            raise ValueError(f'Unknown argument {self.name}')
        return SyntaxDefIdent(level, prec=self.prec)

class Indent:
    prec : int
    value : SyntaxArg

    def __init__(self, prec : int, value : SyntaxArg):
        assert type(prec) is int and prec > 0
        self.prec = prec
        self.value = value

def resolve_syntax(args : dict[str, int], v : str|SyntaxArg|Indent) -> list[SyntaxDefAtom]:
    if isinstance(v, str):
        return [v]
    elif isinstance(v, Indent):
        contents = v.value
        assert isinstance(contents, SyntaxArg)
        atoms = (contents.resolve(args),)
        return [SyntaxDefIndent(v.prec, atoms)]
    else:
        assert isinstance(v, SyntaxArg)
        return [v.resolve(args)]

class OpDecl:
    opSym = ion.SymbolToken(u'op', None, None)
    dialect : str
    name : str
    ident : QualifiedIdent
    arg_name_map : dict[str, int]
    args : tuple[ArgDecl, ...]
    result : SyntaxCat
    metadata : Metadata
    syntax : SyntaxDef|None

    def __init__(self,
                dialect: str,
                name: str,
                args: tuple[ArgDecl, ...],
                result : SyntaxCat,
                *,
                syntax : SyntaxDef|None = None,
                metadata : Metadata|None = None):
        assert all(isinstance(a, ArgDecl) for a in args)
        assert isinstance(result, SyntaxCat)
        assert len(result.args) == 0
        assert name not in reserved, f'{name} is a reserved word.'
        arg_dict : dict[str, int] = {}
        for i, a in enumerate(args):
            assert a.name not in arg_dict
            arg_dict[a.name] = i

        self.dialect = dialect
        self.name = name
        self.ident = QualifiedIdent(dialect, name)
        self.arg_name_map = arg_dict
        self.args = args
        self.result = result
        self.syntax = syntax
        self.metadata = [] if metadata is None else metadata

    def __call__(self, *args, ann=None):
        assert len(args) == len(self.args), f"{self.ident} given {len(args)} argument(s) when {len(self.args)} expected ({args})"
        return Operation(self, list(args), ann=ann)

    def __str__(self) -> str:
        return str(self.ident)

    def to_ion(self):
        flds = {
             "type": self.opSym,
             "name": self.name,
        }
        if len(self.args) > 0:
            flds["args"] = [ a.to_ion() for a in self.args ]
        flds["result"] = self.result.name.to_ion()
        if self.syntax is not None:
            flds["syntax"] = self.syntax.to_ion()
        if len(self.metadata) > 0:
            flds["metadata"] = metadata_to_ion(self.metadata)
        return flds

class TypeDecl:
    def __init__(self, name, argNames):
        assert name not in reserved, f'{name} is a reserved word.'
        self.name = name
        self.argNames = argNames

    def to_ion(self):
        return {
            "type": _typeSym,
            "name": self.name,
            "argNames": self.argNames
        }

_dialectSym = ion.SymbolToken(u'dialect', None, None)

_importSym = ion.SymbolToken(u'import', None, None)

def is_sexp(v) -> bool:
    tv = type(v)
    return tv is ion.IonPyList

def get_field_symbol(event : ion.IonEvent) -> str:
    field_name = event.field_name
    assert isinstance(field_name, ion.SymbolToken), f"Expected field name"
    assert type(field_name.text) is str
    return field_name.text

def has_field_symbol(event : ion.IonEvent, expected : str) -> bool:
    field_name = event.field_name
    if field_name is None:
        return False
    assert isinstance(field_name, ion.SymbolToken), f"Expected field name"
    assert type(field_name.text) is str
    return field_name.text == expected

def read_event(reader) -> ion.IonEvent:
    event = reader.send(ion.NEXT_EVENT)
    assert isinstance(event, ion.IonEvent)
    return event

def is_container_start(event : ion.IonEvent, expected : ion.IonType):
    return event.event_type == ion.IonEventType.CONTAINER_START and event.ion_type == expected

def is_container_end(event : ion.IonEvent, expected : ion.IonType):
    return event.event_type == ion.IonEventType.CONTAINER_END and event.ion_type == expected

def is_list_start(event : ion.IonEvent):
    return is_container_start(event, ion.IonType.LIST)

def is_list_end(event : ion.IonEvent):
    return is_container_end(event, ion.IonType.LIST) and event.field_name is None

def is_sexp_start(event : ion.IonEvent):
    return is_container_start(event, ion.IonType.SEXP)

def is_sexp_end(event : ion.IonEvent):
    return is_container_end(event, ion.IonType.SEXP) and event.field_name is None

def is_struct_start(event : ion.IonEvent):
    return is_container_start(event, ion.IonType.STRUCT)

def is_struct_end(event : ion.IonEvent):
    return is_container_end(event, ion.IonType.STRUCT) and event.field_name is None

def read_list_start(reader):
    event = read_event(reader)
    assert is_list_start(event), f"Expected {repr(event)} list start"
    assert event.field_name is None, "Unexpected field name"

def read_field_list_start(reader) -> str:
    event = read_event(reader)
    assert is_list_start(event), f"Expected list start instead of {repr(event)}"
    return get_field_symbol(event)

def read_sexp_start(reader):
    event = read_event(reader)
    assert is_sexp_start(event), f"Expected sexpr start {repr(event)}"
    assert event.field_name is None, "Unexpected field name"

def read_field_sexp_start(reader) -> str:
    event = read_event(reader)
    assert is_sexp_start(event), f"Expected list start instead of {repr(event)}"
    return get_field_symbol(event)

def read_sexp_end(reader):
    event = read_event(reader)
    assert is_sexp_end(event), f"Expected sexp end {repr(event)}"
    assert event.field_name is None, "Unexpected field name"

def read_struct_start(reader):
    event = read_event(reader)
    assert is_struct_start(event), f"Expected struct start {repr(event)}"
    assert event.field_name is None, "Unexpected field name"

def read_struct_end(reader):
    event = read_event(reader)
    assert is_struct_end(event), f"Expected struct end {repr(event)}"
    assert event.field_name is None, "Unexpected field name"

def is_scalar(event : ion.IonEvent, expected : ion.IonType) -> bool:
    return event.event_type == ion.IonEventType.SCALAR and event.ion_type == expected

def is_string(event : ion.IonEvent) -> bool:
    return is_scalar(event, IonType.STRING)

def is_symbol(event : ion.IonEvent) -> bool:
    return is_scalar(event, IonType.SYMBOL)

def read_scalar(reader, expected : ion.IonType) -> ion.IonEvent:
    event = read_event(reader)
    assert is_scalar(event, expected), f"Expected scalar {repr(expected)} instead of {repr(event)}"
    return event

from amazon.ion.simpleion import IonType

def read_field_symbol(reader) -> tuple[str, ion.IonPySymbol]:
    event = read_scalar(reader, IonType.SYMBOL)
    return (get_field_symbol(event), ion.IonPySymbol.from_event(event))

def read_symbol(reader) -> ion.IonPySymbol:
    event = read_scalar(reader, IonType.SYMBOL)
    assert event.field_name is None, "Unexpected field name"
    return ion.IonPySymbol.from_event(event)

def read_field_string(reader) -> tuple[str, str]:
    event = read_scalar(reader, IonType.STRING)
    scalar = ion.IonPyText.from_event(event)
    assert isinstance(scalar, str)
    return (get_field_symbol(event), scalar)

def read_string(reader) -> str:
    event = read_scalar(reader, IonType.STRING)
    assert event.field_name is None, "Unexpected field name"
    scalar = ion.IonPyText.from_event(event)
    assert isinstance(scalar, str)
    return scalar

X = TypeVar('X')

def read_list(reader : object, f : Callable[[object, ion.IonEvent], X] ) -> tuple[X, ...]:
    res = []
    while True:
        event = read_event(reader)
        if is_list_end(event):
            return tuple(res)
        v = f(reader, event)
        res.append(v)

def read_sexpr(reader : object, f : Callable[[object, ion.IonEvent], X] ) -> tuple[X, ...]:
    res = []
    while True:
        event = read_event(reader)
        if is_sexp_end(event):
            return tuple(res)
        v = f(reader, event)
        res.append(v)

def print_unknown(event : ion.IonEvent):
    pre : str
    if event.field_name is None:
        pre = ""
    else:
        pre = f"{get_field_symbol(event)}: "
    match event.event_type:
        case ion.IonEventType.SCALAR:
            match event.ion_type:
                case ion.IonType.SYMBOL:
                    scalar = ion.IonPySymbol.from_event(event)
                    print(f"{pre}Scalar symbol {repr(scalar)}")
                case _:
                    print(f"{pre}Scalar event {repr(event.ion_type)}")
        case ion.IonEventType.CONTAINER_START:
            print(f"{pre}Container start {repr(event.ion_type)}")
        case ion.IonEventType.CONTAINER_END:
            print(f"{pre}Container stop {repr(event.ion_type)}")
        case _:
            print(f"{pre}Unknown event {repr(event.event_type)}")

def read_unknown(reader):
    event = read_event(reader)
    print_unknown(event)
    sys.exit("Done")

def read_syncatdecl(reader, dialect : 'Dialect'):
    (field, name) = read_field_string(reader)
    assert field == "name", f"Unexpected field {field}"

    event = read_event(reader)
    args : tuple[str, ...]
    if has_field_symbol(event, "args"):
        assert is_list_start(event), f"Expected {repr(event)} list start"

        def get_string_event(reader, event):
            assert is_string(event)
            return ion.IonPyText.from_event(event)

        args = read_list(reader, get_string_event)
        event = read_event(reader)
    else:
        args = ()

    assert is_struct_end(event), f"Expected struct_end"
    dialect.add_syncat(name, args)

def read_ann(event : ion.IonEvent) -> None:
    assert is_scalar(event, IonType.NULL), f"Expected null {repr(event)}"

def as_qualified_ident(event : ion.IonEvent) -> QualifiedIdent:
    assert is_symbol(event), f"Expected symbol instead of {repr(event)}"
    sym = ion.IonPySymbol.from_event(event)
    assert isinstance(sym.text, str)
    tokens = sym.text.split('.')
    assert len(tokens) == 2
    return QualifiedIdent(tokens[0], tokens[1])

def read_syntaxcat(reader, event) -> SyntaxCat:
    assert is_sexp_start(event), f"Expected sexpr start {repr(event)}"
    assert event.field_name is None, "Unexpected field name"

    event = read_event(reader)
    ann = read_ann(event)
    event = read_event(reader)
    assert event.field_name is None, "Unexpected field name"
    name = as_qualified_ident(event)
    args = read_sexpr(reader, read_syntaxcat)
    return SyntaxCat(name, args, ann=ann)


def read_argdecl_kind(reader) -> SyntaxCat|TypeExpr:
    kind = read_symbol(reader)
    match kind.text:
        case "category":
            event = read_event(reader)
            r = read_syntaxcat(reader, event)
            read_sexp_end(reader)
            return r
        case "type":
            raise Exception(f"Unknown kind {kind.text}")
        case _:
            raise Exception(f"Unknown kind {kind.text}")

def read_arg_decl(reader, event) -> ArgDecl:
    assert is_struct_start(event), f"Expected {repr(event)} struct start"
    (field, name) = read_field_string(reader)
    assert field == "name", f"Unexpected field {field}"
    field = read_field_sexp_start(reader)
    assert field == "type", f"Unexpected field {field}"
    type = read_argdecl_kind(reader)
    read_struct_end(reader)
    return ArgDecl(name, type)

class Dialect:
    """
    A Strata dialect
    """

    name : str
    imports : list[str]
    decls : list[SynCatDecl | OpDecl]

    def __init__(self, name: str):
        self.name = name
        self.imports = []
        self.decls = []

    def add_import(self, name: str):
        self.imports.append(name)

    def add_syncat(self, name : str, args: tuple[str, ...]|None = None) -> SynCatDecl:
        decl = SynCatDecl(self.name, name, args)
        self.add(decl)
        return decl

    def add_op(self, name : str, *args: ArgDecl|SyntaxCat,
            syntax : str|SyntaxArg|Indent|None|list[SyntaxDefAtom] = None,
            prec : int|None = None,
            metadata : Metadata|None = None) -> OpDecl:
        assert name not in reserved, f'{name} is a reserved word.'
        assert len(args) > 0
        result = args[-1]
        assert isinstance(result, SyntaxCat), f'{name} result must be a SyntaxCat'
        assert len(result.args) == 0
        args = args[:-1]
        assert all((isinstance(a, ArgDecl) for a in args)), f'{name} args must be a ArgDecl'
        rargs : tuple[ArgDecl, ...] = args # type: ignore

        arg_dict = {}
        for i, a in enumerate(rargs):
            assert a.name not in arg_dict
            arg_dict[a.name] = i

        if syntax is None:
            assert prec is None
            syntaxd = None
        else:
            if prec is None:
                prec = maxPrec
            if isinstance(syntax, list):
                syntax_atoms = syntax
            else:
                syntax_atoms = resolve_syntax(arg_dict, syntax)
            syntaxd = SyntaxDef(syntax_atoms, prec)
        decl = OpDecl(self.name, name, rargs, result, syntax=syntaxd, metadata=metadata)
        self.add(decl)
        return decl

    def add(self, decl : SynCatDecl | OpDecl):
        assert decl is not None
        if isinstance(decl, SynCatDecl):
            assert (decl.dialect == self.name)
            if decl.name in self.__dict__:
                raise Exception(f"{decl.name} already added: {self.__dict__[decl.name]}")
            self.__dict__[decl.name] = decl
        elif isinstance(decl, OpDecl):
            assert (decl.dialect == self.name)
            assert (decl.name not in self.__dict__), f'{decl.name} already added.'
            self.__dict__[decl.name] = decl

        self.decls.append(decl)

    def to_ion(self):
        r : list[object] = [ion_sexp(_dialectSym, self.name)]
        for i in self.imports:
            d = ion.IonPyDict()
            d.add_item("type", _importSym)
            d.add_item("name", i)
            r.append(d)
        for d in self.decls:
            r.append(d.to_ion())
        return r

    @staticmethod
    def from_ion(fp) -> 'Dialect':
#        contents = ion.load(f)

        maybe_ivm = fp.read(4)
        fp.seek(0)
        if maybe_ivm == ion._IVM:
            raw_reader = ion.binary_reader()
        else:
            raw_reader = ion.text_reader()
        from amazon.ion.symbols import SymbolTableCatalog
        catalog = SymbolTableCatalog()
        mr = ion.managed_reader(raw_reader, catalog)
        reader = ion.blocking_reader(mr, fp)


        read_list_start(reader)

        # Read dialect name
        read_sexp_start(reader)
        assert read_symbol(reader).text == "dialect"
        dname = read_string(reader)
        read_sexp_end(reader)

        dialect = Dialect(dname)


        while True:
            event = read_event(reader)
            assert event.field_name is None, "Unexpected field name"

            if is_list_end(event):
                break

            assert is_struct_start(event), f"Expected struct start {repr(event)}"
            (field, field_value) = read_field_symbol(reader)
            assert field == "type", f"Unexpected field {field}"
            match field_value.text:
                case "import":
                    (field, value) = read_field_string(reader)
                    assert field == "name", f"Unexpected field {field}"
                    read_struct_end(reader)
                    dialect.add_import(value)
                case "syncat":
                    read_syncatdecl(reader, dialect)
                case "op":
                    (field, name) = read_field_string(reader)
                    assert field == "name", f"Unexpected field {field}"

                    event = read_event(reader)

                    args : tuple[ArgDecl, ...]
                    if has_field_symbol(event, "args"):
                        assert is_list_start(event), f"Expected {repr(event)} list start"
                        args = read_list(reader, read_arg_decl)
                        event = read_event(reader)
                    else:
                        args = ()

                    assert has_field_symbol(event, "result"), f"Expected result"
                    result_name = as_qualified_ident(event)
                    result = SyntaxCat(result_name)
                    read_struct_end(reader)

                    dialect.add_op(name, *args, result)

        event = read_event(reader)
        assert event.event_type == ion.IonEventType.STREAM_END, "Expected stream end"

        return dialect



_programSym = ion.SymbolToken(u'program', None, None)

class Program:
    dialect : Dialect
    command : list[Operation]

    def __init__(self, dialect: Dialect):
        self.dialect = dialect
        self.commands = []

    def add(self, command : Operation):
        assert type(command) is Operation
        self.commands.append(command)

    def to_ion(self):
        return [
            ion_sexp(_programSym, self.dialect.name),
            *(cmd.to_ion() for cmd in self.commands)
        ]


# FIXME: See if we can find way to keep this in sync with Lean implementation.
# Perhaps we can have Lean implementation export the dialect as a Ion file and
# ship it with Python library so we can read it in.
Init : typing.Any = Dialect('Init')
Init.add_syncat('Command')
Init.add_syncat('Expr')
Init.add_syncat('ByteArray')
Init.add_syncat('Ident')
Init.add_syncat('Num')
Init.add_syncat('Str')
Init.add_syncat('Type')
Init.add_syncat('CommaSepBy', ['x'])
Init.add_syncat('Option', ['x'])
Init.add_syncat('Seq', ['x'])
