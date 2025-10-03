# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""
Description: Core Strata AST datatypes.
"""
from bisect import bisect_right
from dataclasses import dataclass
from decimal import Decimal
import typing
from typing import Any

import amazon.ion.simpleion as ion

def ion_symbol(s : str):
    return ion.IonPySymbol(s, None)

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
    args: list['SyntaxCat']

    def __init__(self, name: QualifiedIdent, args: list['SyntaxCat'] | None = None, *, ann = None):
        self.ann = ann
        self.name = name
        self.args = [] if args is None else args

    def strPrec(self, prec: int) -> str:
        s = f'{str(self.name)}{"".join(' ' + a.strPrec(10) for a in self.args)}'
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

class Operation:
    ann : Any
    decl : 'OpDecl'
    args : dict[str, 'Arg']

    def __init__(self, decl : 'OpDecl', args : list['Arg']|None = None, *, ann = None):
        self.ann = ann
        self.decl = decl
        if args is None:
            args = []
        assert len(decl.args) == len(args)
        self.args = {}
        for i in range(len(decl.args)):
            self.args[decl.args[i].name] = args[i]

    def __str__(self) -> str:
        t = ', '.join(f'{n}={str(v)}' for (n,v) in self.args.items())
        return f'{str(self.decl.ident)}({t})'

    def to_ion(self) -> object:
        return ion_sexp(
            self.decl.ident.to_ion(),
            ann_to_ion(self.ann),
            *(arg_to_ion(a) for a in self.args.values())
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
        assert isinstance(value, int)
        assert value >= 0
        self.ann = ann
        self.value = value

@dataclass
class DecimalLit:
    ann : Any
    value: Decimal

    def __init__(self, value: Decimal, *, ann = None):
        assert isinstance(value, int)
        assert value >= 0
        self.ann = ann
        self.value = value

@dataclass
class StrLit:
    ann : Any
    value: str

    def __init__(self, value: str, *, ann = None):
        self.ann = ann
        self.value = value

    def __str__(self):
        return f'StrLit({repr(self.value)})'

@dataclass
class OptionArg:
    ann : Any
    value: 'Arg|None'

    def __init__(self, value: 'Arg|None', *, ann = None):
        self.ann = ann
        self.value = value

    def __str__(self):
        if self.value is None:
            return 'None'
        else:
            return f'Some({self.value})'

@dataclass
class Seq:
    ann : Any
    values: list['Arg']

    def __init__(self, values: list['Arg'], *, ann = None):
        self.ann = ann
        self.values = values

    def __str__(self) -> str:
        return f"Seq([{', '.join(str(a) for a in self.values)}])"

@dataclass
class CommaSepList:
    ann : Any
    values: list['Arg']

    def __init__(self, values: list['Arg'], *, ann = None):
        self.ann = ann
        self.values = values

type Arg = SyntaxCat | Operation | TypeExpr | Expr | Ident \
    | NumLit | DecimalLit | StrLit | OptionArg | Seq | CommaSepList

strlitSym = ion_symbol("strlit")
numSym = ion_symbol("num")

optionSym = ion_symbol("option")

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
        return ion_sexp(ion_symbol("strlit"), ann_to_ion(a.ann), val)
    elif isinstance(a, OptionArg):
        if a.value is None:
            return ion_sexp(optionSym, ann_to_ion(a.ann))
        else:
            return ion_sexp(optionSym, ann_to_ion(a.ann), arg_to_ion(a.value))
    elif isinstance(a, Seq):
        return ion_sexp(ion_symbol("seq"), ann_to_ion(a.ann), *(arg_to_ion(e) for e in a.values))
    else:
        assert isinstance(a, CommaSepList), f'Expected {type(a)} to be a CommaSepList.'
        return ion_sexp(ion_symbol("commaSepList"), ann_to_ion(a.ann), *(arg_to_ion(e) for e in a.values))

class Program:
    programSym = ion.SymbolToken(u'program', None, None)

    def __init__(self, dialect: str):
        self.dialect = dialect
        self.commands = []

    def add(self, command):
        assert command is not None
        self.commands.append(command)

    def to_ion(self):
        return [
            ion_sexp(self.programSym, self.dialect),
            *(cmd.to_ion() for cmd in self.commands)
        ]

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

type Metadata = list[MetadataAttr]

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
    args : list['SyntaxDefAtom']

    def to_ion(self):
        return ion_sexp(ion_symbol("indent"), self.indent, *(syntaxdef_atom_to_ion(a) for a in self.args))

type SyntaxDefAtom = SyntaxDefAtomBase | str

def syntaxdef_atom_to_ion(atom : SyntaxDefAtom) -> object:
    if isinstance(atom, str):
        return atom
    else:
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

class SynCatDecl:
    syncat = ion.SymbolToken(u'syncat', None, None)
    def __init__(self, dialect : str, name : str, args: list[str]|None = None):
        self.dialect = dialect
        self.name = name
        self.ident = QualifiedIdent(dialect, name)
        self.argNames = [] if args is None else args

    def __call__(self, *args):
        assert len(args) == len(self.argNames)
        return SyntaxCat(self.ident, list(args))

    def to_ion(self):
        return {
            "type": self.syncat,
            "name": self.name,
            "arguments": self.argNames
        }

@dataclass
class ArgDecl:
    "Argument declaration in operator or function"
    name: str
    kind : SyntaxCat|TypeExpr
    metadata: Metadata

    def __init__(self, name: str, kind : SyntaxCat|TypeExpr, metadata: Metadata|None = None):
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

class OpDecl:
    opSym = ion.SymbolToken(u'op', None, None)
    result : QualifiedIdent

    def __init__(self,
                dialect: str,
                name: str,
                args: list[ArgDecl],
                result : SyntaxCat,
                *,
                syntax : SyntaxDef|None = None,
                metadata : Metadata|None = None):
        assert all( isinstance(a, ArgDecl) for a in args)
        self.dialect = dialect
        self.name = name
        self.ident = QualifiedIdent(dialect, name)
        self.args = args
        assert isinstance(result, SyntaxCat)
        assert len(result.args) == 0
        self.result = result.name
        self.metadata = [] if metadata is None else metadata
        self.syntax = syntax

    def __call__(self, *args, ann=None):
        assert len(args) == len(self.args), f"{self.ident} given {len(args)} argument(s) when {len(self.args)} expected ({args})"
        return Operation(self, list(args), ann=ann)

    def to_ion(self):
        flds = {
             "type": self.opSym,
             "name": self.name,
        }
        if len(self.args) > 0:
            flds["args"] = [ a.to_ion() for a in self.args ]
        flds["result"] = self.result.to_ion()
        if self.syntax is not None:
            flds["syntax"] = self.syntax.to_ion()
        if len(self.metadata) > 0:
            flds["metadata"] = metadata_to_ion(self.metadata)
        return flds

class TypeDecl:
    typeSymbol = ion.SymbolToken(u'type', None, None)
    def __init__(self, name, argNames):
        self.name = name
        self.argNames = argNames

    def to_ion(self):
        return {
            "type": self.typeSymbol,
            "name": self.name,
            "argNames": self.argNames
        }

class Dialect:
    dialectSym = ion.SymbolToken(u'dialect', None, None)

    def __init__(self, name: str):
        self.name = name
        self.imports = []
        self.decls = []

    def add_import(self, name: str):
        self.imports.append(name)

    def add_syncat(self, name : str, args: list[str]|None = None) -> SynCatDecl:
        decl = SynCatDecl(self.name, name, args)
        self.add(decl)
        return decl

    def add_op(self, name : str, args: list[ArgDecl], result : SyntaxCat, *,
            syntax : SyntaxDef|None = None,
            metadata : Metadata|None = None) -> OpDecl:
        decl = OpDecl(self.name, name, args, result, syntax=syntax, metadata=metadata)
        self.add(decl)
        return decl

    def add(self, decl):
        assert decl is not None
        if isinstance(decl, SynCatDecl):
            assert (decl.dialect == self.name)
            if decl.name in self.__dict__:
                raise Exception(f"{decl.name} already added: {self.__dict__[decl.name]}")
            self.__dict__[decl.name] = decl
        elif isinstance(decl, OpDecl):
            assert (decl.dialect == self.name)
            assert (decl.name not in self.__dict__)
            self.__dict__[decl.name] = decl

        self.decls.append(decl)

    def to_ion(self):
        r : list[object] = [(self.dialectSym, self.name)]
        for i in self.imports:
            r.append({"type": "import", "name": i})
        for d in self.decls:
            r.append(d.to_ion())
        return r

# FIXME: See if we can find way to keep this in sync with Lean implementation.
# Perhaps we can have Lean implementation export the dialect as a Ion file and
# ship it with Python library so we can read it in.
Init : typing.Any = Dialect('Init')
Init.add_syncat('Command')
Init.add_syncat('Expr')
Init.add_syncat('Num')
Init.add_syncat('Str')
Init.add_syncat('Type')
Init.add_syncat('CommaSepList', ['x'])
Init.add_syncat('Option', ['x'])
Init.add_syncat('Seq', ['x'])
