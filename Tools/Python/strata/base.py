# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""
Description: Core Strata AST datatypes.
"""
from dataclasses import dataclass
from decimal import Decimal
import typing

import amazon.ion.simpleion as ion

def append_args(v, args):
    if len(args) == 0:
        return v
    l = [v]
    for a in args:
        l.append(a.to_ion())
    return l

def ion_symbol(s : str):
    return ion.IonPySymbol(s, None)

def ion_sexp(*args):
    h : typing.Any = ion.IonPyList()
    h.ion_type = ion.IonType.SEXP
    for a in args:
        h.append(a)
    return h

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
    ident : QualifiedIdent
    args: list['SyntaxCat']

    def __init__(self, ident: QualifiedIdent, args: list['SyntaxCat'] | None = None):
        self.ident = ident
        self.args = [] if args is None else args

    def strPrec(self, prec: int) -> str:
        s = f'{str(self.ident)}{"".join(' ' + a.strPrec(10) for a in self.args)}'
        return f'({s})' if prec > 0 else s

    def __str__(self) -> str:
        return self.strPrec(0)

    def to_ion(self):
        return append_args(self.ident.to_ion(), self.args)

class TypeExpr:
    def to_ion(self):
        raise NotImplementedError

@dataclass
class TypeIdent(TypeExpr):
    ident: QualifiedIdent
    args: list[TypeExpr]

    def to_ion(self):
        v = self.ident.to_ion()
        return append_args(v, self.args)

@dataclass
class TypeBVar(TypeExpr):
    index: int
    bvarSym = ion_symbol("bvar")
    def to_ion(self):
        return [self.bvarSym, self.index]

@dataclass
class TypeFVar(TypeExpr):
    index: int
    args: list[TypeExpr]

    fvarSym = ion_symbol("fvar")

    def to_ion(self):
        l = [self.fvarSym, self.index]
        for a in self.args:
            l.append(a.to_ion())
        return l

@dataclass
class TypeArrow(TypeExpr):
    arg: TypeExpr
    res: TypeExpr

    arrowSym = ion_symbol("arrow")

    def to_ion(self):
        return [self.arrowSym, self.arg, self.res]

@dataclass
class TypeFunMacro(TypeExpr):
    bindingsIndex: int
    res: TypeExpr

    funMacroSym = ion_symbol("funMacro")
    def to_ion(self):
        return [self.funMacroSym, self.bindingsIndex, self.res]

@dataclass
class Ident:
    value: str

@dataclass
class NumLit:
    value: int

    numSym = ion_symbol("num")

    def __init__(self, value: int):
        assert isinstance(value, int)
        assert value >= 0
        self.value = value

    def to_ion(self):
        return [self.numSym, self.value]

@dataclass
class StrLit:
    value: str

    def __init__(self, value: str):
        self.value = value

    def __str__(self):
        return f'StrLit({repr(self.value)})'

@dataclass
class SomeArg:
    value: 'Arg'

    def __init__(self, value: 'Arg'):
        self.value = value

    def to_ion(self):
        return ["option", arg_to_ion(self.value)]

    def __str__(self):
        return f'SomeArg({self.value})'

@dataclass
class Seq:
    values: list['Arg']

    def __init__(self, values: list['Arg']):
        self.values = values

    def __str__(self) -> str:
        return f"Seq([{', '.join(str(a) for a in self.values)}])"

@dataclass
class CommaSepList:
    values: list['Arg']

    def __init__(self, values: list['Arg']):
        self.values = values

class Expr:
    def to_ion(self):
        raise NotImplementedError

@dataclass
class ExprBVar(Expr):
    idx : int
    args : list['Arg']
    def to_ion(self):
        l = [ "bvar", self.idx ]
        for a in self.args:
            l.append(arg_to_ion(a))
        return l

@dataclass
class ExprFVar(Expr):
    level : int
    args : list['Arg']
    def to_ion(self):
        l = [ "fvar", self.level ]
        for a in self.args:
            l.append(arg_to_ion(a))
        return l

dataclass
class ExprIdent(Expr):
    ident : QualifiedIdent
    args : list['Arg']
    def to_ion(self):
        l : list[object] = [ self.ident.to_ion() ]
        for a in self.args:
            l.append(arg_to_ion(a))
        return l

@dataclass
class Operation:
    decl : 'OpDecl'
    args : dict[str, 'Arg']

    def __init__(self, decl : 'OpDecl', args : list['Arg']|None = None):
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

    def to_ion(self) -> list[object]:
        l : list[object] = [self.decl.ident.to_ion()]
        for a in self.args.values():
            l.append(arg_to_ion(a))
        return l

type Arg = SyntaxCat | Operation | TypeExpr | Expr | Ident \
    | NumLit | Decimal | StrLit | None | SomeArg | Seq | CommaSepList

def arg_to_ion(a : Arg) -> list[object]:
    if isinstance(a, SyntaxCat):
        return ["cat", a.to_ion()]
    elif isinstance(a, Operation):
        return ["op", a.to_ion()]
    elif isinstance(a, TypeExpr):
        return ["type", a.to_ion()]
    elif isinstance(a, Expr):
        return ["expr", a.to_ion()]
    elif isinstance(a, Ident):
        return ["ident", a.value]
    elif isinstance(a, NumLit):
        return a.to_ion()
    elif isinstance(a, Decimal):
        return ["decimal", a]
    elif isinstance(a, StrLit):
        return ["strlit", a.value]
    elif a is None:
        return ["option"]
    elif isinstance(a, SomeArg):
        return a.to_ion()
    else:
        l : list[object]
        if isinstance(a, Seq):
            l = ["seq"]
        else:
            assert isinstance(a, CommaSepList)
            l = ["commaSepList"]
        for e in a.values:
            l.append(arg_to_ion(e))
        return l

class Program:
    programSym = ion.SymbolToken(u'program', None, None)

    def __init__(self, dialect: str):
        self.dialect = dialect
        self.commands = []

    def add(self, command):
        assert command is not None
        self.commands.append(command)

    def to_ion(self):
        r = [ion_sexp(self.programSym, self.dialect)]
        for cmd in self.commands:
            r.append(cmd.to_ion())
        return r

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
        return [self.someSym, metadata_arg_to_ion(self.value)]

@dataclass
class MetadataAttr:
    ident : QualifiedIdent
    args : list[object]


    def to_ion(self):
        l : list[object] = [self.ident.to_ion()]
        for a in self.args:
            l.append(metadata_arg_to_ion(a))
        return l

type Metadata = list[MetadataAttr]

def metadata_to_ion(values):
    return [ v.to_ion() for v in values ]

def declbinding_kind(v: SyntaxCat|TypeExpr):
    if isinstance(v, SyntaxCat):
        return ["category", v.to_ion()]
    else:
        assert isinstance(v, TypeExpr)
        return ["type", v.to_ion()]

class SyntaxDefAtomBase:
    def to_ion(self):
        raise NotImplementedError()

@dataclass
class SyntaxDefIdent(SyntaxDefAtomBase):
    level: int
    prec: int

    def to_ion(self):
        return ("ident", self.level, self.prec)

@dataclass
class SyntaxDefIndent(SyntaxDefAtomBase):
    indent: int
    args : list['SyntaxDefAtom']

    def to_ion(self):
        l : list[object] = ["indent", self.indent]
        for a in self.args:
            l.append(syntaxdef_atom_to_ion(a))
        return l

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
            "type": declbinding_kind(self.kind),
        }
        if len(self.metadata) > 0:
            flds["metadata"] = metadata_to_ion(self.metadata)
        return flds

class OpDecl:
    opSym = ion.SymbolToken(u'op', None, None)
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
        self.result = result
        self.metadata = [] if metadata is None else metadata
        self.syntax = syntax

    def __call__(self, *args):
        assert len(args) == len(self.args), f"{self.ident} given {len(args)} argument(s) when {len(self.args)} expected ({args})"
        return Operation(self, list(args))

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
