from dataclasses import dataclass
from decimal import Decimal
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
    h = ion.IonPyList()
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

    def to_ion(self):
        return ion_symbol(f"{self.dialect}.{self.name}")



@dataclass
class SyntaxCat:
    ident : QualifiedIdent
    args: list['SyntaxCat']

    def __init__(self, ident: QualifiedIdent, args: list['SyntaxCat'] | None = None):
        self.ident = ident
        self.args = [] if args is None else args

    def to_ion(self):
        return append_args(self.ident.to_ion(), self.args)

class TypeExpr:
    pass

@dataclass
class TypeIdent(TypeExpr):
    name: QualifiedIdent
    args: list[TypeExpr]

    def to_ion(self):
        v = name.to_ion()
        return append_args(v, l)

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
        l = [fvarSym, self.index]
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

@dataclass
class SomeArg:
    value: 'Arg'

    def __init__(self, value: 'Arg'):
        self.value = value

    def to_ion(self):
        return ["option", arg_to_ion(self.value)]

@dataclass
class Seq:
    values: list['Arg']

    def __init__(self, values: list['Arg']):
        self.values = values

@dataclass
class CommaSepList:
    values: list['Arg']

    def __init__(self, values: list['Arg']):
        self.values = values

class Expr:
    pass

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
        l = [ self.ident.to_ion() ]
        for a in self.args:
            l.append(arg_to_ion(a))
        return l

@dataclass
class Operation:
    op : QualifiedIdent
    args : list['Arg']

    def __init__(self, op : QualifiedIdent, args : list['Arg']|None = None):
        self.op = op
        if args is None:
            self.args = []
        else:
            self.args = args

    def to_ion(self):
        l = [self.op.to_ion()]
        for a in self.args:
            l.append(arg_to_ion(a))
        return l

type Arg = SyntaxCat | Operation | TypeExpr | Expr | Ident \
    | NumLit | Decimal | StrLit | None | SomeArg | Seq | CommaSepList

def arg_to_ion(a : Arg):
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
        return ion_sexp(categorySym, self.index)

@dataclass
class MetadataSome:
    value: object

    someSym = ion_symbol("some")
    def to_ion(self):
        return [someSym, metadata_arg_to_ion(self.value)]

@dataclass
class MetadataAttr:
    ident : QualifiedIdent
    args : list[object]

    def to_ion(self):
        l = [ident.to_ion()]
        for a in args:
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

class SynCatDecl:
    syncat = ion.SymbolToken(u'syncat', None, None)
    def __init__(self, name, *args):
        self.name = name
        if len(args) == 1:
            self.argNames = args[0]
        else:
            assert len(args) == 0
            self.argNames = []

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

class SyntaxDefAtomBase:
    pass

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
        l = ["indent", self.indent]
        for a in args:
            l.append(syntaxdef_atom(a))
        return l

type SyntaxDefAtom = SyntaxDefAtomBase | str

def syntaxdef_atom_to_ion(atom : SyntaxDefAtom):
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

class OpDecl:
    opSym = ion.SymbolToken(u'op', None, None)
    def __init__(self,
                name: str,
                args: list[ArgDecl],
                result : SyntaxCat,
                **kwargs):
        assert all( isinstance(a, ArgDecl) for a in args)
        self.name = name
        self.args = args
        self.result = result
        try:
            self.syntax = kwargs["syntax"]
            assert isinstance(self.syntax, SyntaxDef)
        except KeyError:
            self.syntax = None
        try:
            self.metadata = kwargs["metadata"]
        except KeyError:
            self.metadata = []

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
            "type": typeSymbol,
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

    def add(self, decl):
        assert decl is not None
        self.decls.append(decl)

    def to_ion(self):
        r = [(self.dialectSym, self.name)]
        for i in self.imports:
            r.append({"type": "import", "name": i})
        for d in self.decls:
            r.append(d.to_ion())
        return r
