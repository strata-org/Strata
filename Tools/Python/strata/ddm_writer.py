"""
Ion binary output for Strata PythonSpecs DDM format.

Generates .pyspec.st.ion files directly from icontract-decorated Python,
without requiring Lean compilation.

Requires: amazon.ion (pip install amazon.ion)
"""

import amazon.ion.simpleion as ion
from amazon.ion.core import IonType
from amazon.ion.simple_types import IonPySymbol, IonPyNull
import io


# ---------------------------------------------------------------------------
# Ion s-expression helpers
# ---------------------------------------------------------------------------

def _sym(name: str):
    """Create an Ion symbol."""
    return IonPySymbol(text=name)


def _sexp(*args):
    """Create an Ion s-expression (tuple with Ion type annotation)."""
    result = ion.loads(ion.dumps(list(args), binary=False))
    # We need to build sexps manually
    return args  # placeholder — we'll use a different approach


# The DDM Ion format uses s-expressions (sexp) extensively.
# amazon.ion doesn't have great sexp support, so we build the
# binary Ion directly using the low-level writer.

from amazon.ion.writer import blocking_writer
from amazon.ion.writer_binary import binary_writer
from amazon.ion.core import IonEvent, IonEventType, IonType, SymbolToken


class IonDDMWriter:
    """Writes Strata DDM PythonSpecs Ion binary format."""

    def __init__(self):
        self._buf = io.BytesIO()
        self._writer = blocking_writer(
            binary_writer(),
            self._buf
        )

    def _start_sexp(self):
        self._writer.send(IonEvent(IonEventType.CONTAINER_START, IonType.SEXP))

    def _end_sexp(self):
        self._writer.send(IonEvent(IonEventType.CONTAINER_END))

    def _start_list(self):
        self._writer.send(IonEvent(IonEventType.CONTAINER_START, IonType.LIST))

    def _end_list(self):
        self._writer.send(IonEvent(IonEventType.CONTAINER_END))

    def _symbol(self, text: str):
        self._writer.send(IonEvent(IonEventType.SCALAR, IonType.SYMBOL,
                                    value=SymbolToken(text=text, sid=None)))

    def _string(self, text: str):
        self._writer.send(IonEvent(IonEventType.SCALAR, IonType.STRING, value=text))

    def _int(self, value: int):
        self._writer.send(IonEvent(IonEventType.SCALAR, IonType.INT, value=value))

    def _bool(self, value: bool):
        self._writer.send(IonEvent(IonEventType.SCALAR, IonType.BOOL, value=value))

    def _null(self):
        self._writer.send(IonEvent(IonEventType.SCALAR, IonType.NULL))

    # -- DDM node builders --

    def _op(self, op_name: str, *children_fn):
        """Write (op (OP_NAME null ...children...))"""
        self._start_sexp()  # op wrapper
        self._symbol("op")
        self._start_sexp()  # inner op
        self._symbol(op_name)
        self._null()  # annotation slot
        for fn in children_fn:
            fn()
        self._end_sexp()
        self._end_sexp()

    def _strlit(self, value: str):
        """Write (strlit null "value")"""
        self._start_sexp()
        self._symbol("strlit")
        self._null()
        self._string(value)
        self._end_sexp()

    def _ident(self, name: str):
        """Write (ident null name)"""
        self._start_sexp()
        self._symbol("ident")
        self._null()
        self._symbol(name)
        self._end_sexp()

    def _num(self, value: int):
        """Write (num null N)"""
        self._start_sexp()
        self._symbol("num")
        self._null()
        self._int(value)
        self._end_sexp()

    def _option_none(self):
        """Write (option null) — None"""
        self._start_sexp()
        self._symbol("option")
        self._null()
        self._end_sexp()

    def _option_some(self, child_fn):
        """Write (option null child)"""
        self._start_sexp()
        self._symbol("option")
        self._null()
        child_fn()
        self._end_sexp()

    def _seq(self, *children_fn):
        """Write (seq null ...children...)"""
        self._start_sexp()
        self._symbol("seq")
        self._null()
        for fn in children_fn:
            fn()
        self._end_sexp()

    def _commaSepList(self, *children_fn):
        """Write (commaSepList null ...children...)"""
        self._start_sexp()
        self._symbol("commaSepList")
        self._null()
        for fn in children_fn:
            fn()
        self._end_sexp()

    # -- SpecType builders --

    def _typeIdentNoArgs(self, ident_str: str):
        """typeIdentNoArgs("builtins.int") → (op (PythonSpecs.typeIdentNoArgs null (strlit null "builtins.int")))"""
        self._op("PythonSpecs.typeIdentNoArgs",
                 lambda: self._strlit(ident_str))

    def _typeIdent(self, ident_str: str, args_fn):
        """typeIdent with args"""
        self._op("PythonSpecs.typeIdent",
                 lambda: self._strlit(ident_str),
                 args_fn)

    # -- SpecExpr builders --

    def _placeholderExpr(self):
        self._op("PythonSpecs.placeholderExpr")

    def _varExpr(self, name: str):
        self._op("PythonSpecs.varExpr", lambda: self._ident(name))

    def _isInstanceOfExpr(self, subject_fn, type_name: str):
        self._op("PythonSpecs.isInstanceOfExpr", subject_fn,
                 lambda: self._strlit(type_name))

    def _lenExpr(self, subject_fn):
        self._op("PythonSpecs.lenExpr", subject_fn)

    def _intExpr(self, value: int):
        if value >= 0:
            self._op("PythonSpecs.intExpr",
                     lambda: self._op("PythonSpecs.natInt",
                                       lambda: self._num(value)))
        else:
            self._op("PythonSpecs.intExpr",
                     lambda: self._op("PythonSpecs.negInt",
                                       lambda: self._num(-value)))

    def _intGeExpr(self, subject_fn, bound_fn):
        self._op("PythonSpecs.intGeExpr", subject_fn, bound_fn)

    def _intLeExpr(self, subject_fn, bound_fn):
        self._op("PythonSpecs.intLeExpr", subject_fn, bound_fn)

    def _intAddExpr(self, left_fn, right_fn):
        self._op("PythonSpecs.intAddExpr", left_fn, right_fn)

    def _intSubExpr(self, left_fn, right_fn):
        self._op("PythonSpecs.intSubExpr", left_fn, right_fn)

    def _intMulExpr(self, left_fn, right_fn):
        self._op("PythonSpecs.intMulExpr", left_fn, right_fn)

    def _intEqExpr(self, left_fn, right_fn):
        self._op("PythonSpecs.intEqExpr", left_fn, right_fn)

    def _floatExpr(self, value: str):
        self._op("PythonSpecs.floatExpr", lambda: self._strlit(value))

    def _floatGeExpr(self, subject_fn, bound_fn):
        self._op("PythonSpecs.floatGeExpr", subject_fn, bound_fn)

    def _floatLeExpr(self, subject_fn, bound_fn):
        self._op("PythonSpecs.floatLeExpr", subject_fn, bound_fn)

    def _getIndexExpr(self, subject_fn, field: str):
        self._op("PythonSpecs.getIndexExpr", subject_fn,
                 lambda: self._ident(field))

    def _enumMemberExpr(self, subject_fn, values: list):
        self._op("PythonSpecs.enumMemberExpr", subject_fn,
                 lambda: self._seq(*[lambda v=v: self._strlit(v) for v in values]))

    def _notExpr(self, inner_fn):
        self._op("PythonSpecs.notExpr", inner_fn)

    def _forallListExpr(self, list_fn, var_name: str, body_fn):
        self._op("PythonSpecs.forallListExpr", list_fn,
                 lambda: self._ident(var_name), body_fn)

    # -- Assertion / Message --

    def _strMessagePart(self, text: str):
        self._op("PythonSpecs.strMessagePart", lambda: self._strlit(text))

    def _mkAssertion(self, formula_fn, message: str):
        self._op("PythonSpecs.mkAssertion",
                 formula_fn,
                 lambda: self._seq(lambda: self._strMessagePart(message)))

    # -- ArgDecl --

    def _mkArgDecl(self, name: str, type_fn, has_default: bool):
        default_fn = (lambda: self._option_some(
            lambda: self._op("PythonSpecs.noneDefault")
        )) if has_default else self._option_none
        self._op("PythonSpecs.mkArgDecl",
                 lambda: self._ident(name),
                 type_fn,
                 default_fn)

    # -- FunDecl --

    def _mkFunDecl(self, name: str, args_fns, kwonly_fns, return_type_fn,
                   is_overload: bool, precondition_fns, postcondition_fns):
        self._op("PythonSpecs.mkFunDecl",
                 lambda: self._strlit(name),
                 lambda: self._seq(*args_fns),
                 lambda: self._seq(*kwonly_fns),
                 self._option_none,  # kwargs
                 return_type_fn,
                 lambda: self._op("Init.boolTrue" if is_overload else "Init.boolFalse"),
                 lambda: self._seq(*precondition_fns),
                 lambda: self._seq(*postcondition_fns))

    def _functionDecl(self, fun_decl_fn):
        self._start_sexp()
        self._symbol("PythonSpecs.functionDecl")
        self._null()
        fun_decl_fn()
        self._end_sexp()

    def _classDef(self, class_decl_fn):
        self._start_sexp()
        self._symbol("PythonSpecs.classDef")
        self._null()
        class_decl_fn()
        self._end_sexp()

    # -- Program wrapper --

    def write_program(self, command_fns: list):
        """Write the full DDM program: [(program "PythonSpecs"), cmd1, cmd2, ...]"""
        self._start_list()
        # Header: (program "PythonSpecs")
        self._start_sexp()
        self._symbol("program")
        self._string("PythonSpecs")
        self._end_sexp()
        # Commands
        for fn in command_fns:
            fn()
        self._end_list()

    def get_bytes(self) -> bytes:
        self._writer.send(IonEvent(IonEventType.STREAM_END))
        return self._buf.getvalue()
