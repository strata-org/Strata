import strata

from dataclasses import dataclass
from dis import Instruction
import dis
from typing import Any, Iterable
from pathlib import Path
from io import StringIO
import sys
import builtins
from typing import Callable, Iterator, Sized
from .exception_table import ExceptionTableEntry, parse_exception_table_entries
from .base import ArgDecl, Init, SyntaxCat, SyntaxArg, Indent
from . import base

PythonSSA : Any = strata.Dialect('PythonSSA')
"""
Eventual dialect Python SSA representation.

N.B.  This is currently empty.  Eventually the SSA form will be translated into
a Strata dialect, but that is not yet implemented.  
"""

class ValueBase:
    def __init__(self):
        pass

    def to_arg(self) -> base.Arg:
        raise NotImplementedError()

value_cat = PythonSSA.add_syncat("Value")()

none_value = PythonSSA.add_op("valueNone", value_cat, syntax='none')()

pos_int_value = PythonSSA.add_op("valueNum", ArgDecl("value", Init.Num()), value_cat,
                                 syntax=SyntaxArg("value"))

neg_int_value = PythonSSA.add_op("valueNegSucc", ArgDecl("value", Init.Num()), value_cat,
                                 syntax=t'-{SyntaxArg("value")}')

builtin_value = PythonSSA.add_op(
    "valueBuiltin", ArgDecl("value", Init.Str()), value_cat,
    syntax=t'builtin({SyntaxArg("value")})')

code_value = PythonSSA.add_op("valueCode", ArgDecl("value", Init.Str()), value_cat,
                              syntax=t'code({SyntaxArg("value")})')

class Builtin(ValueBase):
    value : str
    def __init__(self, value: str):
        self.value = value

    def __str__(self):
        return self.value

    def to_arg(self) -> base.Arg:
        return builtin_value(base.StrLit(self.value))

class CodeName(ValueBase):
    value : str

    def __init__(self, qualified_name: str):
        self.value = qualified_name

    def __str__(self):
        return f'#{self.value}'

    def to_arg(self) -> base.Arg:
        return code_value(base.StrLit(self.value))

str_value = PythonSSA.add_op("valueStr", ArgDecl("value", Init.Str()), value_cat,
                             syntax=SyntaxArg("value"))

class StringLit(ValueBase):
    value : str
    def __init__(self, value: str):
        assert isinstance(value, str)
        self.value = value

    def __str__(self):
        return repr(self.value)

    def to_arg(self) -> base.Arg:
        return str_value(base.StrLit(self.value))

globals_value = PythonSSA.add_op("globals", value_cat, syntax="globals")()

class GlobalNameMap(ValueBase):
    def __str__(self):
        return "@globals"

    def to_arg(self) -> base.Arg:
        return globals_value

arg_value = PythonSSA.add_op("valueArg", ArgDecl("arg", Init.Num()), value_cat)

class ArgValue(ValueBase):
    """An argument value"""
    index : int
    name : str

    def __init__(self, index : int, name : str):
        self.index = index
        self.name = name
        assert isinstance(self.name, str)

    def __str__(self):
        return self.name

    def to_arg(self) -> base.Arg:
        return arg_value(base.NumLit(self.index))

true_value = PythonSSA.add_op("valueTrue", value_cat)()
false_value = PythonSSA.add_op("valueFalse", value_cat)()

class BoolValue(ValueBase):
    """A boolean literal"""
    value : bool

    def __init__(self, value : bool):
        self.value = value

    def __str__(self):
        return str(self.value)

    def to_arg(self) -> base.Arg:
        return true_value if self.value else false_value

bytes_value = PythonSSA.add_op("valueBytes", ArgDecl("bytes", Init.Str()), value_cat)

class BytesValue(ValueBase):
    """An array of bytes"""
    value : bytes

    def __init__(self, value : bytes):
        self.value = value

    def __str__(self):
        return str(self.value)

    def to_arg(self) -> base.Arg:
        return bytes_value(base.StrLit(str(self.value))) # FIXME: Use bytes

reg_value = PythonSSA.add_op('valueReg', ArgDecl("index", Init.Num()), value_cat, syntax=t'r({SyntaxArg("index")})')

class RegValue(ValueBase):
    """Value returned by a statement"""
    value : int

    def __init__(self, value: int):
        self.value = value

    def __str__(self):
        return f'R{self.value}'

    def to_arg(self) -> base.Arg:
        return reg_value(base.NumLit(self.value))

block_value = PythonSSA.add_op("arg", ArgDecl("value", Init.Num()), value_cat, syntax=t'b{SyntaxArg("value")}')

class BlockArgument(ValueBase):
    """An argument to a basic block."""
    value : int

    def __init__(self, value: int):
        self.value = value

    def __str__(self):
        return f'B{self.value}'

    def to_arg(self) -> base.Arg:
       return block_value(base.NumLit(self.value))

concat_value = PythonSSA.add_op("valueConcat", ArgDecl("seq", Init.CommaSepBy(value_cat)), value_cat)

class StringConcat(ValueBase):
    """A string concatenation"""
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'build_string({val})'

    def to_arg(self) -> base.Arg:
        return concat_value(base.CommaSepBy([value_to_arg(a) for a in self.values]))

#FIXME
float_value = PythonSSA.add_op("valueFloat", value_cat)()

class FloatValue(ValueBase):
    """A floating point literal"""
    value : float

    def __init__(self, value : float):
        self.value = value

    def __str__(self):
        return f'{self.value}'

    def to_arg(self) -> base.Arg:
        return float_value # FIXME

slice_value = PythonSSA.add_op("valueSlice",
    ArgDecl("start", value_cat),
    ArgDecl("stop", value_cat),
    ArgDecl("step", value_cat),
    value_cat)

class SliceValue(ValueBase):
    """A slice literal"""
    start : 'Value'
    stop : 'Value'
    step : 'Value'

    def __init__(self, start : 'Value', stop : 'Value', step : 'Value'):
        self.start = start
        self.stop = stop
        self.step = step

    def __str__(self):
        return f'[{self.start}:{self.stop}:{self.step}]'

    def to_arg(self) -> base.Arg:
        return slice_value(
            value_to_arg(self.start),
            value_to_arg(self.stop),
            value_to_arg(self.step))

frozenset_value = PythonSSA.add_op("valueFrozenSet", ArgDecl("values", Init.CommaSepBy(value_cat)), value_cat)

class FrozenSetValue(ValueBase):
    """A frozen set literal"""
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert values is not None
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'set({val})'

    def to_arg(self) -> base.Arg:
        return frozenset_value(base.CommaSepBy([value_to_arg(a) for a in self.values]))

set_value = PythonSSA.add_op("valueSet", ArgDecl("values", Init.CommaSepBy(value_cat)), value_cat)

class SetValue(ValueBase):
    """A tuple literal"""
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert values is not None
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'set({val})'

    def to_arg(self) -> base.Arg:
        return set_value(base.CommaSepBy([value_to_arg(a) for a in self.values]))

list_value = PythonSSA.add_op("valueList", ArgDecl("values", Init.CommaSepBy(value_cat)), value_cat)

class ListValue(ValueBase):
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert values is not None
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'[{val}]'

    def to_arg(self) -> base.Arg:
        return list_value(base.CommaSepBy([value_to_arg(a) for a in self.values]))

tuple_value = PythonSSA.add_op("valueTuple", ArgDecl("values", Init.CommaSepBy(value_cat)), value_cat)

class Type():
    translate : Callable[[Any], base.Arg]
    def __init__(self, cat : SyntaxCat, translate : Callable[[Any], base.Arg]):
        assert isinstance(cat, SyntaxCat)
        self.cat = cat
        self.translate = translate

    def check_arg(self, arg : Any) -> base.Arg :
        r = self.translate(arg)
        assert not isinstance(r, base.OpDecl)
        return r

class StatementDecl:
    name : str
    args : dict[str, Type]
    returnCount : int
    terminal : bool
    decl : base.OpDecl

    def __init__(self,
                 name : str,
                 args : dict[str, Type],
                 returnCount : int,
                 terminal : bool,
                 decl : base.OpDecl):
        self.name = name
        self.args = args
        self.returnCount = returnCount
        self.terminal = terminal
        self.decl = decl
        assert len(self.args) + returnCount == len(decl.args)

bool_cat = PythonSSA.add_syncat("Bool")()

boolTrue = PythonSSA.add_op("boolTrue", bool_cat, syntax="true")()
boolFalse = PythonSSA.add_op("boolFalse", bool_cat, syntax="false")()

def bool_to_arg(a : Any):
    assert isinstance(a, bool)
    return boolTrue if a else boolFalse

BOOL = Type(bool_cat, bool_to_arg)

def num_to_arg(arg):
    assert isinstance(arg, int)
    return base.NumLit(arg)

NUM = Type(Init.Num(), num_to_arg)

def str_to_arg(a : Any):
    assert isinstance(a, str)
    return base.StrLit(a)

STR = Type(Init.Str(), str_to_arg)

def value_to_arg(arg : 'Value'):
    if arg is None:
        return none_value
    elif type(arg) == int:
        if arg >= 0:
            return pos_int_value(base.NumLit(arg))
        else:
            arg = (-arg) - 1
            return neg_int_value(base.NumLit(arg))
    else:
        assert isinstance(arg, ValueBase), f'Unexpected arg {type(arg)}'
        r = arg.to_arg()
        assert not isinstance(r, base.OpDecl), f'{type(arg)} invalid.'
        return r

VALUE = Type(value_cat, value_to_arg)

value_list_cat = PythonSSA.add_syncat("ValueList")()
value_list_op = PythonSSA.add_op(
    "mk_value_list",
    ArgDecl("elements", Init.CommaSepBy(value_cat)),
    value_list_cat,
    syntax=t'[{SyntaxArg("elements")}]')

def value_list_to_arg(arg : Any) -> base.Arg:
    assert isinstance(arg, tuple)
    args = [value_to_arg(a) for a in arg]
    return value_list_op(base.CommaSepBy(args))

VALUE_LIST = Type(value_list_cat, value_list_to_arg)

@dataclass
class JumpTarget:
    label : int
    arguments : tuple['Value',...]

    def __str__(self):
        return f'L{self.label}({", ".join((str(a) for a in self.arguments))})'

jump_target_cat = PythonSSA.add_syncat("JumpTarget")()

mk_jump_target_op = PythonSSA.add_op("mk_jump_target",
    ArgDecl("index", Init.Num()),
    ArgDecl("args", value_list_cat),
    jump_target_cat,
    syntax=t'target({SyntaxArg("index")}, {SyntaxArg("args")})')

def jump_target_to_arg(arg) -> base.Arg:
    assert isinstance(arg, JumpTarget)
    return mk_jump_target_op(base.NumLit(arg.label), value_list_to_arg(arg.arguments))

JUMP_TARGET = Type(jump_target_cat, jump_target_to_arg)
"""
A JumpTarget value.
"""

exc_handler_cat = PythonSSA.add_syncat("ExcHandler")()

no_exc_handler = PythonSSA.add_op("no_exc_handler",
    exc_handler_cat,
    syntax='none')()

exc_handler = PythonSSA.add_op("exc_handler",
    ArgDecl("target", jump_target_cat),
    ArgDecl("lasti", bool_cat),
    exc_handler_cat,
    syntax=t'exc({SyntaxArg("target")}, {SyntaxArg("lasti")})')

def exc_handler_to_arg(arg : Any) -> base.Arg:
    if arg is None:
        return no_exc_handler
    else:
        assert isinstance(arg, ExcHandler)
        return exc_handler(jump_target_to_arg(arg.target), bool_to_arg(arg.lasti))

EXC_HANDLER = Type(exc_handler_cat, exc_handler_to_arg)
"""
An optional jump-target value
"""

@dataclass
class Binding:
    name : 'Value'
    value : 'Value'

dict_binding_cat = PythonSSA.add_syncat("DictBinding")()

mk_dict_binding = PythonSSA.add_op("mk_binding", ArgDecl("name", value_cat), ArgDecl("value", value_cat), dict_binding_cat)

def binding_to_arg(arg : Any):
    assert isinstance(arg, Binding)
    return mk_dict_binding(value_to_arg(arg.name), value_to_arg(arg.value))

DICT_BINDING = Type(dict_binding_cat, binding_to_arg)

reg_cat = PythonSSA.add_syncat("Reg")()

mk_reg = PythonSSA.add_op("mk_reg", ArgDecl("index", Init.Num), reg_cat, syntax=t'r{SyntaxArg("index")}')

dict_entries_cat = PythonSSA.add_syncat("DictEntries")()
dict_entries_op = PythonSSA.add_op(
    "mk_dict_entries",
    ArgDecl("elements", Init.CommaSepBy(value_cat)),
    dict_entries_cat,
    syntax=t'{{{SyntaxArg("elements")}}}')

def dict_entries_to_arg(arg : Any) -> base.Arg:
    assert isinstance(arg, tuple)
    args = [binding_to_arg(a) for a in arg]
    return dict_entries_op(base.CommaSepBy(args))

DICT_ENTRIES = Type(dict_entries_cat, dict_entries_to_arg)

statement_cat = PythonSSA.add_syncat("Statement")()

def decl_statement(name : str, args : dict[str, Type], returnTypes : Sized|Type|None = None) -> StatementDecl:
    if returnTypes is None:
        rc = 0
    elif isinstance(returnTypes, Type):
        assert returnTypes.cat == VALUE.cat
        rc = 1
    else:
        assert isinstance(returnTypes, tuple)
        assert all((a.cat == VALUE.cat for a in returnTypes))
        rc = len(returnTypes)
    argdecls = [ ArgDecl(name, tp.cat) for (name, tp) in args.items() ]
    argc = len(args)
    assert all(f'r{i}' not in args for i in range(rc))
    retdecls = [ ArgDecl(f'r{i}', reg_cat) for i in range(rc) ]
    atoms = []
    match rc:
        case 0:
            pass
        case 1:
            atoms.append(base.SyntaxDefIdent(argc, 0))
            atoms.append(" = ")
        case _:
            atoms.append("(")
            for i in range(argc, argc + rc):
                atoms.append(base.SyntaxDefIdent(i, 0))
            atoms.append(")")
            atoms.append(" = ")
    atoms.append(name)
    atoms.append("(")
    for i in range(argc):
        if i > 0:
            atoms.append(", ")
        atoms.append(base.SyntaxDefIdent(i, 0))
    atoms.append(")")
    atoms.append("\n")
    op = PythonSSA.add_op(name, *argdecls, *retdecls, statement_cat, syntax = atoms)
    return StatementDecl(name, args, rc, False, op)

def exc_statement(name : str, args : dict[str, Type], returnTypes : Sized|Type|None = None):
    assert "exc" not in args
    args["exc"] = EXC_HANDLER
    return decl_statement(name, args, returnTypes)

term_statement_cat = PythonSSA.add_syncat("TermStatement")()

def term_statement(name : str, args : dict[str, Type]) -> StatementDecl:
    argdecls = (ArgDecl(name, tp.cat) for (name, tp) in args.items())
    atoms = []
    atoms.append(name)
    atoms.append("(")
    for i in range(len(args)):
        if i > 0:
            atoms.append(", ")
        atoms.append(base.SyntaxDefIdent(i, 0))
    atoms.append(")")
    atoms.append("\n")
    decl = PythonSSA.add_op(name, *argdecls, term_statement_cat, syntax=atoms)
    return StatementDecl(name, args, 0, True, decl)

import_decl = exc_statement("pyImport", { "name" : STR, "fromlist" : VALUE, "level" : VALUE }, VALUE)
"""
Implements `__import__` with the given arguments for `name`, `fromlist` and `level`.  
`globals` and `locals` are `None`.

This throws a `ModuleNotFoundError` if the module is not found.
"""

importfrom_decl = exc_statement("importfrom", { "module" : VALUE, "name" : STR }, VALUE)
"""
Imports name from the given module.

This throws an `ImportError` if the module does not contain the name.

Conversely `module.undefined_name`. throws an `AttributeError`, so it not the same.
"""

mk_tuple_decl = decl_statement("mk_tuple", { "entries" : VALUE_LIST }, VALUE)
"""
Creates a tuple for the entries.
"""

mk_dict_decl = decl_statement("mk_dict", { "entries" : DICT_ENTRIES }, VALUE)
"""
Creates a new dictionary key map for the entries.
"""

mk_ref_decl = decl_statement("mk_ref", {"value" : VALUE}, VALUE)

ref_load_decl = decl_statement("ref_load", { "ref" : VALUE }, VALUE)

ref_load_borrow = decl_statement("ref_load_borrow", { "ref" : VALUE }, VALUE)

ref_load_check_decl = exc_statement("ref_load_check", { "ref" : VALUE }, VALUE)
"""
Returns a reference to the value onto the stack, raising an UnboundLocalError
this is not a initialized reference.
"""

get_closure_decl = decl_statement("get_closure", { "expected" : NUM}, VALUE)
"""
Returns the closure for the current function as a tuple.
By construction the tuple should have `expected` arguments.

PyFunctionObject *func = _PyFrame_GetFunction(frame);
PyObject *closure = func->func_closure;
assert (closure has expected arguments)
"""

is_none_decl = decl_statement("is_none", { "value" : VALUE}, VALUE)

pytuple_get_item_decl = decl_statement("pytuple_get_item", { "tuple" : VALUE, "i" : NUM}, VALUE)
"""
Returns the element in the tuple at the given index.
"""

store_ref_decl = decl_statement("store_ref", { "ref" : VALUE, "value" : VALUE })

list_append_decl = decl_statement("list_append", {"l" : VALUE, "item" : VALUE})
"""Implements `list.append(l, item)`"""

list_extend_decl = decl_statement("list_extend", {"l" : VALUE, "seq" : VALUE})
"""Implements `list.extend(l, seq)`"""

set_add_decl = decl_statement("set_add", {"s" : VALUE, "item" : VALUE}, VALUE)
"""
Implements `set.add(s, item)`
"""

set_update_decl = decl_statement("set_update", {"s" : VALUE, "seq" : VALUE}, VALUE)
"""
Implements `set.update(s, seq)`
"""

call_function_ex_decl = decl_statement(
    'call_function_ex',
    {"f" : VALUE, "self" : VALUE, "args" : VALUE, "kwargs" : VALUE}, VALUE)
"""
Implements `f(*args)`
"""

load_special_decl = decl_statement('load_special', {"value" : VALUE, "arg" : NUM}, (VALUE, VALUE))
"""
Performs special method lookup on `value`.

If `type(value).__xxx__` is a method, return `(type(value).__xxx__, value).
Otherwise, return `(STACK[-1].__xxx__, None)`
"""

get_locals_decl = decl_statement("get_locals", {}, VALUE)
"""
Returns locals dictionary
"""

dict_setitem_decl = decl_statement("dict_setitem", {"d" : VALUE, "key" : VALUE, "value" : VALUE}, VALUE)
"""
Implements `dict.__setitem__(d, key, value)`
"""

load_name_decl = decl_statement("load_name", {"dict" : VALUE, "name" : STR}, VALUE)

store_name_decl = decl_statement("store_name", {"dict" : VALUE, "name" : STR, "value" : VALUE})

delete_name_decl = decl_statement("delete_name", { "dict" : VALUE, "name" : STR})

raise_name_error_decl = decl_statement("raise_name_error", { "name" : STR})

make_cell_decl = decl_statement("make_cell", {"value" : VALUE}, VALUE)

load_deref_decl = decl_statement("load_deref", {"cell" : VALUE}, VALUE)
"""
Loads the cell contained from the value and returns a reference to the object
the cell contains on the stack.
"""

store_deref_decl = decl_statement("store_deref", {"cell" : VALUE, "ref" : VALUE}, VALUE)
"""
Loads the cell contained from the value and returns a reference to the object
the cell contains on the stack.
"""

getattr_decl = decl_statement("getattr", {"value":VALUE, "name":STR}, VALUE)

getitem_decl = decl_statement("getitem", {"value": VALUE, "index": NUM}, VALUE)

getmethod_decl = \
    decl_statement(
        "getmethod",
        { "value" : VALUE, "name" : STR },
        (VALUE, VALUE))
"""
This will attempt to load a method `name` from the `value` object. 
This bytecode distinguishes two cases:

* if `value` has a method with the correct name, the bytecode returns the
  unbound method and `value`.

 * Otherwise, this returns `None` and the object returned by the attribute
   lookup.
"""

make_function_decl = decl_statement("make_function", { "code" : VALUE }, VALUE)
"""
Creates a new function object built from a code object.
"""

jump_decl = term_statement("jump", {"target" : JUMP_TARGET})
"""
Jump to `target` block.  Does not check for interrupts.
"""

jump_check_interrupt_decl = term_statement("jump_check_interrupt", {"target" : JUMP_TARGET})
"""
Jump to `target` block.  Checks for interrupts
"""

get_exc_info_decl = decl_statement("get_exc_info", {}, VALUE)
"""
Return the current exception info.

Used in exception handlers.
"""

set_exc_info_decl = decl_statement("set_exc_info", {"state" : VALUE})
"""
Set the current exception state.

See POP_EXCEPT
"""

branch_decl = term_statement("branch", {"value" : VALUE, "true_target" : JUMP_TARGET, "false_target" : JUMP_TARGET})
"""
Terminal statement with a branch to either true or false based on a labels.

Value must be a bool.
"""

call_decl = exc_statement("call", { "f" : VALUE, "obj" : VALUE, "args" : VALUE_LIST}, VALUE)
"""
Calls a callable object `f` with the number of arguments specified by argc.

On the stack are (in ascending order):
* The callable
* self or NULL
* The remaining positional arguments
"""

call_intrinsic_1_decl = decl_statement("call_intrinsic_1", {"intrinsic" : NUM, "arg" : VALUE}, VALUE)

call_kw_decl = exc_statement("call_kw", {"f" : VALUE, "obj" : VALUE, "args" : VALUE_LIST, "kw_names" : VALUE}, VALUE)
"""
Call keyword calls the given function `f` where
* `obj` is either the `self` argument or `None` for methods.
* `args` is a list of arguments.  It starts with the positional arguments and ends with keyword arguments.
* `kw_names` is a tuple of string for the keyword arguments.  The empty tuple is used
  for no keyword arguments.
* `exc` is a jump target for an exception handler - TODO: Figure out exception handling lasti
"""

check_exc_match_decl = decl_statement("check_exc_match", {"e" : VALUE, "class": VALUE}, VALUE)
"""
Returns a Boolean result indicating if `e` an exception matching `class`.
"""

compare_decl = decl_statement(
    "compare",
    { "cmp" : STR, "coerce" : BOOL, "x" : VALUE, "y" : VALUE },
    VALUE)

delete_decl = decl_statement("del", { "v" : VALUE})
"""
Deletes the given value.
"""

dict_merge_decl = decl_statement("dict_merge", { "x" : VALUE, "y" : VALUE})
"""
Like dict.update but raises exception for duplicate keys.
"""

dict_update_decl = decl_statement("dict_update", { "x" : VALUE, "y" : VALUE})
"""
Implements `dict.update(x, y)`
"""

in_decl = decl_statement("in", { "invert" : BOOL, "e" : VALUE, "s" : VALUE }, VALUE)
"""
Performs `e in s` operation if invert is 0 and `e not in s` operation if invert is 1.
"""

is_decl = decl_statement("is", {"invert" : BOOL, "e" : VALUE, "s" : VALUE }, VALUE)
"""
Performs `e is s` operation if invert is 0 and `e not is s` operation if invert is 1.
"""

format_spec_decl = decl_statement("format", {"value" : VALUE, "spec" : VALUE}, VALUE)
"""
Implements `value.__format__(spec)`

Used for format strings.
"""

load_from_dict_or_globals_decl = \
    decl_statement(
        "load_from_dict_or_globals",
        {"dict" : VALUE, "name" : STR},
        VALUE)
"""
Loads the value from the given dictionary or globals if not found
"""

get_iter_decl = decl_statement("get_iter", {"val" : VALUE}, VALUE)
"""
This calls iter and returns the value
"""

for_iter_decl = decl_statement(
    "for_iter",
    { "iter" : VALUE },
    (VALUE, VALUE))
"""
iter is an iterator.  Call its `__next__()` method.
If this yields a new value, return (true, new_value).

If the iterator indicates it is exhausted then return (false, None).
"""

return_decl = term_statement("return", {"value" : VALUE})
"""
Return from procedure with value (terminal)
"""

return_generator_decl = term_statement("return_generator", {})
"""
Return generator (terminal)
"""

with_exit_start_decl = decl_statement("with_exit_start", {"exit_func" : VALUE, "exit_self" : VALUE, "lasti" : VALUE, "exc" : VALUE}, VALUE)
"""
Run WITH_EXIT_START with the given exit function, exit self, lasti and exception values.
"""

yield_decl = decl_statement("yield", {"value":VALUE, "await" : BOOL})
"""
Yield a value from a generator.
"""

set_f_lasti_decl = decl_statement("set_f_lasti", {"lasti" : VALUE})
"""
Set `f_lasti` of the current frame.
"""

raise_prev_decl = term_statement("raise_prev", {})
"""
Reraise the given exception given through frame.
"""

raise_decl = term_statement("raise", {"exc" : VALUE})
"""
Raise the given exception given through frame.
"""

raise_with_cause_decl = term_statement("raise_with_cause", {"exc" : VALUE, "cause" : VALUE})
"""
Raise the given exception with the cause set to `cause`.
"""

reraise_decl = term_statement("reraise", {"exc" : VALUE})
"""
Reraise the given exception.
"""

set_function_attribute_decl = decl_statement(
    "set_function_attribute",
    { "function" : VALUE, "flag" : NUM, "value" : VALUE })
"""
Sets an attribute on a function object using the given value.

The flag determines which attribute to set:

* 0x01 a tuple of default values for positional-only and positional-or-keyword
  parameters in positional order
* 0x02 a dictionary of keyword-only parameters’ default values
* 0x04 a tuple of strings containing parameters’ annotations
* 0x08 a tuple containing cells for free variables, making a closure
"""

store_attr_decl = decl_statement(
    "store_attr",
    {"obj":VALUE, "name" : STR, "value" : VALUE})
"""
Implements `obj.name = value`
"""

unary_not_decl = decl_statement("not", {"val" : VALUE}, VALUE)
"""
Implements not
"""

binary_op_decl = decl_statement("binary_op", { "binop" : STR, "lhs" : VALUE, "rhs" : VALUE}, VALUE)

binary_subscr_decl = decl_statement(
    "binary_subscr",
    { "container" : VALUE, "key" : VALUE },
    VALUE)
"""
Implements `container[key]`
"""

store_subscr_decl = decl_statement(
    "store_subscr",
    { "container" : VALUE, "key" : VALUE, "value" : VALUE})
"""
Implements `container[key] = value`
"""

binary_slice_decl = decl_statement("binary_slice", {"container" : VALUE, "start" : VALUE, "end" : VALUE }, VALUE)
"""
Implements `container[start:end]`
"""

to_bool_decl = decl_statement("to_bool", {"value":VALUE}, VALUE)
"""
Implements `bool(value)`
"""

type Value = ValueBase | None | int

@dataclass
class ExcHandler:
    target : JumpTarget
    lasti : bool

type StatementArg = Value|JumpTarget|ExcHandler|str|tuple[Value,...]|tuple[Binding,...]

class Statement:
    register_base : int
    op : StatementDecl
    args : list[StatementArg]

    def __init__(self, register_base : int, op : StatementDecl, args : Iterable[StatementArg]):
        self.register_base = register_base
        self.op = op
        self.args = list(args)
        assert len(op.args) == len(self.args)

    def __str__(self):
        op = self.op
        result : str
        if op.returnCount > 0:
            result = ', '.join(f'R{self.register_base + i}' for i in range(op.returnCount))
            result = f'{result} = '
        else:
            result = ''

        def ppArg(a):
            if isinstance(a, list):
                return f'[{', '.join(ppArg(e) for e in a)}]'
            else:
                return str(a)
        return f'{result}@{self.op.name}({', '.join(ppArg(a) for a in self.args)})'

    def to_strata(self) -> base.Operation:
        decl = self.op.decl
        assert len(self.op.args) == len(self.args)
        args = (tp.check_arg(self.args[i]) for (i, tp) in enumerate(self.op.args.values()))
        self.op.returnCount
        rbase = self.register_base
        ret_args = (mk_reg(base.NumLit(rbase + i)) for i in range(self.op.returnCount))
        all_args = (*args, *ret_args)
        return decl(*all_args)

block_cat = PythonSSA.add_syncat("Block")()

mk_block = \
    PythonSSA.add_op(
        "mk_block",
        ArgDecl("index", Init.Num()),
        ArgDecl("inputs", Init.CommaSepBy(Init.Ident())),
        ArgDecl("statements", Init.Seq(statement_cat)),
        ArgDecl("term_statement", term_statement_cat),
        block_cat,
        syntax=t'block {SyntaxArg("index")}({SyntaxArg("inputs")}):\n{Indent(2, t"{SyntaxArg('statements')}{SyntaxArg('term_statement')}")}')

class Block:
    index : int
    input_count : int
    exception_handler : int|None
    readonly_height : int
    """Height that block should not be modified."""
    statements : list[Statement]
    term_statement : Statement|None

    def __init__(self,
                 jump_targets : dict[Offset, int],
                 index : int,
                 input_count : int,
                 block_offset : BlockOffset):
        """
        Create a block with the given index, offset within code block 
        """
        self.index = index
        self.input_count = input_count
        exception_handler = block_offset.exception_handler
        if exception_handler is None:
            self.exception_handler = None
            self.readonly_height = 0
        else:
            exception_index = jump_targets[exception_handler.target]
            depth = exception_handler.depth
            self.exception_handler = exception_index
            self.readonly_height = depth
        self.statements = []
        self.term_statement = None

    def to_strata(self) -> base.Operation:
        assert self.input_count is not None
        assert self.term_statement is not None
        return mk_block(
            base.NumLit(self.index),
            base.CommaSepBy([base.Ident(f'b{i}') for i in range(self.input_count)]),
            base.Seq([ s.to_strata() for s in self.statements ]),
            self.term_statement.to_strata()
            )

global_dict = GlobalNameMap()

class Globals:
    builtins : dict[str, Builtin]
    globals : set[str]

    def __init__(self):
        self.builtins = {}
        for b in builtins.__dict__.keys():
            self.add_builtin(b)
        self.add_secret_builtin("__builtins__.__build_class__")
        self.globals = set()

    def add_secret_builtin(self, *args : str):
        assert (name not in self.builtins for name in args)
        for name in args:
            self.builtins[name] = Builtin(name)

    def add_builtin(self, *args : str):
        assert (name not in self.builtins for name in args)
        for name in args:
            assert name in builtins.__dict__.keys(), f"{name} not in builtins"
            self.builtins[name] = Builtin(name)

    def find_name(self, name : str) -> Value:
        if name in self.builtins:
            return self.builtins[name]
        raise RuntimeError(f'Unknown name {name}')

type Offset = int

@dataclass
class BlockOffset:
    offset : Offset
    """
    Offset of first instruction in block (if known)
    """

    stack_height : int|None
    """
    Expected stack size at offset (if known)
    """

    exception_handler : ExceptionTableEntry|None
    """
    Offset of block with exception handler (if known)
    """


CONSTANT_ASSERTIONERROR = 0
CONSTANT_NOTIMPLEMENTEDERROR = 1
CONSTANT_BUILTIN_TUPLE = 2
CONSTANT_BUILTIN_ALL = 3
CONSTANT_BUILTIN_ANY = 4

common_constants : dict[int, Value] = {
    CONSTANT_ASSERTIONERROR: Builtin("AssertionError"),
    CONSTANT_NOTIMPLEMENTEDERROR: Builtin("NotImplementedError"),
    CONSTANT_BUILTIN_TUPLE: Builtin("tuple"),
    CONSTANT_BUILTIN_ALL: Builtin("all"),
    CONSTANT_BUILTIN_ANY: Builtin("any")
}

class Stack:
    _stack : list[Value]

    def __init__(self, values : list[Value]|None = None):
        self._stack = [] if values is None else values

    def pop(self) -> Value:
        """ Pop argument off stack"""
        assert len(self._stack) > 0
        return self._stack.pop()

    def push(self, value: Value):
        """ Push argument off stack"""
        assert value is None or type(value) == int or isinstance(value, ValueBase)
        return self._stack.append(value)

    def check_stack_height(self, offset : BlockOffset):
        """Check stack height matches height if previously recorded."""
        stack_height = len(self._stack)
        if offset.stack_height is not None:
            assert offset.stack_height == stack_height, \
                f'{offset} has mismatched stack heights {stack_height} and {offset.stack_height}.'
        else:
            offset.stack_height = stack_height

    def __iter__(self) -> Iterator[Value]:
        return iter(self._stack)

    def __len__(self) -> int:
        return len(self._stack)

    def __getitem__(self, rindex : int):
        assert type(rindex) == int
        assert rindex < 0 and -rindex <= len(self._stack), f'Invalid index {rindex} and {len(self._stack)}'
        index = len(self._stack) + rindex
        return self._stack[index]

    def __setitem__(self, rindex : int, value : Value):
        assert type(rindex) == int
        assert rindex < 0 and -rindex <= len(self._stack)
        index = len(self._stack) + rindex
        self._stack[index] = value

    def pop_n(self, n : int) -> tuple[Value, ...]:
        if n == 0:
            return ()
        else:
            assert 0 < n and n <= len(self._stack)
            val = tuple(self._stack[-n:])
            del self._stack[-n:]
            return val

class Translator:
    globals : Globals
    code : Any

    jump_targets : dict[Offset, int]
    """
    Map from offsets to the index of the block
    """

    block_offsets : list[BlockOffset]
    """
    Maps block indices to the block offsets.

    The inverse of jump_targets
    """

    blocks : list[Block|None]
    """Maps block offsets to the block"""

    cur_block : Block|None
    """Current block to add code to"""

    stack_heights : dict[Offset, int]
    """Maps block offsets to the expected stack height of block"""

    register_count : int
    """Number of register variables added so far."""

    name_dict : Value
    """Dictionary to write local updates to"""

    names : set[str]|None
    """Names of local variables"""

    co_vars : list[Value]
    """Co variable array used for local storage."""

    stack: Stack
    """Values in current stack"""

    def __init__(self, globals : Globals, code, block_offsets : list[BlockOffset]):

        assert code.co_nlocals == len(code.co_varnames)
        assert code.co_nlocals >= code.co_argcount
        # Module level code has no arguments
        assert code.co_qualname != "<module>" or code.co_argcount == 0
        assert (isinstance(nm, str) for nm in code.co_varnames)
        assert isinstance(code.co_cellvars, tuple)

        # Local count is arguments and locals plus free closure variables and additional
        # cell vars added for local storage.
        local_count = code.co_nlocals + len(code.co_freevars) + len(code.co_cellvars)

        self.globals = globals
        self.code = code
        jump_targets = { b.offset : idx for (idx, b) in enumerate(block_offsets) }
        self.jump_targets = jump_targets
        self.block_offsets = block_offsets

        self.stack_heights = {}
        self.cur_block = None

        self.register_count = 0

        self.stack = Stack([])
        first_block = Block(self.jump_targets, 0, 0, block_offsets[0])
        self.blocks = [first_block]
        self.cur_block = first_block

        # Initialize list of arguments
        arg_values = (ArgValue(i, code.co_varnames[i]) for i in range(code.co_argcount))
        nonarg_locals = local_count - code.co_argcount
        init_local_values = [ *arg_values, *([None] * nonarg_locals) ]
        self.co_vars = [self.mk_ref(v) for v in init_local_values ]

        if code.co_qualname == "<module>":
            self.name_dict = None
            self.names = None
        else:
            self.name_dict = self.mk_dict()
            self.names = set(code.co_varnames)

    def mk_dict(self):
        return self.add_stmt(mk_dict_decl, ())

    def stack_pop(self):
        """ Pop argument off stack"""
        return self.stack.pop()

    def stack_push(self, value: Value):
        """ Push argument off stack"""
        self.stack.push(value)

    def check_stack_height(self, offset : BlockOffset):
        """Check stack height matches height if previously recorded."""
        self.stack.check_stack_height(offset)

    def pop_n(self, n : int) -> tuple[Value, ...]:
        return self.stack.pop_n(n)

    def check_args(self, stmt : StatementDecl, args : tuple[StatementArg, ...]):
        assert len(stmt.args) == len(args)
        for (i, tp) in enumerate(stmt.args.values()):
            v = args[i]
            tp.check_arg(v)

    def create_regvalues(self, count : int):
        assert count >= 0
        base = self.register_count
        self.register_count += count
        match count:
            case 0:
                return
            case 1:
                return RegValue(base)
            case rc:
                return tuple(RegValue(i) for i in range(base, base+rc))

    def add_stmt(self, stmt : StatementDecl, *args : StatementArg) -> Any:
        assert not stmt.terminal
        block = self.cur_block
        assert isinstance(block, Block)
        base = self.register_count
        block.statements.append(Statement(base, stmt, args))
        return self.create_regvalues(stmt.returnCount)

    def add_term_stmt(self, stmt : StatementDecl, *args : StatementArg) -> Any:
        assert stmt.terminal
        assert stmt.returnCount == 0
        base = self.register_count
        block = self.cur_block
        assert block is not None
        assert block.term_statement is None
        self.check_args(stmt, args)
        block.term_statement = Statement(base, stmt, args)
        self.cur_block = None

    def mk_ref(self, value : Value) -> Value:
        return self.add_stmt(mk_ref_decl, value)

    def load_ref(self, ref : Value):
        return self.add_stmt(ref_load_decl, ref)

    def store_ref(self, ref : Value, value : Value):
        self.add_stmt(store_ref_decl, ref, value)

    def add_exc_stmt(self, decl : StatementDecl, *args: StatementArg) -> Value:
        exc = self.mk_exc_target()
        return self.add_stmt(decl, *args, exc)

    def do_call(self, fn : Value, selfObj : Value, *args: Value) -> Value:
        return self.add_exc_stmt(call_decl, fn, selfObj, args)

    def in_block(self) -> bool:
        return self.cur_block is not None

    def try_start_block(self, offset : Offset):
        """
        End current block and start a new block if we know
        stack height at offset.
        """
        block_index = self.jump_targets[offset]
        while len(self.blocks) < block_index:
            self.blocks.append(None)
        assert block_index == len(self.blocks)
        block_offset = self.block_offsets[block_index]

        if self.cur_block is not None:
            self.check_stack_height(block_offset)
            target = self.fallthrough_target()
            self.add_term_stmt(jump_decl, target)

        if block_offset.stack_height is None:
            # If block input_count is None, then this block is not reached
            # by a forward traversal so far.  Every reachable block appears
            # to be forward reachable so this is unreachable and we skip.
            # This case is only known to occur with exception handlers guarding
            # no code `try pass except ...`
            return

        assert type(block_offset.stack_height) is int
        input_count = len(self.co_vars) + block_offset.stack_height
        block = Block(self.jump_targets, block_index, input_count, block_offset)
        self.blocks.append(block)
        assert len(block.statements) == 0
        self.cur_block = block
        covar_count = len(self.co_vars)
        self.co_vars = [ BlockArgument(i) for i in range(covar_count)]
        self.stack = Stack([ BlockArgument(i) for i in range(covar_count, block.input_count)])

    def get_jump_target(self, target : int|None) -> JumpTarget:
        assert isinstance(target, int)
        assert target != 0

        block_index = self.jump_targets[target]
        block_offset = self.block_offsets[block_index]
        self.check_stack_height(block_offset)
        return JumpTarget(block_index, (*self.co_vars, *self.stack))

    def fallthrough_target(self):
        block_index = len(self.blocks)
        block_offset = self.block_offsets[block_index]
        self.check_stack_height(block_offset)
        return JumpTarget(block_index, (*self.co_vars, *self.stack))

    def translate_const(self, c) -> Value:
        if c is None:
            return None
        elif isinstance(c, bool):
            return BoolValue(c)
        elif type(c) == int:
            return c
        elif isinstance(c, bytes):
            return BytesValue(c)
        elif isinstance(c, str):
            return StringLit(c)
        elif isinstance(c, tuple):
            args = tuple(self.translate_const(a) for a in c)
            return self.add_stmt(mk_tuple_decl, args)
        elif isinstance(c, type(self.code)):
            return CodeName(c.co_qualname)
        elif isinstance(c, frozenset):
            assert (isinstance(a, str) for a in c)
            return FrozenSetValue((StringLit(v) for v in c))
        elif isinstance(c, float):
            return FloatValue(c)
        elif isinstance(c, slice):
            return SliceValue(c.start, c.stop, c.step)
        else:
            raise NotImplementedError(f'get_const {type(c)}')

    def get_const(self, arg : int|None) -> Value:
        assert isinstance(arg, int) and arg >= 0 and arg < len(self.code.co_consts)
        c = self.code.co_consts[arg]
        return self.translate_const(c)

    def get_name(self, arg : int|None) -> str:
        assert isinstance(arg, int)
        assert 0 <= arg and arg < len(self.code.co_names), f'Arg {arg} must be less than {len(self.code.co_names)}'
        name = self.code.co_names[arg]
        assert isinstance(name, str)
        return name

    def is_module_init(self):
        is_module_init = self.names is None
        assert is_module_init == (self.name_dict is None)
        return is_module_init

    def load_fast_borrow(self, var_num : int):
        """ Pushes borrowed reference to local variable `var_num` to stack."""
        ref = self.co_vars[var_num]
        val = self.add_stmt(ref_load_borrow, ref)
        self.stack_push(val)

    def load_global(self, name : str) -> Value:
        if name in self.globals.globals:
            return self.add_stmt(load_name_decl, global_dict, name)
        return self.globals.find_name(name)

    def store(self, dict : Value, name : str, val : Value):
        self.add_stmt(store_name_decl, dict, name, val)

    def BINARY_OP(self, ins : Instruction):
        op = ins.argrepr
        assert isinstance(op, str)
        rhs = self.stack_pop()
        lhs = self.stack_pop()
        val = self.add_stmt(binary_op_decl, op, lhs, rhs)
        self.stack_push(val)

    def BINARY_SLICE(self, ins : Instruction):
        """
        Implements `container[start:end]`
        """
        assert ins.arg is None
        end = self.stack_pop()
        start = self.stack_pop()
        container = self.stack_pop()
        slice = self.add_stmt(binary_slice_decl, container, start, end)
        self.stack_push(slice)

    def BINARY_SUBSCR(self, ins : Instruction):
        assert ins.arg is None
        key = self.stack_pop()
        container = self.stack_pop()
        val = self.add_stmt(binary_subscr_decl, container, key)
        self.stack_push(val)

    def BUILD_LIST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = ListValue(self.pop_n(arg))
        self.stack_push(val)

    def BUILD_MAP(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        pairs = self.pop_n(2 * count)
        bindings = tuple(Binding(pairs[2*i], pairs[2*i+1]) for i in range(count))
        val = self.add_stmt(mk_dict_decl, bindings)
        self.stack_push(val)

    def BUILD_STRING(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        val = StringConcat(self.pop_n(count))
        self.stack_push(val)

    def BUILD_SET(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = SetValue(self.pop_n(arg))
        self.stack_push(val)

    def BUILD_TUPLE(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.add_stmt(mk_tuple_decl, self.pop_n(arg))
        self.stack_push(val)

    def CALL(self, ins : Instruction):
        argc = ins.arg
        assert isinstance(argc, int)
        if argc > 999:
            raise NotImplementedError
        args = self.pop_n(argc)
        selfObj = self.stack_pop()
        fn = self.stack_pop()
        val = self.do_call(fn, selfObj, *args)
        self.stack_push(val)

    def CALL_FUNCTION_EX(self, ins : Instruction):
        assert ins.arg is None
        kwargs = self.stack_pop()
        args = self.stack_pop()
        self_value = self.stack_pop()
        fun = self.stack_pop()
        res = self.add_stmt(call_function_ex_decl, fun, self_value, args, kwargs)
        self.stack_push(res)

    def CALL_INTRINSIC_1(self, ins : Instruction):
        op = ins.arg
        assert isinstance(op, int)
        assert op >= 0
        val = self.stack_pop()
        res = self.add_stmt(call_intrinsic_1_decl, op, val)
        self.stack_push(res)

    def mk_exc_target(self) -> ExcHandler|None:
        block = self.cur_block
        assert block is not None
        block_offset = self.block_offsets[block.index]
        exc_block = block_offset.exception_handler
        if exc_block is None:
            return None
        else:
            assert type(block.exception_handler) is int
            depth = exc_block.depth
            assert type(depth) is int
            assert depth <= len(self.stack)
            slice = self.stack._stack[:depth]
            exc_args = (*self.co_vars, *slice)
            tgt = JumpTarget(block.exception_handler, exc_args)
            return ExcHandler(tgt, exc_block.lasti)

    def CALL_KW(self, ins : Instruction):
        argc = ins.arg
        assert isinstance(argc, int)

        names = self.stack_pop()
        args = tuple(self.pop_n(argc))
        self_or_null = self.stack_pop()
        callable = self.stack_pop()
        exc = self.mk_exc_target()
        val = self.add_stmt(call_kw_decl, callable, self_or_null, args, names, exc)
        self.stack_push(val)

    def CHECK_EXC_MATCH(self, ins : Instruction):
        """
        Performs exception matching for except.

        Tests whether the STACK[-2] is an exception matching STACK[-1].
        Pops STACK[-1] and pushes the boolean result of the test.

        """
        assert ins.arg is None
        assert len(self.stack) >= 2
        exc = self.stack[-2]
        tp = self.stack[-1]
        val = self.add_stmt(check_exc_match_decl, exc, tp)
        self.stack_pop()
        self.stack_push(val)

    def COMPARE_OP(self, ins : Instruction):
        opname = ins.arg
        assert isinstance(opname, int)
        op_idx = opname >> 5
        assert 0 <= op_idx and op_idx < len(dis.cmp_op)
        coerce = (opname & 16) != 0
        x = self.stack_pop()
        y = self.stack_pop()
        val = self.add_stmt(compare_decl, dis.cmp_op[op_idx], coerce, x, y)
        self.stack_push(val)

    def CONTAINS_OP(self, ins : Instruction):
        invert = ins.arg
        assert invert in [0, 1]
        e = self.stack_pop()
        s = self.stack_pop()
        val = self.add_stmt(in_decl, invert != 0, e, s)
        self.stack_push(val)

    def COPY(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        assert 0 < i
        assert i <= len(self.stack)
        self.stack_push(self.stack[-i])

    def COPY_FREE_VARS(self, ins : Instruction):
        """
        Copies the n free (closure) variables from the closure into the frame.
        Removes the need for special code on the caller’s side when calling closures.
        """
        n = ins.arg
        assert isinstance(n, int)
        assert 1 <= n
        offset = self.code.co_nlocals
        assert offset + n <= len(self.co_vars)
        closure = self.add_stmt(get_closure_decl, n)
        for i in range(n):
            val = self.add_stmt(pytuple_get_item_decl, closure, i)
            self.co_vars[offset + i] = val

    def DELETE_FAST(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        self.add_stmt(delete_decl, self.co_vars[var_num])

    def DELETE_NAME(self, ins : Instruction):
        name = self.get_name(ins.arg)
        if self.names is not None and name in self.names:
            val = self.add_stmt(delete_name_decl, self.name_dict, name)
        elif name in self.globals.globals:
            self.add_stmt(delete_name_decl, global_dict, name)
        else:
            self.add_stmt(raise_name_error_decl, name)

    def DICT_MERGE(self, ins : Instruction):
        assert len(self.stack) >= 2
        map = self.stack_pop()

        self.add_stmt(dict_merge_decl, self.stack[-1], map)

    def DICT_UPDATE(self, ins : Instruction):
        assert len(self.stack) >= 2
        map = self.stack_pop()
        self.add_stmt(dict_update_decl, self.stack[-1], map)

    def END_FOR(self, ins : Instruction):
        assert ins.arg is None
        # N.B. This is supposed to pop the stack, but always seems followed by POP_TOP.
        # self.stack_pop()

    def EXTENDED_ARG(self, ins : Instruction):
        assert isinstance(ins.arg, int)

    def FOR_ITER(self, ins : Instruction):
        """Implements STACK[-1] = iter(STACK[-1])."""
        delta = ins.arg
        assert isinstance(delta, int)
        assert len(self.stack) > 0
        iter = self.stack[-1]
        (success, val) = self.add_stmt(for_iter_decl, iter)

        false_target_offset = ins.jump_target
        false_target = self.get_jump_target(false_target_offset)

        self.stack_push(val)
        true_target = self.fallthrough_target()
        self.stack_pop()

        # Stack will reflect true height
        self.add_term_stmt(branch_decl, success, true_target, false_target)

    def FORMAT_SIMPLE(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.stack_push(self.add_stmt(format_spec_decl, val, StringLit("")))

    def FORMAT_WITH_SPEC(self, ins : Instruction):
        assert ins.arg is None
        spec = self.stack_pop()
        value = self.stack_pop()
        result = self.add_stmt(format_spec_decl, value, spec)
        self.stack_push(result)

    def GET_ITER(self, ins : Instruction):
        """
        This function appears to have a different implementation when
        executed then how it is documented and normally generated.  The
        documentation appears to be incorrectly documented as it has a special case for lists.
        If the value is a list or tuple, it returns the value and 0.  Otherwise,
        it calls iter and stores null.
        """
        assert ins.arg is None
        val = self.stack_pop()
        iter = self.do_call(Builtin("iter"), None, val)
        self.stack_push(iter)

    def IMPORT_FROM(self, ins : Instruction):
        name = self.get_name(ins.arg)
        assert len(self.stack) > 0
        module = self.stack[-1]
        val = self.add_exc_stmt(importfrom_decl, module, name)
        self.stack_push(val)

    def IMPORT_NAME(self, ins : Instruction):
        name = self.get_name(ins.arg)
        fromlist = self.stack_pop()
        level = self.stack_pop()
        val = self.add_exc_stmt(import_decl, name, fromlist, level)
        self.stack_push(val)

    def IS_OP(self, ins : Instruction):
        invert = ins.arg
        assert invert in [0, 1]
        e = self.stack_pop()
        s = self.stack_pop()
        val = self.add_stmt(is_decl, invert != 0, e, s)
        self.stack_push(val)

    def JUMP_FORWARD(self, ins : Instruction):
        target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(jump_decl, target)

    def JUMP_BACKWARD(self, ins : Instruction):
        target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(jump_check_interrupt_decl, target)

    def JUMP_BACKWARD_NO_INTERRUPT(self, ins : Instruction):
        target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(jump_decl, target)

    def LIST_APPEND(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        item = self.stack_pop()
        assert i > 0
        list = self.stack[-i]
        self.add_stmt(list_append_decl, list, item)

    def LIST_EXTEND(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int) and i > 0
        seq = self.stack_pop()
        l = self.stack[-i]
        self.add_stmt(list_extend_decl, l, seq)

    def LOAD_ATTR(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(namei >> 1)
        if namei & 1 == 1:
            val = self.stack_pop()
            (method, methodSelf) = self.add_stmt(getmethod_decl, val, name)
            self.stack_push(method)
            self.stack_push(methodSelf)
        else:
            val = self.stack_pop()
            val = self.add_stmt(getattr_decl, val, name)
            self.stack_push(val)

    def LOAD_BUILD_CLASS(self, _ : Instruction):
        self.stack_push(Builtin("__builtins__.__build_class__"))

    def LOAD_COMMON_CONSTANT(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = common_constants[arg]
        self.stack_push(val)

    def LOAD_CONST(self, ins : Instruction):
        arg = ins.arg
        val = self.get_const(arg)
        self.stack_push(val)

    def LOAD_DEREF(self, ins : Instruction):
        """
        Loads the cell contained in slot i of the “fast locals” storage.
        Pushes a reference to the object the cell contains on the stack.
        """
        i = ins.arg
        assert isinstance(i, int)
        if i >= len(self.co_vars):
            import inspect
            print(f'Invalid LOAD_DEREF {i} of {len(self.co_vars)}')
            for (k,v) in inspect.getmembers(self.code):
                print(f'{k}: {v}')
            exit(1)
        ref = self.add_stmt(load_deref_decl, self.co_vars[i])
        self.stack_push(ref)

    def LOAD_FAST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        self.stack_push(self.load_ref(self.co_vars[arg]))

    def LOAD_FAST_AND_CLEAR(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        # Get ref
        ref = self.co_vars[var_num]
        # Push value to stack
        self.stack_push(self.load_ref(ref))
        # Clear ref
        self.store_ref(ref, None)

    def LOAD_FAST_BORROW(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        self.load_fast_borrow(var_num)

    def LOAD_FAST_BORROW_LOAD_FAST_BORROW(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        self.load_fast_borrow(var_num >> 4)
        self.load_fast_borrow(var_num & 15)

    def LOAD_FAST_CHECK(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        ref = self.co_vars[var_num]
        val = self.add_exc_stmt(ref_load_check_decl, ref)
        self.stack_push(val)

    def LOAD_FAST_LOAD_FAST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        self.stack_push(self.load_ref(self.co_vars[arg >> 4]))
        self.stack_push(self.load_ref(self.co_vars[arg & 15]))

    def LOAD_FROM_DICT_OR_GLOBALS(self, ins : Instruction):
        assert isinstance(ins.arg, int)
        name = self.get_name(ins.arg)
        d = self.stack_pop()
        val = self.add_stmt(load_from_dict_or_globals_decl, d, name)
        self.stack_push(val)

    def LOAD_GLOBAL(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(namei>>1)
        val = self.load_global(name)
        if namei & 1 == 1:
            self.stack_push(None)
        self.stack_push(val)

    def LOAD_LOCALS(self, ins : Instruction):
        """
        Pushes a reference to the locals dictionary onto the stack.
        """
        assert ins.arg is None
        val = self.add_stmt(get_locals_decl)
        self.stack_push(val)

    def LOAD_NAME(self, ins : Instruction):
        assert isinstance(ins.arg, int)
        name = self.get_name(ins.arg)
        if self.names is not None and name in self.names:
            val = self.add_stmt(load_name_decl, self.name_dict, name)
        else:
            val = self.load_global(name)
        self.stack_push(val)

    def LOAD_SMALL_INT(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        self.stack_push(i)

    def LOAD_SPECIAL(self, ins : Instruction):
        """
        Performs special method lookup on STACK[-1].
        If type(STACK[-1]).__xxx__ is a method, leave type(STACK[-1]).__xxx__;
        STACK[-1] on the stack. If type(STACK[-1]).__xxx__ is not a method,
        leave STACK[-1].__xxx__; NULL on the stack.
        """
        arg = ins.arg
        assert isinstance(arg, int)
        assert arg >= 0
        val = self.stack_pop()
        method, obj = self.add_stmt(load_special_decl, val, arg)
        self.stack_push(method)
        self.stack_push(obj)

    def MAKE_CELL(self, ins : Instruction):
        var_num = ins.arg
        assert isinstance(var_num, int)
        assert var_num >= 0
        assert var_num < len(self.co_vars), f'Invalid var_num {var_num} of {len(self.co_vars)}'
        val = self.add_stmt(make_cell_decl, self.co_vars[var_num])
        self.co_vars[var_num] = val

    def MAKE_FUNCTION(self, ins : Instruction):
        assert ins.arg is None
        code = self.stack_pop()
        fn = self.add_stmt(make_function_decl, code)
        self.stack_push(fn)

    def MAP_ADD(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        assert i > 0
        value = self.stack_pop()
        key = self.stack_pop()
        self.add_stmt(dict_setitem_decl, self.stack[-i], key, value)

    def NOP(self, ins : Instruction):
        assert ins.arg is None
        pass

    def NOT_TAKEN(self, ins : Instruction):
        assert ins.arg is None
        # Do nothing code.
        # Used by the interpreter to record BRANCH_LEFT and BRANCH_RIGHT events for sys.monitoring.
        pass

    def POP_ITER(self, ins : Instruction):
        # Removes the iterator from the top of the stack.
        self.stack_pop()

    def POP_JUMP_IF_FALSE(self, ins : Instruction):
        cond = self.stack_pop()
        block_index = len(self.blocks)
        block_offset = self.block_offsets[block_index].offset
        assert self.cur_block is not None
        assert ins.offset <= block_offset, \
            f'Offset {ins.offset} <= {block_offset}'

        true_target = self.fallthrough_target()
        false_target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(branch_decl, cond, true_target, false_target)

    def POP_JUMP_IF_NONE(self, ins : Instruction):
        val = self.stack_pop()
        cond = self.add_stmt(is_none_decl, val)
        true_target = self.get_jump_target(ins.jump_target)
        false_target = self.fallthrough_target()
        self.add_term_stmt(branch_decl, cond, true_target, false_target)

    def POP_JUMP_IF_NOT_NONE(self, ins : Instruction):
        val = self.stack_pop()
        cond = self.add_stmt(is_none_decl, val)
        true_target = self.fallthrough_target()
        false_target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(branch_decl, cond, true_target, false_target)

    def POP_JUMP_IF_TRUE(self, ins : Instruction):
        cond = self.stack_pop()
        true_target = self.get_jump_target(ins.jump_target)
        false_target = self.fallthrough_target()
        self.add_term_stmt(branch_decl, cond, true_target, false_target)

    def POP_EXCEPT(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.add_stmt(set_exc_info_decl, val)

    def POP_TOP(self, ins : Instruction):
        assert ins.arg is None
        self.stack_pop()

    def PUSH_EXC_INFO(self, ins : Instruction):
        """
        Pops a value from the stack.
        Pushes the current exception to the top of the stack.
        Pushes the value originally popped back to the stack.
        Used in exception handlers.
        """

        assert ins.arg is None
        val = self.stack_pop()
        exc = self.add_stmt(get_exc_info_decl)
        self.stack_push(exc)
        self.stack_push(val)

    def PUSH_NULL(self, ins : Instruction):
        assert ins.arg is None
        self.stack_push(None)

    def RAISE_VARARGS(self, ins : Instruction):
        """
        Raises an exception using one of the 3 forms of the raise statement, depending on the value of argc:

        0: raise (re-raise previous exception)
        1: raise STACK[-1] (raise exception instance or type at STACK[-1])
        2: raise STACK[-2] from STACK[-1] (raise exception instance or type at STACK[-2] with __cause__ set to STACK[-1])
        """
        argc = ins.arg
        assert isinstance(argc, int)
        assert argc in range(2)
        match argc:
            case 0:
                self.add_term_stmt(raise_prev_decl)
            case 1:
                exc = self.stack_pop()
                self.add_term_stmt(raise_decl, exc)
            case 2:
                exc = self.stack_pop()
                cause = self.stack_pop()
                self.add_term_stmt(raise_with_cause_decl, exc, cause)

    def RERAISE(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        exc = self.stack_pop()
        if arg != 0:
            val = self.stack_pop()
            self.add_stmt(set_f_lasti_decl, val)
        self.add_term_stmt(reraise_decl, exc)

    def RESUME(self, ins : Instruction):
        assert isinstance(ins.arg, int)

    def RETURN_CONST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.get_const(arg)
        self.add_term_stmt(return_decl, val)

    def RETURN_GENERATOR(self, ins : Instruction):
        """

        See https://github.com/python/cpython/blob/ff7bb565d836162eed0851c36afa325a107a5a56/InternalDocs/generators.md
        """
        assert ins.arg is None
        assert ins.jump_target is None
        self.add_term_stmt(return_generator_decl)

    def RETURN_VALUE(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.add_term_stmt(return_decl, val)



    def SET_ADD(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int) and i > 0
        item = self.stack_pop()
        self.add_stmt(set_add_decl, self.stack[-i], item)



    def SET_FUNCTION_ATTRIBUTE(self, ins : Instruction):
        flag = ins.arg
        assert isinstance(flag, int)
        assert flag >= 0
        fun = self.stack_pop()
        val = self.stack_pop()
        self.add_stmt(set_function_attribute_decl, fun, flag, val)
        self.stack_push(fun)

    def SET_UPDATE(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        assert i > 0

        assert len(self.stack) >= 2
        seq = self.stack_pop()
        s = self.stack[-i]
        self.add_stmt(set_update_decl, s, seq)

    def SETUP_ANNOTATIONS(self, ins : Instruction):
        assert ins.arg is None
        name = "__annotations__"
        if self.names is not None:
            if name not in self.names:
                self.names.add(name)
                self.store(self.name_dict, name, self.mk_dict())
        else:
            if name not in self.globals.globals:
                self.globals.globals.add(name)
                self.store(global_dict, name, self.mk_dict())

    def STORE_ATTR(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(ins.arg)
        obj = self.stack_pop()
        value = self.stack_pop()
        self.add_stmt(store_attr_decl, obj, name, value)

    def STORE_DEREF(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        cell = self.co_vars[i]
        val = self.stack_pop()
        self.add_stmt(store_deref_decl, cell, val)

    def STORE_FAST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        ref = self.co_vars[arg]
        val = self.stack_pop()
        self.store_ref(ref, val)

    def STORE_FAST_LOAD_FAST(self, ins : Instruction):
        var_nums = ins.arg
        assert isinstance(var_nums, int)
        store_index = var_nums >> 4
        load_index = var_nums & 15
        store_val = self.stack_pop()
        self.store_ref(self.co_vars[store_index], store_val)
        load_val = self.load_ref(self.co_vars[load_index])
        self.stack_push(load_val)

    def STORE_FAST_STORE_FAST(self, ins : Instruction):
        """
        Stores STACK[-1] into co_varnames[var_nums >> 4] and STACK[-2] into co_varnames[var_nums & 15].
        """
        var_nums = ins.arg
        assert isinstance(var_nums, int)
        self.co_vars[var_nums >> 4] = self.stack_pop()
        self.co_vars[var_nums & 15] = self.stack_pop()

    def STORE_NAME(self, ins : Instruction):
        name = self.get_name(ins.arg)
        val = self.stack_pop()
        if self.names is None:
            self.globals.globals.add(name)
            self.store(global_dict, name, val)
        else:
            self.names.add(name)
            self.store(self.name_dict, name, val)

    def STORE_SUBSCR(self, ins : Instruction):
        key = self.stack_pop()
        container = self.stack_pop()
        value = self.stack_pop()
        self.add_stmt(store_subscr_decl, container, key, value)

    def SWAP(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        stack = self.stack
        assert 1 < i and i <= len(stack), f'Swap {i} with length {len(stack)}'
        (stack[-i], stack[-1]) = (stack[-1], stack[-i])

    def TO_BOOL(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.stack_push(self.add_stmt(to_bool_decl, val))

    def UNARY_NOT(self, ins : Instruction):
        assert ins.arg is None
        assert len(self.stack) > 0
        val = self.stack[-1]
        self.stack[-1] = self.add_stmt(unary_not_decl, val)

    def UNPACK_SEQUENCE(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        val = self.stack_pop()
        for i in reversed(range(count)):
            self.stack_push(self.add_stmt(getitem_decl, val, i))

    def WITH_EXCEPT_START(self, ins : Instruction):
        assert len(self.stack) >= 5
        exc = self.stack[-1]
        lasti = self.stack[-3]
        exit_self = self.stack[-4]
        exit_func = self.stack[-5]

        res = self.add_stmt(with_exit_start_decl, exit_func, exit_self, lasti, exc)
        self.stack_push(res)

    def YIELD_VALUE(self, ins : Instruction):
        arg = ins.arg
        assert arg == 0 or arg == 1
        assert len(self.stack) > 0
        val = self.stack[-1]
        self.add_stmt(yield_decl, val, arg != 0)

def handler_for(exceptions : list[ExceptionTableEntry], entry : Offset) -> ExceptionTableEntry|None:
    for ex in exceptions:
        if ex.start <= entry and entry - ex.start < ex.length:
            return ex
    return None

def create_block_offsets(
        insns : list[dis.Instruction],
        exceptions : list[ExceptionTableEntry]) -> list[BlockOffset]:
    """Create sorted list of block offsets from list of instructions."""
    assert len(insns) > 0
    last_offset = insns[-1].offset

    # Maps block offsets to the expected stack height or None if
    # expected stack height is unknown.
    # N.B. The expected stack height is only known for exception
    # targets
    block_offset_map : dict[Offset, int|None] = {}
    block_offset_map[0] = 0

    # Initialize block offsets from exception table entries.
    # Exception handling is documented here:
    # https://github.com/python/cpython/blob/b881df47ff1adca515d1de04f689160ddae72142/InternalDocs/exception_handling.md

    for e in exceptions:
        start = e.start
        end = start + e.length
        assert isinstance(start, int)
        assert isinstance(e.length, int)
        assert isinstance(e.target, int)
        if start not in block_offset_map:
            block_offset_map[start] = None
        if end <= last_offset and end not in block_offset_map:
            block_offset_map[end] = None

        prev = block_offset_map.get(e.target, None)
        height = e.target_stack_height()
        if prev is None:
            depth = e.depth + 1
            if e.lasti:
                depth += 1
            block_offset_map[e.target] = height
        else:
            assert prev == height

    next_jump_target : bool = True
    next_jump_stack : int|None = None
    for insn in insns:
        # Create next jump target if needed
        if next_jump_target:
            assert isinstance(insn.offset, int)
            if insn.offset not in block_offset_map:
                block_offset_map[insn.offset] = next_jump_stack
            next_jump_target = False

        target = insn.jump_target
        if target is not None:
            if target not in block_offset_map:
                block_offset_map[target] = None
            next_jump_target = True
            next_jump_stack = None
        match insn.opname:
            case 'RETURN_GENERATOR':
                assert target is None
                next_jump_target = True
                next_jump_stack = 1
            case 'YIELD_VALUE':
                assert target is None
                next_jump_target = True
                next_jump_stack = None
    def mk_block_offset(off : Offset, tgt : int|None):
        return BlockOffset(off, tgt, handler_for(exceptions, off))
    return sorted((mk_block_offset(off, h) for (off, h) in block_offset_map.items()), key=lambda x: x.offset)

class RedirectStdStreams(object):
    def __init__(self, stdout=None, stderr=None):
        self._stdout = stdout or sys.stdout
        self._stderr = stderr or sys.stderr

    def __enter__(self):
        self.old_stdout = sys.stdout
        self.old_stdout.flush()
        self.old_stderr = sys.stderr
        self.old_stderr.flush()

        sys.stdout = self._stdout
        sys.stderr = self._stderr

    def __exit__(self, exc_type, exc_value, traceback):
        self._stdout.flush()
        self._stderr.flush()
        sys.stdout = self.old_stdout
        sys.stderr = self.old_stderr

def compile_path(path : Path, contents : bytes) -> tuple[Any, str]:
    output = StringIO()
    with RedirectStdStreams(stdout = output, stderr=output):
        c = compile(contents, mode='exec', filename=path)
    return (c, output.getvalue())

class MissingInstructions:
    """Class that collects missing instructions."""
    missing : dict[Path, set[str]|None]

    supported : set[str]

    def __init__(self):
        self.missing = dict()
        self.supported = set(Translator.__dict__.keys())

    def add_missing(self, missing : set[str], co):
        codeType = type(co)
        for c in co.co_consts:
            if isinstance(c, codeType):
                self.add_missing(missing, c)
        insns = list(dis.get_instructions(co))

        # Set of block from jump target to block index.
        for ins in insns:
            if ins.opname not in self.supported:
                missing.add(ins.opname)

    def analyze_code(self, path : Path):
        if path in self.missing:
            return
        try:
            with open(path, 'rb') as r:
                contents = r.read()
            (c, _) = compile_path(path, contents)
        except SyntaxError as e:
            self.missing[path] = None
            return

        missing = set()
        self.add_missing(missing, c)
        self.missing[path] = missing

    def analyze_dir(self, path : Path):
        if path.is_dir():
            for p in path.glob('**/*.py'):
                print(f'Analyzing {p}')
                self.analyze_code(p)
        else:
            self.analyze_code(path)

        counts : dict[str, tuple[Path, int]] = {}
        successes = 0
        total = 0
        for (p, m) in self.missing.items():
            if m is None:
                continue
            total = total + 1
            if len(m) == 0:
                successes = successes + 1
            for opcode in m:
                c = counts.get(opcode, None)
                if c is None:
                    counts[opcode] = (p, 1)
                else:
                    counts[opcode] = (c[0], c[1] + 1)
        r = sorted(counts.items(), key=lambda p: (p[1][1], p[0]), reverse=True)
        print(f'{len(counts)} missing operations:')
        for (k, (p, c)) in r:
            print(f"{k}: {c} ({p})")
        print(f"Succcess: {successes}/{total}")

def generate_blocks(globals, co) -> list[Block]:
    codeType = type(co)
    consts = co.co_consts
    assert isinstance(consts, tuple)

    insns = list(dis.get_instructions(co))

    assert isinstance(co.co_exceptiontable, bytes)
    exception_table = parse_exception_table_entries(co.co_exceptiontable)

    supported = set(Translator.__dict__.keys())
    assert all(ins.opname in supported for ins in insns) or True

    # Set of block from jump target to block index.
    block_offsets = create_block_offsets(insns, exception_table)
    translator = Translator(globals, co, block_offsets)
    for ins in insns:
        offset = ins.offset
        if offset != 0 and offset in translator.jump_targets:
            translator.try_start_block(offset)
        if not translator.in_block():
            continue
        f = getattr(translator, ins.opname, None)
        assert f is not None, f'Missing support for {ins.opname}'
        f(ins)

    return [ b for b in translator.blocks if b is not None ]

function_decl = \
    PythonSSA.add_op(
        "mk_function",
        ArgDecl("name", Init.Str()),
        ArgDecl("args", Init.Seq(Init.Str())),
        ArgDecl("blocks", Init.Seq(block_cat)),
        Init.Command(),
        syntax=t'function {SyntaxArg("name")}({SyntaxArg("args")})\n{Indent(2, SyntaxArg("blocks"))}')

@dataclass
class Function:
    name : str
    args : list[str]
    blocks : list[Block]

    def to_strata(self) -> base.Operation:
        assert isinstance(self.name, str)
        assert all(isinstance(a, str) for a in self.args)

        return function_decl(
            base.StrLit(self.name),
            base.Seq([base.StrLit(a) for a in self.args]),
            base.Seq([b.to_strata() for b in self.blocks if b is not None]))

    def to_ion(self):
        return self.to_strata().to_ion()

def extract_functions(prev : list[Function], globals : Globals, code):

    codeType = type(code)

    blocks = generate_blocks(globals, code)

    args = [ code.co_varnames[i] for i in range(code.co_argcount)]

    prev.append(Function(code.co_qualname, args, blocks))

    for c in code.co_consts:
        if isinstance(c, codeType):
            extract_functions(prev, globals, c)


def py_to_ssa(path : Path, contents : bytes) -> list[Function]:
    (code, _) = compile_path(path, contents)
    codeType = type(code)

    globals = Globals()
    prev = []
    extract_functions(prev, globals, code)
    return prev

def find_code(globals : Globals, n : int, co):
    codeType = type(co)
    consts = co.co_consts
    assert isinstance(consts, tuple)

    insns = list(dis.get_instructions(co))


    print(f'Function {co.co_qualname}')

    print(f'  Instructions ({len(insns)}):')
    for ins in insns:
        print(f'    {ins.offset}: {ins.opname} {ins.arg} ({ins.argval}, line={ins.line_number})')

    assert isinstance(co.co_exceptiontable, bytes)
    exception_table = parse_exception_table_entries(co.co_exceptiontable)

    if len(exception_table) > 0:
        print(f'  {len(exception_table)} exception table entries:')
        for entry in exception_table:
            print(f'    {entry.pretty_format()}')

    supported = set(Translator.__dict__.keys())
    incomplete = any(ins.opname not in supported for ins in insns) or True

    # Set of block from jump target to block index.
    block_offsets = create_block_offsets(insns, exception_table)

    translator = Translator(globals, co, block_offsets)
    for ins in insns:
        offset = ins.offset
        if offset != 0 and offset in translator.jump_targets:
            translator.try_start_block(offset)
        if not translator.in_block():
            continue
        if incomplete:
            print(f'{offset}: {ins.opname} {ins.arg} ({ins.argval}) (stack=[{", ".join(str(s) for s in translator.stack)}])')
        f = getattr(translator, ins.opname, None)
        if f is not None:
            f(ins)
        else:
            print("Exiting due to no support.")
            exit(1)

    print(f'  Statements:')
    for (idx, block) in enumerate(translator.blocks):
        if block is None:
            continue
        assert block.index == idx
        assert isinstance(block.input_count, int)
        assert block.term_statement is not None
        args = ', '.join([f'B{idx}' for idx in range(block.input_count)])
        print(f'    L{idx}({args}):')
        for stmt in block.statements:
            print(f'      {stmt}')
        print(f'      {block.term_statement}')

    for c in consts:
        if isinstance(c, codeType):
            find_code(globals, n + 1, c)
