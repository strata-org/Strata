import strata

from dataclasses import dataclass
from dis import Instruction
import dis
from typing import Any, Iterable
from pathlib import Path
from io import StringIO
import sys
import builtins
from typing import Sized
from .exception_table import parse_exception_table_entries

PythonSSA : Any = strata.Dialect('PythonSSA')
"""
Eventual dialect Python SSA representation.

N.B.  This is currently empty.  Eventually the SSA form will be translated into
a Strata dialect, but that is not yet implemented.  
"""

class ValueBase:
    def __init__(self):
        pass

class Builtin(ValueBase):
    value : str
    def __init__(self, value: str):
        self.value = value

    def __str__(self):
        return self.value

class CodeName(ValueBase):
    value : str

    def __init__(self, qualified_name: str):
        self.value = qualified_name

    def __str__(self):
        return f'#{self.value}'

class StringLit(ValueBase):
    value : str
    def __init__(self, value: str):
        self.value = value

    def __str__(self):
        return repr(self.value)

class GlobalNameMap(ValueBase):
    def __init__(self):
        pass

    def __str__(self):
        return "@globals"

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

class RegValue(ValueBase):
    """Value returned by a statement"""
    value : int

    def __init__(self, value: int):
        self.value = value

    def __str__(self):
        return f'R{self.value}'

class DictValue(ValueBase):
    """A dictionary value (currently only empty supported)"""
    def __str__(self):
        return '{}'

class StringConcat(ValueBase):
    """A string concatenation"""
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'build_string({val})'

class TupleValue(ValueBase):
    """A tuple literal"""
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert values is not None
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'({val})'

class ListValue(ValueBase):
    values : Iterable['Value']

    def __init__(self, values : Iterable['Value']):
        assert values is not None
        assert (isinstance(a, str) for a in values)
        self.values = values

    def __str__(self):
        val = ', '.join((str(a) for a in self.values))
        return f'[{val}]'

class BlockArgument(ValueBase):
    """An argument to a basic block."""
    value : int

    def __init__(self, value: int):
        self.value = value

    def __str__(self):
        return f'B{self.value}'

@dataclass
class JumpTarget:
    label : int
    arguments : list['Value']

    def __str__(self):
        return f'L{self.label}({", ".join((str(a) for a in self.arguments))})'

class StatementDecl:
    name : str
    args : Iterable[str]
    returnCount : int

    def __init__(self, name : str, args : Iterable[str], returnCount : int):
        self.name = name
        self.args = args
        self.returnCount = returnCount

class Type():
    def __init__(self, name : str):
        self.name = name

BIN_OP = Type("bin_op")
STR = Type("string")
VALUE = Type("value")
INT = Type("int")

def decl_statement(name : str, args : dict[str, Type], returnTypes : Sized|Type) -> StatementDecl:
    rc = 1 if isinstance(returnTypes, Type) else len(returnTypes)
    return StatementDecl(name, args, rc)


import_decl = StatementDecl("import", ("name", "globals", "locals", "fromlist", "level"), 1)

importfrom_decl = StatementDecl("importfrom", ("module", "name"), 1)
"""
Imports name from the declaration
"""

mk_dict = StatementDecl("mk_dict", (), 1)

mk_ref_decl = StatementDecl("mk_ref", ("value",), 1)

build_const_key_map_decl = StatementDecl("build_const_key_map", ("names", "values"), 1)
"""
Creates a constant key map with names from the tuple `names` and values from tuple `values`

The number of elements in names and values should match as this is compiler generated.
"""

load_ref_decl = StatementDecl("load_ref", ("ref", ), 1)

store_ref_decl = StatementDecl("store_ref", ("ref", "value"), 0)

list_append_decl = StatementDecl("list_append", ("l", "item"), 0)
"""Implements `list.append(l, item)`"""

load_name_decl = StatementDecl("load_name", ("dict", "name", "value"), 1)

store_name_decl = StatementDecl("store_name", ("dict", "name", "value"), 0)

getattr_decl = StatementDecl("getattr", ("value", "name"), 1)

getitem_decl = decl_statement("getitem", {"value": VALUE, "index": INT}, VALUE)

getmethod_decl = StatementDecl("getmethod", ("value", "name"), 2)

make_function_decl = StatementDecl("make_function", ("code"), 1)

jump_check_interrupt = StatementDecl("jump_check_interrupt", ("target",), 0)
"""
Terminal statement with a jump to block.
"""

branch = StatementDecl("branch", ("value", "true_target", "false_target"), 0)
"""
Terminal statement with a branch to one of two labels.

Value must be a bool.
"""

call_decl = StatementDecl("call", ("fn", "obj", "args"), 1)

call_kw_decl = StatementDecl("call", ("fn", "obj", "args", "kw_names"), 1)

compare_decl = StatementDecl("compare", ("op", "coerce", "x", "y"), 1)

in_decl = StatementDecl("in", ("invert", "e", "s"), 1)
"""
Performs `e in s` operation if invert is 0 and `e not in s` operation if invert is 1.
"""

not_decl = StatementDecl("compare", ("op", "coerce", "x", "y"), 1)

format_decl = StatementDecl("format", ("value"), 1)
"""
Implements `value.__format__("")`

Used for format strings.
"""

iter_decl = StatementDecl("iter", ("val",), 1)
"""
Implements `iter(val)`
"""

for_iter_decl = StatementDecl("for_iter", ("iter",), 2)
"""
iter is an iterator.  Call its __next__() method.
If this yields a new value, return (true, new_value).

If the iterator indicates it is exhausted then return (false, None).
"""

return_decl = StatementDecl("return", ("value"), 0)
"""
Return from procedure with value (terminal)
"""

set_function_attribute = StatementDecl("set_function_attribute", ("function", "flag", "value"), 0)
"""
Sets an attribute on a function object using the given value.

The flag determines which attribute to set:

* 0x01 a tuple of default values for positional-only and positional-or-keyword
  parameters in positional order
* 0x02 a dictionary of keyword-only parameters’ default values
* 0x04 a tuple of strings containing parameters’ annotations
* 0x08 a tuple containing cells for free variables, making a closure
"""

store_attr = StatementDecl("store_attr", ("obj", "name", "value"), 0)
"""
Implements `obj.name = value`
"""

binary_op_decl = decl_statement("binary_op", { "op" : STR, "lhs" : VALUE, "rhs" : VALUE}, VALUE)

binary_subscr = StatementDecl("binary_subscr", ("container", "key"), 1)
"""
Implements `container[key]`
"""

store_subscr = StatementDecl("store_subscr", ("container", "key", "value"), 0)
"""
Implements `container[key] = value`
"""

to_bool_decl = StatementDecl("to_bool", ("value",), 1)
"""
Implements `bool(value)`
"""

type Value = ValueBase | None | int

class Statement:
    index : int
    op : StatementDecl
    args : Iterable[Value|JumpTarget|str]

    def __init__(self, index : int, op : StatementDecl, args : Iterable[Value|JumpTarget|str]):
        self.index = index
        self.op = op
        self.args = args

    def __str__(self):
        op = self.op
        result : str
        if op.returnCount > 0:
            result = ', '.join(f'R{self.index + i}' for i in range(op.returnCount))
            result = f'{result} = '
        else:
            result = ''
        return f'{result}@{self.op.name}({', '.join(str(a) for a in self.args)})'

class Block:
    offset : int
    input_count : int|None
    statements : list[Statement]

    def __init__(self, offset : int):
        self.offset = offset
        self.input_count = None
        self.statements = []

global_dict = GlobalNameMap()

class Globals:

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

class Translator:
    globals : Globals
    code : Any

    jump_targets : dict[Offset, int]

    blocks : list[Block]
    """Maps block offsets to the block"""

    next_block_index : int

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

    stack: list[Value]
    """Values in current stack"""

    def __init__(self, globals : Globals, code, block_offsets : list[Offset]):
        assert (isinstance(nm, str) for nm in code.co_varnames)
        assert code.co_nlocals >= code.co_argcount
        assert code.co_nlocals == len(code.co_varnames)

        self.globals = globals
        self.code = code
        self.jump_targets = { offset : idx for (idx, offset) in enumerate(block_offsets) }
        self.blocks = [ Block(offset) for offset in block_offsets ]
        self.stack_heights = {}
        self.cur_block = None
        self.stack = []

        self.register_count = 0

        first_block = self.blocks[0]
        first_block.input_count = code.co_nlocals
        self.cur_block = first_block
        self.next_block_index = 1

        # Initialize list of arguments
        arg_values = (ArgValue(i, code.co_varnames[i]) for i in range(code.co_argcount))
        nonarg_locals = code.co_nlocals - code.co_argcount
        init_local_values = [ *arg_values, *([None] * nonarg_locals) ]
        self.co_vars = [self.mk_ref(v) for v in init_local_values ]

        if code.co_qualname == "<module>":
            assert code.co_nlocals == 0
            self.name_dict = None
            self.names = None
        else:
            self.name_dict = self.add_stmt(mk_dict)
            self.names = set(code.co_varnames)

    def stack_pop(self):
        """ Pop argument off stack"""
        assert len(self.stack) > 0
        return self.stack.pop()

    def stack_push(self, value: Value):
        """ Push argument off stack"""
        return self.stack.append(value)

    def pop_n(self, n : int):
        if n == 0:
            return ()
        else:
            assert 0 < n and n <= len(self.stack)
            val = tuple(self.stack[-n:])
            del self.stack[-n:]
            return val

    def add_stmt(self, stmt : StatementDecl, *args : Value|JumpTarget|str) -> Any:
        base = self.register_count
        self.register_count += stmt.returnCount
        block = self.cur_block
        assert isinstance(block, Block)
        block.statements.append(Statement(base, stmt, args))
        match stmt.returnCount:
            case 0:
                return
            case 1:
                return RegValue(base)
            case rc:
                return tuple(RegValue(i) for i in range(base, base+rc))

    def mk_ref(self, value : Value) -> Value:
        return self.add_stmt(mk_ref_decl, value)

    def load_ref(self, ref : Value):
        return self.add_stmt(load_ref_decl, ref)

    def store_ref(self, ref : Value, value : Value):
        self.add_stmt(store_ref_decl, ref, value)

    def in_block(self) -> bool:
        return self.cur_block is not None

    def end_block(self):
        assert self.cur_block is not None
        self.cur_block = None

    def check_stack_height(self, block: Block, stack_height : int) -> Block:
        """Check stack height matches height if previously recorded."""


        local_count = len(self.co_vars)
        input_count = local_count + stack_height
        if block.input_count is None:
            block.input_count = input_count
        else:
            assert block.input_count == input_count, \
                f'{block.offset} has mismatched input_counts {input_count} and {block.input_count}.'
        return block

    def start_block(self, offset: int):
        block_index = self.jump_targets[offset]
        assert block_index == self.next_block_index
        block = self.blocks[block_index]

        if self.cur_block is not None:
            self.check_stack_height(block, len(self.stack))
            self.end_block()

        assert isinstance(block.input_count, int), f'Block at {offset} has not been reached.'
        assert len(block.statements) == 0
        self.cur_block = block
        self.next_block_index = self.next_block_index + 1
        covar_count = len(self.co_vars)
        self.co_vars = [ BlockArgument(i) for i in range(covar_count)]
        self.stack = [ BlockArgument(i) for i in range(covar_count, block.input_count)]

    def get_jump_target(self, target : int|None) -> JumpTarget:
        assert isinstance(target, int)
        assert target != 0

        block_index = self.jump_targets[target]
        self.check_stack_height(self.blocks[block_index], len(self.stack))
        arguments = [*self.co_vars, *self.stack]
        return JumpTarget(block_index, arguments)

    def fallthrough_target(self):
        arguments = [*self.co_vars, *self.stack]
        block_index = self.next_block_index
        self.check_stack_height(self.blocks[block_index], len(self.stack))
        return JumpTarget(block_index, arguments)

    def add_term_stmt(self, stmt : StatementDecl, *args: Value|JumpTarget):
        self.add_stmt(stmt, *args)
        self.end_block()

    def get_const(self, arg) -> Value:
        assert isinstance(arg, int) and arg >= 0 and arg < len(self.code.co_consts)
        c = self.code.co_consts[arg]
        if c is None:
            return None
        if isinstance(c, int):
            return c
        if isinstance(c, str):
            return StringLit(c)
        if isinstance(c, tuple):
            assert (isinstance(a, str) for a in c)
            return TupleValue(c)
        if isinstance(c, type(self.code)):
            return CodeName(c.co_qualname)
        raise NotImplementedError(f'get_const {type(c)}')

    def get_name(self, arg : int) -> str:
        assert 0 <= arg and arg < len(self.code.co_names), f'Arg {arg} must be less than {len(self.code.co_names)}'
        name = self.code.co_names[arg]
        assert isinstance(name, str)
        return name

    def is_module_init(self):
        is_module_init = self.names is None
        assert is_module_init == (self.name_dict is None)
        return is_module_init

    def load_global(self, name : str):
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

    def BINARY_SUBSCR(self, ins : Instruction):
        assert ins.arg is None
        key = self.stack_pop()
        container = self.stack_pop()
        val = self.add_stmt(binary_subscr, container, key)
        self.stack_push(val)

    def BUILD_CONST_KEY_MAP(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        names = self.stack_pop()
        values = TupleValue(self.pop_n(count))
        val = self.add_stmt(build_const_key_map_decl, names, values)
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
        names = TupleValue([pairs[2*i] for i in range(count)])
        values = TupleValue([pairs[2*i+1] for i in range(count)])
        val = self.add_stmt(build_const_key_map_decl, names, values)
        self.stack_push(val)

    def BUILD_STRING(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        val = StringConcat(self.pop_n(count))
        self.stack_push(val)

    def BUILD_TUPLE(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = TupleValue(self.pop_n(arg))
        self.stack_push(val)

    def CALL(self, ins : Instruction):
        argc = ins.arg
        assert isinstance(argc, int)
        args = TupleValue(list(self.stack_pop() for _ in range(argc)))
        selfObj = self.stack_pop()
        fn = self.stack_pop()
        val = self.add_stmt(call_decl, fn, selfObj, args)
        self.stack_push(val)

    def CALL_KW(self, ins : Instruction):
        argc = ins.arg
        assert isinstance(argc, int)
        selfObj = self.stack_pop()
        fn = self.stack_pop()
        args = TupleValue(list(self.stack_pop() for _ in range(argc)))
        names = self.stack_pop()
        val = self.add_stmt(call_kw_decl, fn, selfObj, args, names)
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
        val = self.add_stmt(in_decl, invert, e, s)
        self.stack_push(val)

    def COPY(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        assert 0 < i
        assert i < len(self.stack)
        self.stack.append(self.stack[-i])

    def END_FOR(self, ins : Instruction):
        assert ins.arg is None
        # N.B. This is supposed to pop the stack, but always seems followed by POP_TOP.
        #self.stack_pop()

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
        self.add_term_stmt(branch, success, true_target, false_target)

    def FORMAT_SIMPLE(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.stack_push(self.add_stmt(format_decl, val))

    def GET_ITER(self, ins : Instruction):
        """Implements STACK[-1] = iter(STACK[-1])."""
        assert ins.arg is None
        val = self.stack_pop()
        val = self.add_stmt(iter_decl, val)
        self.stack_push(val)

    def IMPORT_FROM(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(namei)
        assert len(self.stack) > 0
        module = self.stack[-1]
        val = self.add_stmt(importfrom_decl, module, name)
        self.stack_push(val)

    def IMPORT_NAME(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(namei)
        fromlist = self.stack_pop()
        level = self.stack_pop()
        val = self.add_stmt(import_decl, name, None, None, fromlist, level)
        self.stack_push(val)

    def JUMP_BACKWARD(self, ins : Instruction):
        target = self.get_jump_target(ins.jump_target)
        self.add_stmt(jump_check_interrupt, target)
        self.end_block()

    def LIST_APPEND(self, ins : Instruction):
        i = ins.arg
        assert isinstance(i, int)
        item = self.stack_pop()
        assert i > 0
        list = self.stack[-i]
        self.add_stmt(list_append_decl, list, item)

    def LOAD_ATTR(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.get_name(namei >> 1)
        if namei % 2 == 0:
            val = self.stack_pop()
            val = self.add_stmt(getattr_decl, val, name)
            self.stack_push(val)
        else:
            val = self.stack_pop()
            (method, methodSelf) = self.add_stmt(getmethod_decl, val, name)
            self.stack_push(method)
            self.stack_push(methodSelf)

    def LOAD_BUILD_CLASS(self, _ : Instruction):
        self.stack_push(Builtin("__builtins__.__build_class__"))

    def LOAD_CONST(self, ins : Instruction):
        arg = ins.arg
        val = self.get_const(arg)
        self.stack_push(val)

    def LOAD_FAST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        self.stack_push(self.load_ref(self.co_vars[arg]))

    def LOAD_FAST_AND_CLEAR(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        # Get ref
        ref = self.co_vars[arg]
        # Push value to stack
        self.stack_push(self.load_ref(ref))
        # Clear ref
        self.store_ref(ref, None)

    def LOAD_FAST_LOAD_FAST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        self.stack_push(self.load_ref(self.co_vars[arg >> 4]))
        self.stack_push(self.load_ref(self.co_vars[arg & 15]))

    def LOAD_GLOBAL(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        name = self.get_name(arg>>1)
        val = self.load_global(name)
        if arg&1 == 1:
            self.stack_push(None)
        self.stack_push(val)

    def LOAD_NAME(self, ins : Instruction):
        assert isinstance(ins.arg, int)
        name = self.get_name(ins.arg)
        if self.names is not None and name in self.names:
            val = self.add_stmt(load_name_decl, self.name_dict, name)
        else:
            val = self.load_global(name)
        self.stack_push(val)

    def MAKE_FUNCTION(self, ins : Instruction):
        assert ins.arg is None
        code = self.stack_pop()
        fn = self.add_stmt(make_function_decl, code)
        self.stack_push(fn)

    def NOP(self, ins : Instruction):
        assert ins.arg is None
        pass

    def POP_JUMP_IF_FALSE(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.stack_pop()
        true_target = self.fallthrough_target()
        false_target = self.get_jump_target(ins.jump_target)
        self.add_term_stmt(branch, val, true_target, false_target)

    def POP_JUMP_IF_TRUE(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.stack_pop()
        true_target = self.get_jump_target(ins.jump_target)
        false_target = self.fallthrough_target()
        self.add_term_stmt(branch, val, true_target, false_target)

    def POP_TOP(self, _ : Instruction):
        self.stack_pop()

    def PUSH_NULL(self, ins : Instruction):
        assert ins.arg is None
        self.stack_push(None)

    def RESUME(self, ins : Instruction):
        assert isinstance(ins.arg, int)

    def RETURN_CONST(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.get_const(arg)
        self.add_term_stmt(return_decl, val)

    def RETURN_VALUE(self, ins : Instruction):
        assert ins.arg is None
        val = self.stack_pop()
        self.add_term_stmt(return_decl, val)

    def SET_FUNCTION_ATTRIBUTE(self, ins : Instruction):
        flag = ins.arg
        assert isinstance(flag, int)
        fun = self.stack_pop()
        val = self.stack_pop()
        self.add_stmt(set_function_attribute, fun, flag, val)
        self.stack_push(fun)

    def SETUP_ANNOTATIONS(self, ins : Instruction):
        assert ins.arg is None
        name = "__annotations__"
        if self.names is not None:
            if name not in self.names:
                self.names.add(name)
                self.store(self.name_dict, name, DictValue())
        else:
            if name not in self.globals.globals:
                self.globals.globals.add(name)
                self.store(global_dict, name, DictValue())

    def STORE_ATTR(self, ins : Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.code.co_names[namei]
        obj = self.stack_pop()
        value = self.stack_pop()
        self.add_stmt(store_attr, obj, name, value)

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

    def STORE_NAME(self, ins : Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        name = self.get_name(arg)
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
        self.add_stmt(store_subscr, container, key, value)

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

    def UNPACK_SEQUENCE(self, ins : Instruction):
        count = ins.arg
        assert isinstance(count, int)
        val = self.stack_pop()
        for i in reversed(range(count)):
            self.stack_push(self.add_stmt(getitem_decl, val, i))

def create_block_offsets(insns : list[dis.Instruction]) -> list[int]:
    """Create sorted list of block offsets from list of instructions."""
    block_offsets : set[int] = set()
    next_jump_target : bool = True
    for insn in insns:
        if next_jump_target:
            block_offsets.add(insn.offset)
            next_jump_target = False
        target = insn.jump_target
        if target is not None:
            if target not in block_offsets:
                block_offsets.add(target)
            next_jump_target = True
    assert 0 in block_offsets
    return sorted(block_offsets)

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

def compile_path(path : Path) -> tuple[Any, str]:
    with open(path, 'rb') as r:
        bytes = r.read()
    output = StringIO()
    with RedirectStdStreams(stdout = output, stderr=output):
        c = compile(bytes, mode='exec', filename=path)
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
            (c, _) = compile_path(path)
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

def find_code(globals : Globals, n : int, co):
    codeType = type(co)
    consts = co.co_consts
    assert isinstance(consts, tuple)

    indent0 = '  ' * n
    print(f'{indent0}Constants:')
    indent = indent0 + '  '
    for i, c in enumerate(consts):
        if isinstance(c, codeType):
            print(f'{indent}{i}: code({c.co_qualname})')
        elif isinstance(c, str):
            print(f'{indent}{i}: str({repr(c)})')
        elif isinstance(c, int):
            print(f'{indent}{i}: int({repr(c)})')
        elif isinstance(c, tuple):
            assert (isinstance(v, str) for v in c)
            tp = ','.join([repr(v) for v in c])
            print(f'{indent}{i}: tuple({tp})')
        elif c is None:
            print(f'{indent}{i}: None')
        else:
            print(f'{indent}{i}: {type(c)}')
    insns = list(dis.get_instructions(co))

    print(f'{indent0}Instructions ({len(insns)}):')
    for ins in insns:
        print(f'{indent0}  {ins.offset}: {ins.opname} {ins.arg} ({ins.argval})')

    assert isinstance(co.co_exceptiontable, bytes)
    exception_table = parse_exception_table_entries(co.co_exceptiontable)

    if len(exception_table) > 0:
        print(f"Exception tables aren't yet supported.")
        for entry in exception_table:
            print(f'{entry.pretty_format()}')
        exit(1)
        return

    supported = set(Translator.__dict__.keys())
    incomplete = any(ins.opname not in supported for ins in insns)

    # Set of block from jump target to block index.
    block_offsets = create_block_offsets(insns)
    translator = Translator(globals, co, block_offsets)
    for i, ins in enumerate(insns):
        if ins.offset != 0 and ins.offset in translator.jump_targets:
            translator.start_block(ins.offset)
        elif not translator.in_block():
            continue
        if incomplete:
            print(f'{ins.offset}: {ins.opname} {ins.arg} ({ins.argval}) (stack=[{", ".join(str(s) for s in translator.stack)}])')
        f = getattr(translator, ins.opname, None)
        if f is not None:
            f(ins)
        else:
            exit(1)

    print(f'{indent0}Statements:')
    for (idx, block) in enumerate(translator.blocks):
        assert isinstance(block.input_count, int)
        args = ', '.join([f'B{idx}' for idx in range(block.input_count)])
        print(f'{indent0}  L{idx}({args}):')
        for stmt in block.statements:
            print(f'{indent0}    {stmt}')

    for c in consts:
        if isinstance(c, codeType):
            find_code(globals, n + 1, c)
