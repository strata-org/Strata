# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

#!/usr/bin/env python3

"""
Command line script for exporting Python dialect and program to files.
"""

import argparse
import os
import amazon.ion.simpleion as ion
from dataclasses import dataclass
from strata import Dialect
from strata import python as stratap
import sys
from strata.pythond import InstructionMap, PythonD
from pathlib import Path
from typing import Any, Iterable

import ast
import dis

def write_dialect(dialect : Dialect, dir : Path):
    if not dir.is_dir():
        print(f"Directory {dir} does not exist.", file=sys.stderr)
        exit(1)
    output = dir / f"{dialect.name}.dialect.st.ion"
    with output.open('wb') as w:
        ion.dump(dialect.to_ion(), w, binary=True)
    print(f"Wrote {dialect.name} dialect to {output}")


def gen_dialect_imp(args):
    write_dialect(stratap.Python, Path(args.output_dir))

def parse_python_imp(args):
    path = args.python
    with open(path, 'rb') as r:
        try:
            (_, p) = stratap.parse_module(r.read(), path)
        except SyntaxError as e:
            print(f"Error parsing {path}:\n  {e}", file=sys.stderr)
            exit(1)
    with open(args.output, 'wb') as w:
        ion.dump(p.to_ion(), w, binary=True)

def gen_pythond_dialect_imp(args):
    write_dialect(PythonD, Path(args.output_dir))

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

@dataclass
class JumpTarget(ValueBase):
    label : int

    def __str__(self):
        return f'L{self.label}'

class StatementDecl:
    name : str
    args : Iterable[str]
    returnCount : int

    def __init__(self, name : str, args : Iterable[str], returnCount : int):
        self.name = name
        self.args = args
        self.returnCount = returnCount

import_decl = StatementDecl("import", ("name", "globals", "locals", "fromlist", "level"), 1)

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

getattrDecl = StatementDecl("getattr", ("value", "name"), 1)

getmethodDecl = StatementDecl("getmethod", ("value", "name"), 2)

make_function_decl = StatementDecl("make_function", ("code"), 1)

jump_check_interupt = StatementDecl("jump_check_interupt", ("target",), 0)
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

binary_subscr = StatementDecl("binary_subscr", ("container", "key"), 1)
"""
Implements `container[key]`
"""

store_subscr = StatementDecl("store_subscr", ("container", "key", "value"), 0)
"""
Implements `container[key] = value`
"""

type Value = ValueBase | None | int

class Statement:
    index : int
    op : StatementDecl
    args : Iterable[Value|str]

    def __init__(self, index : int, op : StatementDecl, args : Iterable[Value|str]):
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
    statements : list[Statement]

    def __init__(self, offset : int, statements : list[Statement]):
        self.statements = statements

class Globals:
    builtins : dict[str, Value]

    dict_value : Value
    globals : set[str]

    def __init__(self):
        self.builtins = {}
        self.add_builtin("__name__", "getattr", "str")
        self.add_builtin("__builtins__.__build_class__")
#        self.add_builtin("__annotations__")
        self.dict_value = GlobalNameMap()
        self.globals = set()

    def add_builtin(self, *args : str):
        assert (name not in self.builtins for name in args)
        for name in args:
            self.builtins[name] = Builtin(name)

    def find_name(self, name : str) -> Value:
        if name in self.builtins:
            return self.builtins[name]
        raise RuntimeError(f'Unknown name {name}')

type Offset = int

class Spec:
    globals : Globals
    code : Any

    jump_targets : dict[int, JumpTarget]

    blocks : dict[Offset, Block]
    """Maps block offsets to the block"""
    stack_heights : dict[Offset, int]
    """Maps block offsets to the expected stack height of block"""

    cur_block : Block|None
    """Current block to add code to"""

    locals : int
    """Number of local variables added so far."""

    name_dict : Value
    """Dictionary to write local updates to"""
    names : set[str]|None
    stack: list[Value]

    def __init__(self, globals : Globals, code, block_offsets : list[Offset]):
        self.globals = globals
        self.code = code
        self.jump_targets = { off : JumpTarget(idx) for (idx, off) in enumerate(block_offsets) }
        self.blocks = {}
        self.stack_heights = {}
        self.cur_block = None
        self.stack = []

        self.start_block(0)
        self.locals = 0
        assert (isinstance(nm, str) for nm in code.co_varnames)
        assert code.co_nlocals >= code.co_argcount
        assert code.co_nlocals == len(code.co_varnames)
        arg_values = (ArgValue(i, code.co_varnames[i]) for i in range(code.co_argcount))
        # Initialize list of arguments
        nonarg_locals = code.co_nlocals - code.co_argcount
        init_local_values = [ *arg_values, *([None] * nonarg_locals) ]
        self.co_vars = [self.mk_ref(v) for v in init_local_values ]

        if code.co_qualname == "<module>":
            assert code.co_nlocals == 0
            self.name_dict = None
            self.names = None
        else:
            self.name_dict = self.add_stmt(mk_dict, [])
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

    def add_stmt(self, stmt : StatementDecl, args : Iterable[Value|str]) -> Any:
        base = self.locals
        self.locals += stmt.returnCount
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
        return self.add_stmt(mk_ref_decl, (value, ))

    def load_ref(self, ref : Value):
        return self.add_stmt(load_ref_decl, (ref,))

    def store_ref(self, ref : Value, value : Value):
        self.add_stmt(store_ref_decl, (ref, value))

    def get_jump_target(self, target : int|None, expected_stack_height : int) -> JumpTarget:
        assert isinstance(target, int)
        assert target in self.jump_targets
        self.check_stack_height(target, expected_stack_height)
        tgt = self.jump_targets[target]
        return tgt

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
            return self.add_stmt(load_name_decl, [self.globals.dict_value, name])
        return self.globals.find_name(name)

    def store(self, dict : Value, name : str, val : Value):
        self.add_stmt(store_name_decl, (dict, name, val))

    def check_stack_height(self, offset : Offset, height : int):
        """Check stack height matches height if previously recorded."""
        expected = self.stack_heights.get(offset, None)
        if expected is None:
            self.stack_heights[offset] = height
        else:
            assert expected == height

    def in_block(self) -> bool:
        return self.cur_block is not None

    def start_block(self, offset: int):
        if self.cur_block is not None:
            self.end_block()
        assert offset not in self.blocks
        self.check_stack_height(offset, len(self.stack))
        b = Block(offset, [])
        self.blocks[offset] = b
        self.cur_block = b

    def end_block(self):
        assert self.cur_block is not None
        self.cur_block = None

    def BINARY_SUBSCR(self, ins : dis.Instruction):
        assert ins.arg is None
        key = self.stack_pop()
        container = self.stack_pop()
        val = self.add_stmt(binary_subscr, (container, key))
        self.stack_push(val)

    def BUILD_CONST_KEY_MAP(self, ins : dis.Instruction):
        count = ins.arg
        assert isinstance(count, int)
        names = self.stack_pop()
        values = TupleValue(self.pop_n(count))
        val = self.add_stmt(build_const_key_map_decl, (names, values))
        self.stack_push(val)

    def BUILD_LIST(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = ListValue(self.pop_n(arg))
        self.stack_push(val)

    def BUILD_MAP(self, ins : dis.Instruction):
        count = ins.arg
        assert isinstance(count, int)
        names = self.stack_pop()
        pairs = self.pop_n(2 * count)
        names = TupleValue([pairs[2*i] for i in range(count)])
        values = TupleValue([pairs[2*i+1] for i in range(count)])
        val = self.add_stmt(build_const_key_map_decl, (names, values))
        self.stack_push(val)

    def BUILD_TUPLE(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = TupleValue(self.pop_n(arg))
        self.stack_push(val)

    def CALL(self, ins : dis.Instruction):
        argc = ins.arg
        assert isinstance(argc, int)
        args = TupleValue(list(self.stack_pop() for _ in range(argc)))
        selfObj = self.stack_pop()
        fn = self.stack_pop()
        val = self.add_stmt(call_decl, (fn, selfObj, args))
        self.stack_push(val)

    def CALL_KW(self, ins : dis.Instruction):
        argc = ins.arg
        assert isinstance(argc, int)
        selfObj = self.stack_pop()
        fn = self.stack_pop()
        args = TupleValue(list(self.stack_pop() for _ in range(argc)))
        names = self.stack_pop()
        val = self.add_stmt(call_kw_decl, (fn, selfObj, args, names))
        self.stack_push(val)

    def COMPARE_OP(self, ins : dis.Instruction):
        opname = ins.arg
        assert isinstance(opname, int)
        op_idx = opname >> 5
        assert 0 <= op_idx and op_idx < len(dis.cmp_op)
        coerce = (opname & 16) != 0
        x = self.stack_pop()
        y = self.stack_pop()
        val = self.add_stmt(compare_decl, (dis.cmp_op[op_idx], coerce, x, y))
        self.stack_push(val)

    def CONTAINS_OP(self, ins : dis.Instruction):
        invert = ins.arg
        assert invert in [0, 1]
        e = self.stack_pop()
        s = self.stack_pop()
        val = self.add_stmt(in_decl, (invert, e, s))
        self.stack_push(val)

    def END_FOR(self, ins : dis.Instruction):
        assert ins.arg is None
        # N.B. This is supposed to pop the stack, but always seems followed by POP_TOP.
        #self.stack_pop()

    def FOR_ITER(self, ins : dis.Instruction):
        """Implements STACK[-1] = iter(STACK[-1])."""
        delta = ins.arg
        assert isinstance(delta, int)
        assert len(self.stack) > 0
        iter = self.stack[-1]
        (success, val) = self.add_stmt(for_iter_decl, (iter,))

        true_target = JumpTarget(len(self.blocks))
        false_target_offset = ins.jump_target
        false_target = self.get_jump_target(false_target_offset, len(self.stack))
        # Stack will reflect true height
        self.add_stmt(branch, (success, true_target, false_target))
        self.end_block()
        self.stack_push(val)

    def GET_ITER(self, ins : dis.Instruction):
        """Implements STACK[-1] = iter(STACK[-1])."""
        assert ins.arg is None
        val = self.stack_pop()
        val = self.add_stmt(iter_decl, (val,))
        self.stack_push(val)

    def IMPORT_NAME(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        fromlist = self.stack_pop()
        level = self.stack_pop()
        name = self.get_name(arg)
        val = self.add_stmt(import_decl, [name, None, None, fromlist, level])
        self.stack_push(val)

    def JUMP_BACKWARD(self, ins : dis.Instruction):
        target = self.get_jump_target(ins.jump_target, len(self.stack))
        self.add_stmt(jump_check_interupt, (target,))
        self.end_block()

    def LIST_APPEND(self, ins : dis.Instruction):
        i = ins.arg
        assert isinstance(i, int)
        item = self.stack_pop()
        assert i > 0
        list = self.stack[-i]
        self.add_stmt(list_append_decl, (list, item))

    def LOAD_ATTR(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        if arg % 2 == 0:
            name = self.get_name(arg >> 1)
            val = self.stack_pop()
            val = self.add_stmt(getattrDecl, (val, name))
            self.stack_push(val)
        else:
            name = self.get_name(arg >> 1)
            val = self.stack_pop()
            (method, methodSelf) = self.add_stmt(getmethodDecl, (val, name))
            self.stack_push(method)
            self.stack_push(methodSelf)

    def LOAD_BUILD_CLASS(self, _ : dis.Instruction):
        self.stack_push(Builtin("__builtins__.__build_class__"))

    def LOAD_CONST(self, ins : dis.Instruction):
        arg = ins.arg
        val = self.get_const(arg)
        self.stack_push(val)

    def LOAD_FAST(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.load_ref(self.co_vars[arg])
        self.stack_push(val)

    def LOAD_FAST_AND_CLEAR(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        # Get ref
        ref = self.co_vars[arg]
        # Push value to stack
        self.stack_push(self.load_ref(ref))
        # Clear ref
        self.store_ref(ref, None)

    def LOAD_GLOBAL(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        name = self.get_name(arg>>1)
        val = self.load_global(name)
        if arg&1 == 1:
            self.stack_push(None)
        self.stack_push(val)

    def LOAD_NAME(self, ins : dis.Instruction):
        assert isinstance(ins.arg, int)
        name = self.get_name(ins.arg)
        if self.names is not None and name in self.names:
            val = self.add_stmt(load_name_decl, [self.name_dict, name])
        else:
            val = self.load_global(name)
        self.stack_push(val)

    def MAKE_FUNCTION(self, ins : dis.Instruction):
        assert ins.arg is None
        code = self.stack_pop()
        fn = self.add_stmt(make_function_decl, [code])
        self.stack_push(fn)

    def POP_JUMP_IF_FALSE(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.stack_pop()
        true_target = JumpTarget(len(self.blocks))
        false_target_offset = ins.jump_target
        false_target = self.get_jump_target(false_target_offset, len(self.stack))
        self.add_stmt(branch, [val, true_target, false_target])

    def POP_JUMP_IF_TRUE(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.stack_pop()
        false_target = JumpTarget(len(self.blocks))
        true_target_offset = ins.jump_target
        true_target = self.get_jump_target(true_target_offset, len(self.stack))
        self.add_stmt(branch, [val, true_target, false_target])

    def POP_TOP(self, _ : dis.Instruction):
        self.stack_pop()

    def PUSH_NULL(self, ins : dis.Instruction):
        assert ins.arg is None
        self.stack_push(None)

    def RESUME(self, ins : dis.Instruction):
        assert isinstance(ins.arg, int)

    def RETURN_CONST(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.get_const(arg)
        self.add_stmt(return_decl, [val])
        self.end_block()

    def RETURN_VALUE(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        val = self.get_const(arg)
        self.add_stmt(return_decl, [val])
        self.end_block()

    def SET_FUNCTION_ATTRIBUTE(self, ins : dis.Instruction):
        flag = ins.arg
        assert isinstance(flag, int)
        fun = self.stack_pop()
        val = self.stack_pop()
        self.add_stmt(set_function_attribute, (fun, flag, val))
        self.stack_push(fun)

    def SETUP_ANNOTATIONS(self, ins : dis.Instruction):
        assert ins.arg is None
        name = "__annotations__"
        if self.names is not None:
            if name not in self.names:
                self.names.add(name)
                self.store(self.name_dict, name, DictValue())
        else:
            if name not in self.globals.globals:
                self.globals.globals.add(name)
                self.store(self.globals.dict_value, name, DictValue())

    def STORE_ATTR(self, ins : dis.Instruction):
        namei = ins.arg
        assert isinstance(namei, int)
        name = self.code.co_names[namei]
        obj = self.stack_pop()
        value = self.stack_pop()
        self.add_stmt(store_attr, (obj, name, value))

    def STORE_FAST(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        ref = self.co_vars[arg]
        val = self.stack_pop()
        self.store_ref(ref, val)

    def STORE_FAST_LOAD_FAST(self, ins : dis.Instruction):
        var_nums = ins.arg
        assert isinstance(var_nums, int)
        store_index = var_nums >> 4
        load_index = var_nums  & 15
        store_val = self.stack_pop()
        self.store_ref(self.co_vars[store_index], store_val)
        load_val = self.load_ref(self.co_vars[load_index])
        self.stack_push(load_val)

    def STORE_NAME(self, ins : dis.Instruction):
        arg = ins.arg
        assert isinstance(arg, int)
        name = self.get_name(arg)
        val = self.stack_pop()
        if self.names is None:
            self.globals.globals.add(name)
            self.store(self.globals.dict_value, name, val)
        else:
            self.names.add(name)
            self.store(self.name_dict, name, val)

    def STORE_SUBSCR(self, ins : dis.Instruction):
        key = self.stack_pop()
        container = self.stack_pop()
        value = self.stack_pop()
        self.add_stmt(store_subscr, (container, key, value))

    def SWAP(self, ins : dis.Instruction):
        i = ins.arg
        assert isinstance(i, int)
        stack = self.stack
        assert 1 < i and i <= len(stack), f'Swap {i} with length {len(stack)}'
        (stack[-i], stack[-1]) = (stack[-1], stack[-i])

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


missing = set()

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

    # Set of block from jump target to block index.
    block_offsets = create_block_offsets(insns)
    print(f"block_offsets: {block_offsets}")
    spec = Spec(globals, co, block_offsets)
    for i, ins in enumerate(insns):
        if ins.offset != 0 and ins.offset in spec.jump_targets:
            spec.start_block(ins.offset)
        elif not spec.in_block():
            continue
        f = getattr(spec, ins.opname, None)
        if f is not None:
            f(ins)
        else:
            print(f'{indent0}  {ins.offset}: {ins.opname} {ins.arg} ({ins.argval}) (stack=[{", ".join(str(s) for s in spec.stack)}])')
            missing.add(ins.opname)

    print(f'{indent0}Statements:')
    for (idx, block) in enumerate(spec.blocks.values()):
        print(f'{indent0}  L{idx}:')
        for stmt in block.statements:
            print(f'{indent0}    {stmt}')

    for c in consts:
        if isinstance(c, codeType):
            find_code(globals, n + 1, c)


def print_insn_info():
    """
    Prints out dis instruction information including the opcode.
    """
    m = InstructionMap()
    min_instrumentedcode : int = 236
    count = 0
    for i in range(min(len(m.idxmap), min_instrumentedcode)):
        d = m.idxmap[i]
        if d is None:
            continue
        count = count + 1
        print(f'{i}: {d.name} {d.hasarg}')
    print(f'Total: {count}')

def print_ast(bytes, path):
    a = ast.parse(bytes, mode='exec', filename=path)
    print(ast.dump(a, indent=2))

def print_supported_stata():
    """Analyzes dis.opmap to print supported operations."""
    names = Spec.__dict__
    total = 0
    supported = 0
    for (op, idx) in dis.opmap.items():
        if idx > 119:
            continue
        total = total + 1
        if op in names:
            supported = supported + 1
        print(f'{op}: {op in names}')
    print(f"Supports {supported} of {total} operations")

def dis_python_imp(args):
    path = args.python
    with open(path, 'r') as r:
        try:
            bytes = r.read()
        except SyntaxError as e:
            raise e

    c = compile(bytes, mode='exec', filename=path)

    print(f'Root: {c.co_qualname}')
    globals = Globals()
    find_code(globals, 0, c)
    for m in missing:
        print(f'Missing: {m}')

def main():
    parser = argparse.ArgumentParser(
                    prog='strata_python',
                    description='Strata interface to Python parser')
    subparsers = parser.add_subparsers(help="subcommand help")

    gen_dialect_command = subparsers.add_parser('dialect', help='Create Strata dialect.')
    gen_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    gen_dialect_command.set_defaults(func=gen_dialect_imp)

    parse_command = subparsers.add_parser('parse', help='Parse a Python file')
    parse_command.add_argument('python', help='Path of file to read.')
    parse_command.add_argument('output', help='Path to write Strata')
    parse_command.set_defaults(func=parse_python_imp)

    gend_dialect_command = subparsers.add_parser('pythond', help='Create Strata PythonD dialect.')
    gend_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to.')
    gend_dialect_command.set_defaults(func=gen_pythond_dialect_imp)

    dis_command = subparsers.add_parser('dis', help='Disassemble a Python file')
    dis_command.add_argument('python', help='Path of Python file to translate.')
    dis_command.set_defaults(func=dis_python_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()
