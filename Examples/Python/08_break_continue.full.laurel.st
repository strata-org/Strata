datatype LaurelResolutionErrorPlaceholder {  }

datatype Float64IsNotSupportedYet {  }

datatype Error { NoError, TypeError(Type_msg: string), AttributeError(Attribute_msg: string), AssertionError(Assertion_msg: string), UnimplementedError(Unimplement_msg: string), UndefinedError(Undefined_msg: string), IndexError(IndexError_msg: string), RePatternError(Re_msg: string) }

datatype OptionInt { OptSome(unwrap: int), OptNone }

datatype Any { from_None, from_bool(as_bool: bool), from_int(as_int: int), from_float(as_float: real), from_str(as_string: string), from_datetime(as_datetime: int), from_bytes(as_bytes: string), from_DictStrAny(as_Dict: DictStrAny), from_ListAny(as_ListAny: ListAny), from_ClassInstance(classname: string, instance_attributes: DictStrAny), from_Slice(start: int, stop: OptionInt), exception(get_error: Error) }

datatype ListAny { ListAny_nil, ListAny_cons(head: Any, tail: ListAny) }

datatype DictStrAny { DictStrAny_empty, DictStrAny_cons(key: string, val: Any, tail: DictStrAny) }

composite PythonError { response: (Core Any) }

function select(map: int, key: int): intexternal;

function update(map: int, key: int, value: int): intexternal;

function const(value: int): intexternal;

function Any_to_bool(v: Any): bool
{ if Any..isfrom_bool(v) then Any..as_bool!(v) else if Any..isfrom_None(v) then false else if Any..isfrom_str(v) then !(Any..as_string!(v) == "") else if Any..isfrom_int(v) then !(Any..as_int!(v) == 0) else if Any..isfrom_float(v) then !(Any..as_float!(v) == 0.0) else if Any..isfrom_DictStrAny(v) then !(Any..as_Dict!(v) == DictStrAny_empty()) else if Any..isfrom_ListAny(v) then !(Any..as_ListAny!(v) == ListAny_nil()) else <?> };

function List_extend(l1: ListAny, l2: ListAny): ListAny
{ if ListAny..isListAny_nil(l1) then l2 else ListAny_cons(ListAny..head!(l1), List_extend(ListAny..tail!(l1), l2)) };

function is_IntReal(v: Any): bool
  opaque;

function Any_real_to_int(v: Any): int
  opaque;

function normalize_any(v: Any): Any
{ if v == from_bool(true) then from_int(1) else if v == from_bool(false) then from_int(0) else if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else v };

function int_to_real(i: int): real
  opaque;

function bool_to_int(bval: bool): int
{ if bval then 1 else 0 };

function bool_to_real(b: bool): real
{ if b then 1.0 else 0.0 };

function Str.Concat(s: string, s2: string): stringexternal;

function PAdd(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_int(bool_to_int(Any..as_bool!(v1)) + bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_int(bool_to_int(Any..as_bool!(v1)) + Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_int(Any..as_int!(v1) + bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then from_float(int_to_real(Any..as_int!(v1)) + Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then from_float(Any..as_float!(v1) + bool_to_real(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_int(Any..as_int!(v1) + Any..as_int!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then from_float(Any..as_float!(v1) + int_to_real(Any..as_int!(v2))) else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then from_float(Any..as_float!(v1) + Any..as_float!(v2)) else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then from_str(Str.Concat(Any..as_string!(v1), Any..as_string!(v2))) else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then from_ListAny(List_extend(Any..as_ListAny!(v1), Any..as_ListAny!(v2))) else if Any..isfrom_datetime(v1) && Any..isfrom_int(v2) then from_datetime(Any..as_datetime!(v1) + Any..as_int!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function string_lt(s1: string, s2: string): bool
  opaque;

function List_lt(l1: ListAny, l2: ListAny): bool
  opaque;

function PLt(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) < bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) < Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_int!(v1) < bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then from_bool(bool_to_real(Any..as_bool!(v1)) < Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_float!(v1) < bool_to_real(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_bool(Any..as_int!(v1) < Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then from_bool(int_to_real(Any..as_int!(v1)) < Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then from_bool(Any..as_float!(v1) < int_to_real(Any..as_int!(v2))) else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then from_bool(Any..as_float!(v1) < Any..as_float!(v2)) else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then from_bool(string_lt(Any..as_string!(v1), Any..as_string!(v2))) else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then from_bool(List_lt(Any..as_ListAny!(v1), Any..as_ListAny!(v2))) else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then from_bool(Any..as_datetime!(v1) < Any..as_datetime!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function PEq(v: Any, |v'|: Any): Any
{ from_bool(normalize_any(v) == normalize_any(|v'|)) };

function to_string(a: Any): string
  opaque;

function to_string_any(a: Any): Any
{ from_str(to_string(a)) };

function datetime_strptime(dtstring: Any, format: Any): Any
  opaque;

procedure datetime_tostring_cancel(dt: Any)
  invokeOn datetime_strptime(to_string_any(dt), from_str("%Y-%m-%d"))
  opaque
  ensures datetime_strptime(to_string_any(dt), from_str("%Y-%m-%d")) == dt;

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var maybe_except: (Core Error) := NoError(); var i: (Core Any) := <?>; var seen: (Core Any) := <?>; i := from_int(0); assert Any..isfrom_int(i); seen := from_int(0); assert Any..isfrom_int(seen); assert !Any..isexception(PLt(i, from_int(10))) summary "Check PLt exception"; { while(Any_to_bool(PLt(i, from_int(10)))) { assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception"; i := PAdd(i, from_int(1)); if Any_to_bool(PEq(i, from_int(3))) then { exit loop_continue_55 }; if Any_to_bool(PEq(i, from_int(6))) then { exit loop_break_55 }; assert !Any..isexception(PAdd(seen, from_int(1))) summary "Check PAdd exception"; seen := PAdd(seen, from_int(1)) }loop_continue_55 }loop_break_55; assert Any_to_bool(PEq(seen, from_int(4))) summary "should have counted 1,2,4,5" };

procedure $composite_to_string_PythonError(self: PythonError): string
  opaque
  modifies *;

procedure $composite_to_string_any_PythonError(self: PythonError): (Core Any)
  opaque
  modifies *;

procedure __main__()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var maybe_except: (Core Error) := NoError(); var __name__: (Core Any) := <?>; __name__ := from_str("__main__") };
