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

function List_len(l: ListAny): int
{ if ListAny..isListAny_nil(l) then 0 else 1 + List_len(ListAny..tail!(l)) };

procedure List_len_pos(l: ListAny)
  invokeOn List_len(l)
  opaque
  ensures List_len(l) >= 0;

function List_extend(l1: ListAny, l2: ListAny): ListAny
{ if ListAny..isListAny_nil(l1) then l2 else ListAny_cons(ListAny..head!(l1), List_extend(ListAny..tail!(l1), l2)) };

function List_get_non_neg(l: ListAny, i: int): Any
  requires i >= 0 && i < List_len(l)
{ if ListAny..isListAny_nil(l) then from_None() else if i == 0 then ListAny..head!(l) else List_get_non_neg(ListAny..tail!(l), i - 1) };

function List_get(l: ListAny, i: int): Any
  requires i >= -List_len(l) && i < List_len(l)
{ if i >= 0 then List_get_non_neg(l, i) else List_get_non_neg(l, List_len(l) + i) };

function List_take(l: ListAny, i: int): ListAny
  requires i >= 0 && i <= List_len(l)
{ if ListAny..isListAny_nil(l) then ListAny_nil() else if i == 0 then ListAny_nil() else ListAny_cons(ListAny..head!(l), List_take(ListAny..tail!(l), i - 1)) };

procedure List_take_len(l: ListAny, i: int)
  invokeOn List_len(List_take(l, i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_take(l, i)) == i;

function List_drop(l: ListAny, i: int): ListAny
  requires i >= 0 && i <= List_len(l)
{ if ListAny..isListAny_nil(l) then ListAny_nil() else if i == 0 then l else List_drop(ListAny..tail!(l), i - 1) };

procedure List_drop_len(l: ListAny, i: int)
  invokeOn List_len(List_drop(l, i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_drop(l, i)) == List_len(l) - i;

function DictStrAny_contains(d: DictStrAny, key: string): bool
{ if DictStrAny..isDictStrAny_empty(d) then false else DictStrAny..key!(d) == key || DictStrAny_contains(DictStrAny..tail!(d), key) };

function DictStrAny_get(d: DictStrAny, key: string): Any
  requires DictStrAny_contains(d, key)
{ if DictStrAny..isDictStrAny_empty(d) then from_None() else if DictStrAny..key!(d) == key then DictStrAny..val!(d) else DictStrAny_get(DictStrAny..tail!(d), key) };

function Any_get(dictOrList: Any, index: Any): Any
  requires Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index)) || Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= -List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList))
{ if Any..isfrom_DictStrAny(dictOrList) then DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index)) else List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index)) };

function Any_len(v: Any): int
  opaque;

function Any_len_to_Any(v: Any): Any
{ from_int(Any_len(v)) };

procedure Any_len_pos(v: Any)
  invokeOn Any_len(v)
  opaque
  ensures Any_len(v) >= 0;

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

function PNeg(v: Any): Any
{ if Any..isexception(v) then v else if Any..isfrom_bool(v) then from_int(-bool_to_int(Any..as_bool!(v))) else if Any..isfrom_int(v) then from_int(-Any..as_int!(v)) else if Any..isfrom_float(v) then from_float(-Any..as_float!(v)) else exception(UndefinedError("Operand Type is not defined")) };

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

procedure linear_search($in_xs: (Core Any), $in_target: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_xs)( summary "(linear_search requires) Type constraint of xs")
  requires Any..isfrom_int($in_target)( summary "(linear_search requires) Type constraint of target")
  opaque
  ensures Any..isfrom_int(LaurelResult)( summary "(linear_search ensures) Return type constraint")
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var xs: (Core Any) := $in_xs; var target: (Core Any) := $in_target; var maybe_except: (Core Error) := NoError(); var i: (Core Any) := <?>; var n: (Core Any) := <?>; i := from_int(0); assert Any..isfrom_int(i); n := Any_len_to_Any(xs); assert Any..isfrom_int(n); assert !Any..isexception(PLt(i, n)) summary "Check PLt exception"; { while(Any_to_bool(PLt(i, n))) { if Any_to_bool(PEq(Any_get(xs, i), target)) then { LaurelResult := i; exit $body }; assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception"; i := PAdd(i, from_int(1)) }loop_continue_125 }loop_break_125; assert !Any..isexception(PNeg(from_int(1))) summary "Check PNeg exception"; LaurelResult := PNeg(from_int(1)); exit $body };

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var maybe_except: (Core Error) := NoError(); var xs: (Core Any) := <?>; var found: (Core Any) := <?>; var missing: (Core Any) := <?>; xs := from_ListAny(ListAny_cons(from_int(10), ListAny_cons(from_int(20), ListAny_cons(from_int(30), ListAny_cons(from_int(40), ListAny_cons(from_int(50), ListAny_nil())))))); found := linear_search(xs, from_int(30)); assert Any..isfrom_int(found); assert Any_to_bool(PEq(found, from_int(2))) summary "30 is at index 2"; missing := linear_search(xs, from_int(99)); assert Any..isfrom_int(missing); assert !Any..isexception(PNeg(from_int(1))) summary "Check PNeg exception"; assert Any_to_bool(PEq(missing, PNeg(from_int(1)))) summary "99 is not present" };

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
