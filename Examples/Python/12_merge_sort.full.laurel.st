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

function int_max(i1: int, i2: int): int
{ if i1 >= i2 then i1 else i2 };

function int_min(i1: int, i2: int): int
{ if i1 <= i2 then i1 else i2 };

function List_slice_non_neg(l: ListAny, start: int, stop: int): ListAny
  requires start >= 0 && stop >= 0
{ if start >= List_len(l) || start >= stop then ListAny_nil() else List_take(List_drop(l, start), int_min(stop, List_len(l)) - start) };

function List_slice(l: ListAny, start: int, stop: int): ListAny
{ List_slice_non_neg(l, if start >= 0 then start else int_max(List_len(l) + start, 0), if stop >= 0 then stop else int_max(List_len(l) + stop, 0)) };

function DictStrAny_contains(d: DictStrAny, key: string): bool
{ if DictStrAny..isDictStrAny_empty(d) then false else DictStrAny..key!(d) == key || DictStrAny_contains(DictStrAny..tail!(d), key) };

function DictStrAny_get(d: DictStrAny, key: string): Any
  requires DictStrAny_contains(d, key)
{ if DictStrAny..isDictStrAny_empty(d) then from_None() else if DictStrAny..key!(d) == key then DictStrAny..val!(d) else DictStrAny_get(DictStrAny..tail!(d), key) };

function Any_get(dictOrList: Any, index: Any): Any
  requires Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index)) || Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= -List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList))
{ if Any..isfrom_DictStrAny(dictOrList) then DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index)) else List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index)) };

function Any_get_slice(list: Any, index: Any): Any
  requires Any..isfrom_ListAny(list) && Any..isfrom_Slice(index)
{ from_ListAny(List_slice(Any..as_ListAny!(list), Any..start!(index), if OptionInt..isOptSome(Any..stop!(index)) then OptionInt..unwrap!(Any..stop!(index)) else List_len(Any..as_ListAny!(list)))) };

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

function Str.Concat(s: string, s2: string): stringexternal;

function PAdd(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_int(bool_to_int(Any..as_bool!(v1)) + bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_int(bool_to_int(Any..as_bool!(v1)) + Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_int(Any..as_int!(v1) + bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then from_float(int_to_real(Any..as_int!(v1)) + Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then from_float(Any..as_float!(v1) + bool_to_real(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_int(Any..as_int!(v1) + Any..as_int!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then from_float(Any..as_float!(v1) + int_to_real(Any..as_int!(v2))) else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then from_float(Any..as_float!(v1) + Any..as_float!(v2)) else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then from_str(Str.Concat(Any..as_string!(v1), Any..as_string!(v2))) else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then from_ListAny(List_extend(Any..as_ListAny!(v1), Any..as_ListAny!(v2))) else if Any..isfrom_datetime(v1) && Any..isfrom_int(v2) then from_datetime(Any..as_datetime!(v1) + Any..as_int!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function PFloorDiv(v1: Any, v2: Any): Any
  requires (Any..isfrom_bool(v2) ==> Any..as_bool!(v2)) && (Any..isfrom_int(v2) ==> Any..as_int!(v2) != 0)
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_int(bool_to_int(Any..as_bool!(v1)) / bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_int(bool_to_int(Any..as_bool!(v1)) / Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_int(Any..as_int!(v1) / bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_int(Any..as_int!(v1) / Any..as_int!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function string_lt(s1: string, s2: string): bool
  opaque;

function string_le(s1: string, s2: string): bool
  opaque;

function List_lt(l1: ListAny, l2: ListAny): bool
  opaque;

function List_le(l1: ListAny, l2: ListAny): bool
  opaque;

function PLt(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) < bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) < Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_int!(v1) < bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then from_bool(bool_to_real(Any..as_bool!(v1)) < Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_float!(v1) < bool_to_real(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_bool(Any..as_int!(v1) < Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then from_bool(int_to_real(Any..as_int!(v1)) < Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then from_bool(Any..as_float!(v1) < int_to_real(Any..as_int!(v2))) else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then from_bool(Any..as_float!(v1) < Any..as_float!(v2)) else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then from_bool(string_lt(Any..as_string!(v1), Any..as_string!(v2))) else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then from_bool(List_lt(Any..as_ListAny!(v1), Any..as_ListAny!(v2))) else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then from_bool(Any..as_datetime!(v1) < Any..as_datetime!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function PLe(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2 else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) <= bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then from_bool(bool_to_int(Any..as_bool!(v1)) <= Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_int!(v1) <= bool_to_int(Any..as_bool!(v2))) else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then from_bool(bool_to_real(Any..as_bool!(v1)) <= Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then from_bool(Any..as_float!(v1) <= bool_to_real(Any..as_bool!(v2))) else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then from_bool(Any..as_int!(v1) <= Any..as_int!(v2)) else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then from_bool(int_to_real(Any..as_int!(v1)) <= Any..as_float!(v2)) else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then from_bool(Any..as_float!(v1) <= int_to_real(Any..as_int!(v2))) else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then from_bool(Any..as_float!(v1) <= Any..as_float!(v2)) else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then from_bool(string_le(Any..as_string!(v1), Any..as_string!(v2))) else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then from_bool(List_le(Any..as_ListAny!(v1), Any..as_ListAny!(v2))) else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then from_bool(Any..as_datetime!(v1) <= Any..as_datetime!(v2)) else exception(UndefinedError("Operand Type is not defined")) };

function PEq(v: Any, |v'|: Any): Any
{ from_bool(normalize_any(v) == normalize_any(|v'|)) };

function PAnd(v1: Any, v2: Any): Any
{ if Any..isexception(v1) then v1 else if !Any_to_bool(v1) then v1 else v2 };

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

procedure merge($in_left: (Core Any), $in_right: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_left)( summary "(merge requires) Type constraint of left")
  requires Any..isfrom_ListAny($in_right)( summary "(merge requires) Type constraint of right")
  opaque
  ensures Any..isfrom_ListAny(LaurelResult)( summary "(merge ensures) Return type constraint")
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var left: (Core Any) := $in_left; var right: (Core Any) := $in_right; var maybe_except: (Core Error) := NoError(); var out: (Core Any) := <?>; var i: (Core Any) := <?>; var j: (Core Any) := <?>; out := from_ListAny(ListAny_nil()); i := from_int(0); assert Any..isfrom_int(i); j := from_int(0); assert Any..isfrom_int(j); assert !Any..isexception(PAnd(PLt(i, Any_len_to_Any(left)), PLt(j, Any_len_to_Any(right)))) summary "Check PAnd exception"; { while(Any_to_bool(PAnd(PLt(i, Any_len_to_Any(left)), PLt(j, Any_len_to_Any(right))))) { assert !Any..isexception(PLe(Any_get(left, i), Any_get(right, j))) summary "Check PLe exception"; if Any_to_bool(PLe(Any_get(left, i), Any_get(right, j))) then { assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())))) summary "Check PAdd exception"; out := PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil()))); assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception"; i := PAdd(i, from_int(1)) } else { assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())))) summary "Check PAdd exception"; out := PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil()))); assert !Any..isexception(PAdd(j, from_int(1))) summary "Check PAdd exception"; j := PAdd(j, from_int(1)) } }loop_continue_148 }loop_break_148; assert !Any..isexception(PLt(i, Any_len_to_Any(left))) summary "Check PLt exception"; { while(Any_to_bool(PLt(i, Any_len_to_Any(left)))) { assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())))) summary "Check PAdd exception"; out := PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil()))); assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception"; i := PAdd(i, from_int(1)) }loop_continue_351 }loop_break_351; assert !Any..isexception(PLt(j, Any_len_to_Any(right))) summary "Check PLt exception"; { while(Any_to_bool(PLt(j, Any_len_to_Any(right)))) { assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())))) summary "Check PAdd exception"; out := PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil()))); assert !Any..isexception(PAdd(j, from_int(1))) summary "Check PAdd exception"; j := PAdd(j, from_int(1)) }loop_continue_424 }loop_break_424; LaurelResult := out; exit $body };

procedure merge_sort($in_xs: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_xs)( summary "(merge_sort requires) Type constraint of xs")
  opaque
  ensures Any..isfrom_ListAny(LaurelResult)( summary "(merge_sort ensures) Return type constraint")
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var xs: (Core Any) := $in_xs; var maybe_except: (Core Error) := NoError(); var n: (Core Any) := <?>; var mid: (Core Any) := <?>; var left: (Core Any) := <?>; var right: (Core Any) := <?>; n := Any_len_to_Any(xs); assert Any..isfrom_int(n); assert !Any..isexception(PLe(n, from_int(1))) summary "Check PLe exception"; if Any_to_bool(PLe(n, from_int(1))) then { LaurelResult := xs; exit $body }; assert !Any..isexception(PFloorDiv(n, from_int(2))) summary "Check PFloorDiv exception"; mid := PFloorDiv(n, from_int(2)); assert Any..isfrom_int(mid); left := merge_sort(Any_get_slice(xs, from_Slice(0, OptSome(Any..as_int!(mid))))); right := merge_sort(Any_get_slice(xs, from_Slice(Any..as_int!(mid), OptNone()))); LaurelResult := merge(left, right); exit $body };

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var maybe_except: (Core Error) := NoError(); var xs: (Core Any) := <?>; var sorted_xs: (Core Any) := <?>; xs := from_ListAny(ListAny_cons(from_int(5), ListAny_cons(from_int(2), ListAny_cons(from_int(8), ListAny_cons(from_int(1), ListAny_cons(from_int(9), ListAny_cons(from_int(3), ListAny_nil()))))))); sorted_xs := merge_sort(xs); assert Any_to_bool(PEq(Any_len_to_Any(sorted_xs), from_int(6))) summary "length preserved"; assert Any_to_bool(PEq(Any_get(sorted_xs, from_int(0)), from_int(1))) summary "first is 1"; assert Any_to_bool(PEq(Any_get(sorted_xs, from_int(5)), from_int(9))) summary "last is 9" };

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
