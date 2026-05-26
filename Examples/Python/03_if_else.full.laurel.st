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

function is_IntReal(v: Any): bool
  opaque;

function Any_real_to_int(v: Any): int
  opaque;

function normalize_any(v: Any): Any
{ if v == from_bool(true) then from_int(1) else if v == from_bool(false) then from_int(0) else if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else v };

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
{ var nullcall_ret: (Core Any) := from_None(); LaurelResult := from_None(); var maybe_except: (Core Error) := NoError(); var flag: (Core Any) := <?>; var val: (Core Any) := <?>; flag := from_bool(true); assert Any..isfrom_bool(flag); val := from_int(0); assert Any..isfrom_int(val); if Any_to_bool(flag) then { val := from_int(10) } else { val := from_int(20) }; assert Any_to_bool(PEq(val, from_int(10))) summary "val should be 10" };

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
