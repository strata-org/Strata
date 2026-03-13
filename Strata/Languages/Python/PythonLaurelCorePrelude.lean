/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Elab
import Strata.DDM.AST
public import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

def pythonLaurelPrelude :=
#strata
program Core;

// /////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.

datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string)
};

// /////////////////////////////////////////////////////////////////////////////////////

// Any type modelling for Python
// We model Any type of Python as an inductive type in Strata,
// where the value of each type is wrapped around by a constructor.
// In the PythonToLaurel translator, all user-defined variables
// and input/outputs of all user-defined functions are
// translated into variables of this Any type.
// We also add exception constructor for Any type to catch
// errors in the functions that model Python operators that
// appears later in this prelude.
// In this prelude, we model datetime as a single int and assume
// that the conversion from a string constant is handled by the translator.

mutual
datatype Any () {
  from_none (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_string (as_string : string),
  from_datetime (as_datetime : int),
  from_Dict (as_Dict: DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: DictStrAny),
  exception (get_error: Error)
};

datatype ListAny () {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
};

datatype DictStrAny () {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
};
end;

// /////////////////////////////////////////////////////////////////////////////////////
//Functions that we provide to Python user
//to write assertions/contracts about about types of variables

inline function isBool (v: Any) : Any {
  from_bool (Any..isfrom_bool(v))
}

inline function isInt (v: Any) : Any {
  from_bool (Any..isfrom_int(v))
}

inline function isFloat (v: Any) : Any {
  from_bool (Any..isfrom_float(v))
}

inline function isString (v: Any) : Any {
  from_bool (Any..isfrom_string(v))
}

inline function isdatetime (v: Any) : Any {
  from_bool (Any..isfrom_datetime(v))
}

inline function isDict (v: Any) : Any {
  from_bool (Any..isfrom_Dict(v))
}

inline function isList (v: Any) : Any {
  from_bool (Any..isfrom_ListAny(v))
}

inline function isClassInstance (v: Any) : Any {
  from_bool (Any..isfrom_ClassInstance(v))
}

inline function isInstance_of_Int (v: Any) : Any {
  from_bool (Any..isfrom_int(v) || Any..isfrom_bool(v))
}

inline function isInstance_of_Float (v: Any) : Any {
  from_bool (Any..isfrom_float(v) || Any..isfrom_int(v) || Any..isfrom_bool(v))
}

// /////////////////////////////////////////////////////////////////////////////////////
//Functions that we provide to Python user
//to write assertions/contracts about about types of errors
// /////////////////////////////////////////////////////////////////////////////////////

inline function isTypeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
}

inline function isAttributeError (e: Error) : Any {
  from_bool (Error..isAttributeError(e))
}

inline function isAssertionError (e: Error) : Any {
  from_bool (Error..isAssertionError(e))
}

inline function isUnimplementedError (e: Error) : Any {
  from_bool (Error..isUnimplementedError(e))
}

inline function isUndefinedError (e: Error) : Any {
  from_bool (Error..isUndefinedError(e))
}

inline function isError (e: Error) : bool {
  ! Error..isNoError(e)
}

// /////////////////////////////////////////////////////////////////////////////////////
//The following function convert Any type to bool
//based on the Python definition of truthiness for basic types
// https://docs.python.org/3/library/stdtypes.html
// /////////////////////////////////////////////////////////////////////////////////////

inline function Any_to_bool (v: Any) : bool
  requires (Any..isfrom_bool(v) || Any..isfrom_none(v) || Any..isfrom_string(v) || Any..isfrom_int(v));
{
  if (Any..isfrom_bool(v)) then Any..as_bool!(v) else
  if (Any..isfrom_none(v)) then false else
  if (Any..isfrom_string(v)) then !(Any..as_string!(v) == "") else
  if (Any..isfrom_int(v)) then !(Any..as_int!(v) == 0) else
  false
  //WILL BE ADDED
}

// /////////////////////////////////////////////////////////////////////////////////////
// ListAny functions
// /////////////////////////////////////////////////////////////////////////////////////

rec function List_len (@[cases] l : ListAny) : int
{
  if ListAny..isListAny_nil(l) then 0 else 1 + List_len(ListAny..tail!(l))
}

axiom [List_len_pos]: forall l : ListAny :: List_len(l) >= 0;

rec function List_contains (@[cases] l : ListAny, x: Any) : bool
{
  if ListAny..isListAny_nil(l) then false else (ListAny..head!(l) == x) || List_contains(ListAny..tail!(l), x)
}

rec function List_extend (@[cases] l1 : ListAny, l2: ListAny) : ListAny
{
  if ListAny..isListAny_nil(l1) then l2
  else ListAny_cons(ListAny..head!(l1), List_extend(ListAny..tail!(l1), l2))
}

rec function List_get (@[cases] l : ListAny, i : int) : Any
  requires i >= 0 && i < List_len(l);
{
  if ListAny..isListAny_nil(l) then from_none()
  else if  i == 0 then ListAny..head!(l)
  else List_get(ListAny..tail!(l), i - 1)
}

rec function List_take (@[cases] l : ListAny, i: int) : ListAny
  requires i >= 0 && i <= List_len(l);
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then ListAny_nil()
  else ListAny_cons(ListAny..head!(l), List_take(ListAny..tail!(l), i - 1))
}

axiom [List_take_len]: forall l : ListAny, i: int :: {List_len(List_take(l,i))}
  (i >= 0 && i <= List_len(l)) ==> List_len(List_take(l,i)) == i;

rec function List_drop (@[cases] l : ListAny, i: int) : ListAny
  requires i >= 0 && i <= List_len(l);
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then l
  else List_drop(ListAny..tail!(l), i - 1)
}

axiom [List_drop_len]: forall l : ListAny, i: int :: {List_len(List_drop(l,i))}
  (i >= 0 && i <= List_len(l)) ==> List_len(List_drop(l,i)) == List_len(l) - i;

inline function List_slice (l : ListAny, start : int, stop: int) : ListAny
  requires start >= 0 && start < List_len(l) && stop >= 0 && stop <= List_len(l) && start <= stop;
{
  List_take (List_drop (l, start), stop - start)
}

rec function List_set (@[cases] l : ListAny, i : int, v: Any) : ListAny
  requires i >= 0 && i < List_len(l);
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then ListAny_cons(v, ListAny..tail!(l))
  else ListAny_cons(ListAny..head!(l), List_set(ListAny..tail!(l), i - 1, v))
}

rec function List_map (@[cases] l : ListAny, f: Any -> Any) : ListAny
{
  if ListAny..isListAny_nil(l) then
    ListAny_nil()
  else
    ListAny_cons(f(ListAny..head!(l)), List_map(ListAny..tail!(l), f))
}

rec function List_filter (@[cases] l : ListAny, f: Any -> bool) : ListAny
{
  if ListAny..isListAny_nil(l) then
    ListAny_nil()
  else if f(ListAny..head!(l)) then
    ListAny_cons(ListAny..head!(l), List_filter(ListAny..tail!(l), f))
  else
    List_filter(ListAny..tail!(l), f)
}

//Require recursive function on int
function List_repeat (l: ListAny, n: int): ListAny;


// /////////////////////////////////////////////////////////////////////////////////////
// DictStrAny functions
// /////////////////////////////////////////////////////////////////////////////////////

rec function DictStrAny_contains (@[cases] d : DictStrAny, key: string) : bool
{
  if DictStrAny..isDictStrAny_empty(d) then false
  else (DictStrAny..key!(d) == key) || DictStrAny_contains(DictStrAny..tail!(d), key)
}

rec function DictStrAny_get (@[cases] d : DictStrAny, key: string) : Any
  requires DictStrAny_contains(d, key);
{
  if  DictStrAny..isDictStrAny_empty(d) then from_none()
  else if DictStrAny..key!(d) == key then DictStrAny..val!(d)
  else DictStrAny_get(DictStrAny..tail!(d), key)
}

rec function DictStrAny_insert (@[cases] d : DictStrAny, key: string, val: Any) : DictStrAny
{
  if DictStrAny..isDictStrAny_empty(d) then DictStrAny_cons(key, val, DictStrAny_empty())
  else if DictStrAny..key!(d) == key then DictStrAny_cons(key, val, DictStrAny..tail!(d))
  else DictStrAny_cons(DictStrAny..key!(d), DictStrAny..val!(d), DictStrAny_insert(DictStrAny..tail!(d), key, val))
}

inline function Any_get (dictOrList: Any, index: Any): Any
  requires  (Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index))) ||
            (Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= 0 && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)));
{
  if Any..isfrom_Dict(dictOrList) then
    DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index))
  else
    List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index))
}

inline function Any_get! (dictOrList: Any, index: Any): Any
{
  if Any..isexception(dictOrList) then dictOrList
  else if Any..isexception(index) then index
  else if !(Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index)) && !(Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index)) then
    exception (TypeError("Invalid subscription type"))
  else if Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index)) then
    DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index))
  else if Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= 0 && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)) then
    List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index))
  else
    exception (IndexError("Invalid subscription"))
}

inline function Any_set (dictOrList: Any, index: Any, val: Any): Any
  requires  (Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index)) ||
            (Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= 0 && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)));
{
  if Any..isfrom_Dict(dictOrList) then
    from_Dict(DictStrAny_insert(Any..as_Dict!(dictOrList), Any..as_string!(index), val))
  else
    from_ListAny(List_set(Any..as_ListAny!(dictOrList), Any..as_int!(index), val))
}

inline function Any_set! (dictOrList: Any, index: Any, val: Any): Any
{
  if Any..isexception(dictOrList) then dictOrList
  else if Any..isexception(index) then index
  else if Any..isexception(val) then val
  else if !(Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index)) && !(Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index)) then
    exception (TypeError("Invalid subscription type"))
  else if Any..isfrom_Dict(dictOrList) && Any..isfrom_string(index) then
    from_Dict(DictStrAny_insert(Any..as_Dict!(dictOrList), Any..as_string!(index), val))
  else if Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= 0 && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)) then
    from_ListAny(List_set(Any..as_ListAny!(dictOrList), Any..as_int!(index), val))
  else
    exception (IndexError("Index out of bound"))
}

rec function Any_sets (dictOrList: Any, @[cases] indices: ListAny, val: Any): Any
{
  if ListAny..isListAny_nil(indices) then dictOrList
  else if ListAny..isListAny_nil(ListAny..tail!(indices)) then Any_set!(dictOrList, ListAny..head!(indices), val)
  else Any_set!(dictOrList, ListAny..head!(indices),
    Any_sets(Any_get!(dictOrList, ListAny..head!(indices)), ListAny..tail!(indices), val))
}

inline function PIn (v: Any, dictOrList: Any) : Any
  requires (Any..isfrom_Dict(dictOrList) && Any..isfrom_string(v)) || Any..isfrom_ListAny(dictOrList);
{
  from_bool(
    if Any..isfrom_Dict(dictOrList) then
      DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(v))
    else
      List_contains(Any..as_ListAny!(dictOrList), v)
  )
}

inline function PNotIn ( v: Any, dictOrList: Any) : Any
  requires (Any..isfrom_Dict(dictOrList) && Any..isfrom_string(v)) || Any..isfrom_ListAny(dictOrList);
{
  from_bool(
    if Any..isfrom_Dict(dictOrList) then
      !DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(v))
    else
      !List_contains(Any..as_ListAny!(dictOrList), v)
  )
}

// /////////////////////////////////////////////////////////////////////////////////////
// Python treats some values of different types to be equivalent
// This function models that behavior
// /////////////////////////////////////////////////////////////////////////////////////

function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;

inline function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
}

// /////////////////////////////////////////////////////////////////////////////////////
// MODELLING PYTHON OPERATIONS
// Note that there is no official document that define the semantic of Python operations
// The model of them in this prelude is based on experiments of basic types
// /////////////////////////////////////////////////////////////////////////////////////


// /////////////////////////////////////////////////////////////////////////////////////
// This function convert an int to a real
// Need to connect to an SMT function
function int_to_real (i: int) : real;

// /////////////////////////////////////////////////////////////////////////////////////
// Converting bool to int or real
// Used to in Python binary operators' modelling
inline function bool_to_int (bval: bool) : int {if bval then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python unary operations
// /////////////////////////////////////////////////////////////////////////////////////

inline function PNeg (v: Any) : Any
{
  if Any..isexception(v) then v
  else if (Any..isfrom_bool(v)) then
    from_int(- bool_to_int(Any..as_bool!(v)))
  else if (Any..isfrom_int(v)) then
    from_int(- Any..as_int!(v))
  else if (Any..isfrom_float(v)) then
    from_float(- Any..as_float!(v))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PNot (v: Any) : Any
{
  if Any..isexception(v) then v
  else if (Any..isfrom_bool(v)) then
    from_bool(!(Any..as_bool!(v)))
  else if (Any..isfrom_int(v)) then
    from_bool(!(Any..as_int!(v) == 0))
  else if (Any..isfrom_float(v)) then
    from_bool(!(Any..as_float!(v) == 0.0))
  else if (Any..isfrom_string(v)) then
    from_bool(!(Any..as_string!(v) == ""))
  else if (Any..isfrom_ListAny(v)) then
    from_bool(!(List_len(Any..as_ListAny!(v)) == 0))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}


// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python binary operations
// /////////////////////////////////////////////////////////////////////////////////////

inline function PAdd (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) + bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) + Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_int(Any..as_int!(v1) + bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_float(int_to_real(Any..as_int!(v1)) + Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_float(Any..as_float!(v1) + bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_int(Any..as_int!(v1) + Any..as_int!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_float(Any..as_float!(v1) + int_to_real(Any..as_int!(v2)) )
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_float(Any..as_float!(v1) + Any..as_float!(v2))
  else if (Any..isfrom_string(v1) && Any..isfrom_string(v2)) then
    from_string(str.concat(Any..as_string!(v1),Any..as_string!(v2)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2)) then
    from_ListAny(List_extend(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_int(v2)) then
    from_datetime((Any..as_datetime!(v1) + Any..as_int!(v2)))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}


inline function PSub (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) - bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) - Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_int(Any..as_int!(v1) - bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_float(bool_to_real(Any..as_bool!(v1)) - Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_float(Any..as_float!(v1) - bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_int(Any..as_int!(v1) - Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_float(int_to_real(Any..as_int!(v1)) - Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_float(Any..as_float!(v1) - int_to_real(Any..as_int!(v2)) )
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_float(Any..as_float!(v1) - Any..as_float!(v2))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_int(v2)) then
    from_datetime(Any..as_datetime!(v1) - Any..as_int!(v2))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2)) then
    from_int(Any..as_datetime!(v1) - Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}


function string_repeat (s: string, i: int) : string;

inline function PMul (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) * bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) * Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_int(Any..as_int!(v1) * bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_float(bool_to_real(Any..as_bool!(v1)) * Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_float(Any..as_float!(v1) * bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_string(v2)) then
    if Any..as_bool!(v1) then v2 else from_string("")
  else if (Any..isfrom_string(v1) && Any..isfrom_bool(v2)) then
    if Any..as_bool!(v2) then v1 else from_string("")
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_int(Any..as_int!(v1) * Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_float(int_to_real(Any..as_int!(v1)) * Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_float(Any..as_float!(v1) * int_to_real(Any..as_int!(v2)) )
  else if (Any..isfrom_int(v1) && Any..isfrom_string(v2)) then
    from_string(string_repeat(Any..as_string!(v2), Any..as_int!(v1)))
  else if (Any..isfrom_string(v1) && Any..isfrom_int(v2)) then
    from_string(string_repeat(Any..as_string!(v1), Any..as_int!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_ListAny(v2)) then
    from_ListAny(List_repeat(Any..as_ListAny!(v2), Any..as_int!(v1)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_int(v2)) then
    from_ListAny(List_repeat(Any..as_ListAny!(v1), Any..as_int!(v2)))
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_float(Any..as_float!(v1) * Any..as_float!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PFloorDiv (v1: Any, v2: Any) : Any
  requires (Any..isfrom_bool(v2)==>Any..as_bool!(v2)) && (Any..isfrom_int(v2)==>Any..as_int!(v2)!=0);
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_int( bool_to_int(Any..as_bool!(v1)) / bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_int(bool_to_int(Any..as_bool!(v1)) / Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_int(Any..as_int!(v1) / bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_int(Any..as_int!(v1) / Any..as_int!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python comparision operations
// /////////////////////////////////////////////////////////////////////////////////////

function string_lt (s1: string, s2: string) : bool;
function string_le (s1: string, s2: string) : bool;
function string_gt (s1: string, s2: string) : bool;
function string_ge (s1: string, s2: string) : bool;
function List_lt (l1: ListAny, l2: ListAny): bool;
function List_le (l1: ListAny, l2: ListAny): bool;
function List_gt (l1: ListAny, l2: ListAny): bool;
function List_ge (l1: ListAny, l2: ListAny): bool;

inline function PLt (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) < bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) < Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_int!(v1) < bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_bool(bool_to_real(Any..as_bool!(v1)) < Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_float!(v1) < bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_int!(v1) < Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_bool(int_to_real(Any..as_int!(v1)) < Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_float!(v1) < int_to_real(Any..as_int!(v2)))
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_bool(Any..as_float!(v1) < Any..as_float!(v2))
  else if (Any..isfrom_string(v1) && Any..isfrom_string(v2)) then
    from_bool(string_lt(Any..as_string!(v1), Any..as_string!(v2)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2)) then
    from_bool(List_lt(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2)) then
    from_bool(Any..as_datetime!(v1) <Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PLe (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) <= bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) <= Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_int!(v1) <= bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_bool(bool_to_real(Any..as_bool!(v1)) <= Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_float!(v1) <= bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_int!(v1) <= Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_bool(int_to_real(Any..as_int!(v1)) <= Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_float!(v1) <= int_to_real(Any..as_int!(v2)))
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_bool(Any..as_float!(v1) <= Any..as_float!(v2))
  else if (Any..isfrom_string(v1) && Any..isfrom_string(v2)) then
    from_bool(string_le(Any..as_string!(v1), Any..as_string!(v2)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2)) then
    from_bool(List_le(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2)) then
    from_bool(Any..as_datetime!(v1) <=Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PGt (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) > bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) > Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_int!(v1) > bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_bool(bool_to_real(Any..as_bool!(v1)) > Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_float!(v1) > bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_int!(v1) > Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_bool(int_to_real(Any..as_int!(v1)) > Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_float!(v1) > int_to_real(Any..as_int!(v2)))
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_bool(Any..as_float!(v1) > Any..as_float!(v2))
  else if (Any..isfrom_string(v1) && Any..isfrom_string(v2)) then
    from_bool(string_gt(Any..as_string!(v1), Any..as_string!(v2)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2)) then
    from_bool(List_gt(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2)) then
    from_bool(Any..as_datetime!(v1) >Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PGe (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) >= bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_bool(bool_to_int(Any..as_bool!(v1)) >= Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_int!(v1) >= bool_to_int(Any..as_bool!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_float(v2)) then
    from_bool(bool_to_real(Any..as_bool!(v1)) >= Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_bool(v2)) then
    from_bool(Any..as_float!(v1) >= bool_to_real(Any..as_bool!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_int!(v1) >= Any..as_int!(v2))
  else if (Any..isfrom_int(v1) && Any..isfrom_float(v2)) then
    from_bool(int_to_real(Any..as_int!(v1)) >= Any..as_float!(v2))
  else if (Any..isfrom_float(v1) && Any..isfrom_int(v2)) then
    from_bool(Any..as_float!(v1) >= int_to_real(Any..as_int!(v2)))
  else if (Any..isfrom_float(v1) && Any..isfrom_float(v2)) then
    from_bool(Any..as_float!(v1) >= Any..as_float!(v2))
  else if (Any..isfrom_string(v1) && Any..isfrom_string(v2)) then
    from_bool(string_ge(Any..as_string!(v1), Any..as_string!(v2)))
  else if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2)) then
    from_bool(List_ge(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2)) then
    from_bool(Any..as_datetime!(v1) >=Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
}

inline function PEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) == normalize_any (v'))
}

inline function PNEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) != normalize_any (v'))
}

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python Boolean operations And and Or
// /////////////////////////////////////////////////////////////////////////////////////

inline function PAnd (v1: Any, v2: Any) : Any
  requires (Any..isfrom_bool(v1) || Any..isfrom_none(v1) || Any..isfrom_string(v1) || Any..isfrom_int(v1));
{
  if ! Any_to_bool (v1) then v1 else v2
}

inline function POr (v1: Any, v2: Any) : Any
  requires (Any..isfrom_bool(v1) || Any..isfrom_none(v1) || Any..isfrom_string(v1) || Any..isfrom_int(v1));
{
  if Any_to_bool (v1) then v1 else v2
}


// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of other Python operations, currrently unsupported
// /////////////////////////////////////////////////////////////////////////////////////
inline function PPow (v1: Any, v2: Any) : Any
{
  exception(UnimplementedError ("Pow operator is not supported"))
}

inline function PMod (v1: Any, v2: Any) : Any
{
  exception(UnimplementedError ("Mod operator is not supported"))
}

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python Boolean operations And and Or
// /////////////////////////////////////////////////////////////////////////////////////


// /////////////////////////////////////////////////////////////////////////////////////
// Modelling some datetime-related Python operations, for testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

function to_string(a: Any) : string;

function to_string_any(a: Any) : Any {
  from_string(to_string(a))
}

function datetime_strptime(dtstring: Any, format: Any) : Any;

axiom [datetime_tostring_cancel]: forall dt: Any ::
  datetime_strptime(to_string_any(dt), from_string ("%Y-%m-%d")) == dt;

procedure datetime_date(d: Any) returns (ret: Any, error: Error)
spec {
  requires [d_type]: Any..isfrom_datetime(d);
  ensures [ret_type]: Any..isfrom_datetime(ret) && Any..as_datetime!(ret) <= Any..as_datetime!(d);
}
{
  var timedt: int;
  if (Any..isfrom_datetime(d)) {
    assume [timedt_le]: timedt <= Any..as_datetime!(d);
    ret := from_datetime(timedt);
    error := NoError();
  }
  else {
    ret := from_none();
    error := TypeError("Input must be datetime");
  }
};

procedure datetime_now() returns (ret: Any)
spec {
  ensures [ret_type]: Any..isfrom_datetime(ret);
}
{
  var d: int;
  ret := from_datetime(d);
};

procedure timedelta(days: Any, hours: Any) returns (delta : Any, maybe_except: Error)
spec{
  requires [days_type]: Any..isfrom_none(days) || Any..isfrom_int(days);
  requires [hours_type]: Any..isfrom_none(hours) || Any..isfrom_int(hours);
  requires [days_pos]: Any..isfrom_int(days) ==> Any..as_int!(days)>=0;
  requires [hours_pos]: Any..isfrom_int(hours) ==> Any..as_int!(hours)>=0;
  ensures [ret_pos]: Any..isfrom_int(delta) && Any..as_int!(delta)>=0;
}
{
  var days_i : int := 0;
  if (Any..isfrom_int(days)) {
        days_i := Any..as_int!(days);
  }
  var hours_i : int := 0;
  if (Any..isfrom_int(hours)) {
        hours_i := Any..as_int!(hours);
  }
  delta := from_int ((((days_i * 24) + hours_i) * 3600) * 1000000);
};

// /////////////////////////////////////////////////////////////////////////////////////
// For testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

procedure test_helper_procedure(req_name : Any, opt_name : Any) returns (ret: Any, maybe_except: Error)
spec {
  requires [req_name_is_foo]: req_name == from_string("foo");
  requires [req_opt_name_none_or_str]: (Any..isfrom_none(opt_name)) || (Any..isfrom_string(opt_name));
  requires [req_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar"));
  ensures [ensures_maybe_except_none]: (Error..isNoError(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == from_string("foo");
  assert [assert_opt_name_none_or_str]: (Any..isfrom_none(opt_name)) || (Any..isfrom_string(opt_name));
  assert [assert_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar"));
  assume [assume_maybe_except_none]: (Error..isNoError(maybe_except));
};

procedure print(msg : Any) returns ();

//This is only used to overwrite the Box datatype of Laurel prelude
//WILL BE REMOVED
datatype Box () {
  BoxInt(intVal: Any)
};

#end

public section

def Core.PythonLaurelPrelude : Core.Program :=
   Core.getProgram pythonLaurelPrelude |>.fst


def getProcedures (decls: List Core.Decl) : List String :=
  decls.filterMap (λ decl =>
    match decl.kind with
        |.proc => some decl.name.name
        | _ => none)

def corePreludeProcedures := getProcedures Core.PythonLaurelPrelude.decls

end -- public section

end Python
end Strata
