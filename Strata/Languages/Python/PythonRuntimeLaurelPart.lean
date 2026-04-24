/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
public import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Python

/--
Python prelude declarations expressed in Laurel grammar.
Converted from PythonLaurelCorePrelude.lean (Core dialect) to Laurel dialect.

Core-specific constructs that Laurel does not support:
- `inline` keyword: noted in comments
- Labels on requires/ensures/assert/assume: noted in nearby comments
- Axioms: commented out
- `mutual`/`end` blocks: flattened (Laurel does not support mutual blocks)
-/
private def pythonRuntimeLaurelPartDDM :=
#strata
program Laurel;


// /////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.

datatype Error {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string),
  RePatternError (Re_msg : string)
}

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

// Note: Core uses mutual/end blocks for Any and ListAny.
// Laurel does not support mutual blocks, so they are declared separately.

datatype OptionInt {
  OptSome (unwrap: int),
  OptNone ()
}

datatype Any {
  from_None (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_str (as_string : string),
  from_datetime (as_datetime : int),
  from_bytes (as_bytes: string),
  from_DictStrAny (as_Dict: DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: DictStrAny),
  from_Slice(start: int, stop: OptionInt),
  exception (get_error: Error)
}

datatype ListAny {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
}

datatype ListStr {
  ListStr_nil (),
  ListStr_cons (head: string, tail: ListStr)
}

datatype DictStrAny {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
}


// Regex support — re.Match and re module functions
//
// Models Python's re.Match as a composite (reference) type following the
// module_Class naming convention (re_Match).
//
// The Python-through-Laurel pipeline is entirely Any-typed: all user
// variables and function inputs/outputs are wrapped in the Any datatype.
// Consequently, re_match/re_search/re_fullmatch return Any (from_None
// or from_ClassInstance wrapping a re_Match).  If the pipeline ever
// moves to concrete types, these should return re_Match | None directly.
//
// pos and endpos are sound as 0 / str.len
// for the module-level re.match/re.search/re.fullmatch API which does
// not accept pos/endpos arguments.  If compiled-pattern method calls
// with explicit pos/endpos are supported later, those values must be
// threaded through.
//
// Methods that depend on capture groups (group, start, end, span,
// groups, lastindex, lastgroup) are uninterpreted because SMT-LIB's
// string theory has no capture group support.  This is a sound
// over-approximation: the solver treats them as abstract, so
// verification results involving these will be inconclusive rather
// than unsound.
//
// Python signatures:
//   re.compile(pattern: str) -> re.Pattern
//   re.match(pattern: str | re.Pattern, string: str) -> re.Match | None
//   re.search(pattern: str | re.Pattern, string: str) -> re.Match | None
//   re.fullmatch(pattern: str | re.Pattern, string: str) -> re.Match | None
//
// Architecture:
//
// re.compile is a semantic no-op — it returns the pattern string unchanged.
// The mode-specific factory functions re_fullmatch_bool, re_match_bool,
// re_search_bool each compile a pattern+string pair to a Bool via
// pythonRegexToCore, so anchors (^/$) are handled correctly per mode.
// Their concreteEval fires when the pattern is a string literal; on
// unsupported patterns it returns .none, leaving an uninterpreted Bool UF
// (which produces `unknown` gracefully rather than a cvc5 theory-combination
// error).
//
// On match, we return a from_ClassInstance wrapping a concrete re_Match
// with pos=0 and endpos=str.len(s), which is sound for the module-level
// API (no pos/endpos parameters).
//
// Mode-specific factory functions are declared via ReFactory (with concreteEval
// for literal pattern expansion), not in this prelude, to avoid duplicate
// definitions.

composite re_Match {
  var re_match_string : string
  var re_match_pos : int
  var re_match_endpos : int
}

// re.Match methods — uninterpreted (capture groups are beyond SMT-LIB)
function re_Match_group (self : re_Match, n : int) : string;
function re_Match_start (self : re_Match, n : int) : int;
function re_Match_end   (self : re_Match, n : int) : int;
function re_Match_span_start (self : re_Match, n : int) : int;
function re_Match_span_end   (self : re_Match, n : int) : int;
function re_Match_lastindex  (self : re_Match) : int;
function re_Match_lastgroup  (self : re_Match) : string;
function re_Match_groups     (self : re_Match) : ListStr;

function re_pattern_error(pattern : string) : Error
  external;

// The _bool variants are also factory functions (not inlined here) so that
// unsupported patterns leave an uninterpreted Bool UF rather than an
// uninterpreted RegLan UF.  An uninterpreted Bool UF produces `unknown`
// gracefully; an uninterpreted RegLan UF causes cvc5 theory-combination errors.
function re_fullmatch_bool(pattern : string, s : string) : bool
  external;
function re_match_bool(pattern : string, s : string) : bool
  external;
function re_search_bool(pattern : string, s : string) : bool
  external;

function Str.InRegEx(s: string, r: Core regex): bool external;
function Str.Length(s: string): int external;

// /////////////////////////////////////////////////////////////////////////////////////


function mk_re_Match(s : string) : Any {
  from_ClassInstance("re_Match",
    DictStrAny_cons("re_match_string", from_str(s),
      DictStrAny_cons("re_match_pos", from_int(0),
        DictStrAny_cons("re_match_endpos", from_int(Str.Length(s)),
          DictStrAny_empty()))))
};

// re.compile is a no-op: returns the pattern string unchanged.
function re_compile(pattern : Any) : Any
  requires Any..isfrom_str(pattern)
{
  pattern
};

function re_fullmatch(pattern : Any, s : Any) : Any
  requires Any..isfrom_str(pattern) && Any..isfrom_str(s)
{
  if Error..isRePatternError(re_pattern_error(Any..as_string!(pattern)))
  then exception(re_pattern_error(Any..as_string!(pattern)))
  else if re_fullmatch_bool(Any..as_string!(pattern), Any..as_string!(s))
       then mk_re_Match(Any..as_string!(s))
       else from_None()
};
function re_match(pattern : Any, s : Any) : Any
  requires Any..isfrom_str(pattern) && Any..isfrom_str(s)
{
  if Error..isRePatternError(re_pattern_error(Any..as_string!(pattern)))
  then exception(re_pattern_error(Any..as_string!(pattern)))
  else if re_match_bool(Any..as_string!(pattern), Any..as_string!(s))
       then mk_re_Match(Any..as_string!(s))
       else from_None()
};
function re_search(pattern : Any, s : Any) : Any
  requires Any..isfrom_str(pattern) && Any..isfrom_str(s)
{
  if Error..isRePatternError(re_pattern_error(Any..as_string!(pattern)))
  then exception(re_pattern_error(Any..as_string!(pattern)))
  else if re_search_bool(Any..as_string!(pattern), Any..as_string!(s))
       then mk_re_Match(Any..as_string!(s))
       else from_None()
};

// /////////////////////////////////////////////////////////////////////////////////////
//Functions that we provide to Python user
//to write assertions/contracts about about types of variables

function isBool (v: Any) : Any {
  from_bool (Any..isfrom_bool(v))
};

function isInt (v: Any) : Any {
  from_bool (Any..isfrom_int(v))
};

function isFloat (v: Any) : Any {
  from_bool (Any..isfrom_float(v))
};

function isString (v: Any) : Any {
  from_bool (Any..isfrom_str(v))
};

function isdatetime (v: Any) : Any {
  from_bool (Any..isfrom_datetime(v))
};

function isDict (v: Any) : Any {
  from_bool (Any..isfrom_DictStrAny(v))
};

function isList (v: Any) : Any {
  from_bool (Any..isfrom_ListAny(v))
};

function isClassInstance (v: Any) : Any {
  from_bool (Any..isfrom_ClassInstance(v))
};

function isInstance_of_Int (v: Any) : Any {
  from_bool (Any..isfrom_int(v) || Any..isfrom_bool(v))
};

function isInstance_of_Float (v: Any) : Any {
  from_bool (Any..isfrom_float(v) || Any..isfrom_int(v) || Any..isfrom_bool(v))
};

// /////////////////////////////////////////////////////////////////////////////////////
//Functions that we provide to Python user
//to write assertions/contracts about about types of errors
// /////////////////////////////////////////////////////////////////////////////////////

function isTypeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
};

function isAttributeError (e: Error) : Any {
  from_bool (Error..isAttributeError(e))
};

function isAssertionError (e: Error) : Any {
  from_bool (Error..isAssertionError(e))
};

function isUnimplementedError (e: Error) : Any {
  from_bool (Error..isUnimplementedError(e))
};

function isUndefinedError (e: Error) : Any {
  from_bool (Error..isUndefinedError(e))
};

function isError (e: Error) : bool {
  ! Error..isNoError(e)
};

// /////////////////////////////////////////////////////////////////////////////////////
//The following function convert Any type to bool
//based on the Python definition of truthiness for basic types
// https://docs.python.org/3/library/stdtypes.html
// /////////////////////////////////////////////////////////////////////////////////////

function Any_to_bool (v: Any) : bool
{
  if (Any..isfrom_bool(v)) then Any..as_bool!(v) else
  if (Any..isfrom_None(v)) then false else
  if (Any..isfrom_str(v)) then !(Any..as_string!(v) == "") else
  if (Any..isfrom_int(v)) then !(Any..as_int!(v) == 0) else
  if (Any..isfrom_float(v)) then !(Any..as_float!(v) == 0.0) else
  if (Any..isfrom_DictStrAny(v)) then !(Any..as_Dict!(v) == DictStrAny_empty()) else
  if (Any..isfrom_ListAny(v)) then !(Any..as_ListAny!(v) == ListAny_nil()) else
  <?>
};

// /////////////////////////////////////////////////////////////////////////////////////
// ListAny functions
// /////////////////////////////////////////////////////////////////////////////////////

function List_len (l : ListAny) : int
{
  if ListAny..isListAny_nil(l) then 0 else 1 + List_len(ListAny..tail!(l))
};

procedure List_len_pos(l : ListAny)
  invokeOn List_len(l)
  opaque
  ensures List_len(l) >= 0;

function List_contains (l : ListAny, x: Any) : bool
{
  if ListAny..isListAny_nil(l) then false else (ListAny..head!(l) == x) || List_contains(ListAny..tail!(l), x)
};

function List_extend (l1 : ListAny, l2: ListAny) : ListAny
{
  if ListAny..isListAny_nil(l1) then l2
  else ListAny_cons(ListAny..head!(l1), List_extend(ListAny..tail!(l1), l2))
};

function List_get_non_neg (l : ListAny, i : int) : Any
  requires i >= 0 && i < List_len(l)
{
  if ListAny..isListAny_nil(l) then from_None()
  else if  i == 0 then ListAny..head!(l)
  else List_get(ListAny..tail!(l), i - 1)
};

function List_get (l : ListAny, i : int) : Any
  requires i >= - List_len(l) && i < List_len(l)
{
  if i >= 0 then List_get_non_neg(l, i)
  else List_get_non_neg(l, List_len(l) + i)
};

function List_take (l : ListAny, i: int) : ListAny
  requires i >= 0 && i <= List_len(l)
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then ListAny_nil()
  else ListAny_cons(ListAny..head!(l), List_take(ListAny..tail!(l), i - 1))
};

procedure List_take_len(l : ListAny, i: int)
  invokeOn List_len(List_take(l,i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_take(l,i)) == i;

function List_drop (l : ListAny, i: int) : ListAny
  requires i >= 0 && i <= List_len(l)
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then l
  else List_drop(ListAny..tail!(l), i - 1)
};

procedure List_drop_len(l : ListAny, i: int)
  invokeOn List_len(List_drop(l,i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_drop(l,i)) == List_len(l) - i;

function int_max (i1: int, i2: int) : int
{
  if i1 >= i2 then i1 else i2
};

function int_min (i1: int, i2: int) : int
{
  if i1 <= i2 then i1 else i2
};

function List_slice_non_neg (l : ListAny, start : int, stop: int) : ListAny
  requires start >= 0 && stop >= 0
{
  if (start >= List_len(l)) || (start >= stop) then ListAny_nil()
  else List_take (List_drop (l, start), int_min(stop, List_len(l))  - start)
};


function List_slice (l : ListAny, start : int, stop: int) : ListAny
{
  List_slice_non_neg (l,
    if start >= 0 then start else int_max (List_len(l) + start, 0),
    if stop >= 0 then stop else int_max (List_len(l) + stop, 0)
  )
};

function List_set_non_neg (l : ListAny, i : int, v: Any) : ListAny
  requires i >= 0 && i < List_len(l)
{
  if ListAny..isListAny_nil(l) then ListAny_nil()
  else if  i == 0 then ListAny_cons(v, ListAny..tail!(l))
  else ListAny_cons(ListAny..head!(l), List_set(ListAny..tail!(l), i - 1, v))
};

function List_set (l : ListAny, i : int, v: Any) : ListAny
  requires i >= - List_len(l) && i < List_len(l)
{
  if i >= 0 then List_set_non_neg(l, i, v)
  else List_set_non_neg(l, List_len(l) + i, v)
};

//Require recursive function on int
function List_repeat (l: ListAny, n: int): ListAny;

function range (start: Any, stop: Any, step: Any) : Any
  requires Any..isfrom_int(start) && Any..isfrom_None(stop) && Any..isfrom_None(step);

// /////////////////////////////////////////////////////////////////////////////////////
// DictStrAny functions
// /////////////////////////////////////////////////////////////////////////////////////

function DictStrAny_contains (d : DictStrAny, key: string) : bool
{
  if DictStrAny..isDictStrAny_empty(d) then false
  else (DictStrAny..key!(d) == key) || DictStrAny_contains(DictStrAny..tail!(d), key)
};

function DictStrAny_get (d : DictStrAny, key: string) : Any
  requires DictStrAny_contains(d, key)
{
  if  DictStrAny..isDictStrAny_empty(d) then from_None()
  else if DictStrAny..key!(d) == key then DictStrAny..val!(d)
  else DictStrAny_get(DictStrAny..tail!(d), key)
};

function DictStrAny_get_or_none (d : DictStrAny, key: string) : Any
{
  if DictStrAny_contains(d, key) then DictStrAny_get(d, key)
  else from_None()
};

function Any_get_or_none (dict: Any, key: Any) : Any
  requires Any..isfrom_DictStrAny(dict) && Any..isfrom_str(key)
{
  DictStrAny_get_or_none(Any..as_Dict!(dict), Any..as_string!(key))
};

function DictStrAny_insert (d : DictStrAny, key: string, val: Any) : DictStrAny
{
  if DictStrAny..isDictStrAny_empty(d) then DictStrAny_cons(key, val, DictStrAny_empty())
  else if DictStrAny..key!(d) == key then DictStrAny_cons(key, val, DictStrAny..tail!(d))
  else DictStrAny_cons(DictStrAny..key!(d), DictStrAny..val!(d), DictStrAny_insert(DictStrAny..tail!(d), key, val))
};

function Any_get (dictOrList: Any, index: Any): Any
  requires  (Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index))) ||
            (Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= - List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)))
{
  if Any..isfrom_DictStrAny(dictOrList) then
    DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index))
  else
    List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index))
};

function Any_get_slice (list: Any, index: Any): Any
  requires (Any..isfrom_ListAny(list) && Any..isfrom_Slice(index))
{
  from_ListAny(List_slice(
    Any..as_ListAny!(list),
    Any..start!(index),
    if OptionInt..isOptSome(Any..stop!(index))
    then OptionInt..unwrap!(Any..stop!(index))
    else List_len(Any..as_ListAny!(list))))
};

function Any_get! (dictOrList: Any, index: Any): Any
{
  if Any..isexception(dictOrList) then dictOrList
  else if Any..isexception(index) then index
  else if !(Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index)) && !(Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index)) then
    exception (TypeError("Invalid subscription type"))
  else if Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index) && DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(index)) then
    DictStrAny_get(Any..as_Dict!(dictOrList), Any..as_string!(index))
  else if Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) && Any..as_int!(index) >= - List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)) then
      List_get(Any..as_ListAny!(dictOrList), Any..as_int!(index))
  else
    exception (IndexError("Invalid subscription"))
};

function Any_set (dictOrList: Any, index: Any, val: Any): Any
  requires  (Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index)) ||
            (Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) &&
            Any..as_int!(index) >= - List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)))
{
  if Any..isfrom_DictStrAny(dictOrList) then
    from_DictStrAny(DictStrAny_insert(Any..as_Dict!(dictOrList), Any..as_string!(index), val))
  else
    from_ListAny(List_set(Any..as_ListAny!(dictOrList), Any..as_int!(index), val))
};

function Any_set! (dictOrList: Any, index: Any, val: Any): Any
{
  if Any..isexception(dictOrList) then dictOrList
  else if Any..isexception(index) then index
  else if Any..isexception(val) then val
  else if !(Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index)) && !(Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index)) then
    exception (TypeError("Invalid subscription type"))
  else if Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(index) then
    from_DictStrAny(DictStrAny_insert(Any..as_Dict!(dictOrList), Any..as_string!(index), val))
  else if Any..isfrom_ListAny(dictOrList) && Any..isfrom_int(index) &&
          Any..as_int!(index) >= - List_len(Any..as_ListAny!(dictOrList)) && Any..as_int!(index) < List_len(Any..as_ListAny!(dictOrList)) then
    from_ListAny(List_set(Any..as_ListAny!(dictOrList), Any..as_int!(index), val))
  else
    exception (IndexError("Index out of bound"))
};

function Any_sets! (indices: ListAny, dictOrList: Any, val: Any): Any
{
  if ListAny..isListAny_nil(indices) then dictOrList
  else if ListAny..isListAny_nil(ListAny..tail!(indices)) then Any_set!(dictOrList, ListAny..head!(indices), val)
  else Any_set!(dictOrList, ListAny..head!(indices),
    Any_sets!(ListAny..tail!(indices), Any_get!(dictOrList, ListAny..head!(indices)), val))
};

function Any_len (v: Any) : int;

function Any_len_to_Any (v: Any) : Any {
  from_int(Any_len(v))
};

procedure Any_len_pos(v: Any)
  invokeOn Any_len(v)
  ensures Any_len(v) >= 0;

function Any_iter_index(iter: Any, index: int) : Any;

function PIn (v: Any, dictOrList: Any) : Any
  requires (Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(v)) || Any..isfrom_ListAny(dictOrList)
{
  from_bool(
    if Any..isfrom_DictStrAny(dictOrList) then
      DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(v))
    else
      List_contains(Any..as_ListAny!(dictOrList), v)
  )
};

function PNotIn ( v: Any, dictOrList: Any) : Any
  requires (Any..isfrom_DictStrAny(dictOrList) && Any..isfrom_str(v)) || Any..isfrom_ListAny(dictOrList)
{
  from_bool(
    if Any..isfrom_DictStrAny(dictOrList) then
      !DictStrAny_contains(Any..as_Dict!(dictOrList), Any..as_string!(v))
    else
      !List_contains(Any..as_ListAny!(dictOrList), v)
  )
};

// /////////////////////////////////////////////////////////////////////////////////////
// Python treats some values of different types to be equivalent
// This function models that behavior
// /////////////////////////////////////////////////////////////////////////////////////

function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;

function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
};


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
function bool_to_int (bval: bool) : int {if bval then 1 else 0};
function bool_to_real (b: bool) : real {if b then 1.0 else 0.0};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python unary operations
// /////////////////////////////////////////////////////////////////////////////////////

function PNeg (v: Any) : Any
{
  if Any..isexception(v) then v
  else if Any..isfrom_bool(v) then
    from_int(- bool_to_int(Any..as_bool!(v)))
  else if Any..isfrom_int(v) then
    from_int(- Any..as_int!(v))
  else if Any..isfrom_float(v) then
    from_float(- Any..as_float!(v))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PBitNot (v: Any) : Any
{
  if Any..isexception(v) then v
  else if Any..isfrom_bool(v) then
    from_int(-(bool_to_int(Any..as_bool!(v)) + 1))
  else if Any..isfrom_int(v) then
    from_int(-(Any..as_int!(v) + 1))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PNot (v: Any) : Any
{
  if Any..isexception(v) then v
  else from_bool(!(Any_to_bool(v)))
};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python binary operations
// /////////////////////////////////////////////////////////////////////////////////////

function Str.Concat(s: string, s2: string): string external;

function PAdd (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) + bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) + Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) + bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_float(int_to_real(Any..as_int!(v1)) + Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_float(Any..as_float!(v1) + bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_int(Any..as_int!(v1) + Any..as_int!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_float(Any..as_float!(v1) + int_to_real(Any..as_int!(v2)) )
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_float(Any..as_float!(v1) + Any..as_float!(v2))
  else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then
    from_str(Str.Concat(Any..as_string!(v1),Any..as_string!(v2)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then
    from_ListAny(List_extend(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if Any..isfrom_datetime(v1) && Any..isfrom_int(v2) then
    from_datetime((Any..as_datetime!(v1) + Any..as_int!(v2)))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PSub (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) - bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) - Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) - bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_float(bool_to_real(Any..as_bool!(v1)) - Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_float(Any..as_float!(v1) - bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_int(Any..as_int!(v1) - Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_float(int_to_real(Any..as_int!(v1)) - Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_float(Any..as_float!(v1) - int_to_real(Any..as_int!(v2)) )
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_float(Any..as_float!(v1) - Any..as_float!(v2))
  else if Any..isfrom_datetime(v1) && Any..isfrom_int(v2) then
    from_datetime(Any..as_datetime!(v1) - Any..as_int!(v2))
  else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then
    from_int(Any..as_datetime!(v1) - Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function string_repeat (s: string, i: int) : string;

function PMul (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) * bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) * Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) * bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_float(bool_to_real(Any..as_bool!(v1)) * Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_float(Any..as_float!(v1) * bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_str(v2) then
    if Any..as_bool!(v1) then v2 else from_str("")
  else if Any..isfrom_str(v1) && Any..isfrom_bool(v2) then
    if Any..as_bool!(v2) then v1 else from_str("")
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_int(Any..as_int!(v1) * Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_float(int_to_real(Any..as_int!(v1)) * Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_float(Any..as_float!(v1) * int_to_real(Any..as_int!(v2)) )
  else if Any..isfrom_int(v1) && Any..isfrom_str(v2) then
    from_str(string_repeat(Any..as_string!(v2), Any..as_int!(v1)))
  else if Any..isfrom_str(v1) && Any..isfrom_int(v2) then
    from_str(string_repeat(Any..as_string!(v1), Any..as_int!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_ListAny(v2) then
    from_ListAny(List_repeat(Any..as_ListAny!(v2), Any..as_int!(v1)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_int(v2) then
    from_ListAny(List_repeat(Any..as_ListAny!(v1), Any..as_int!(v2)))
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_float(Any..as_float!(v1) * Any..as_float!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PFloorDiv (v1: Any, v2: Any) : Any
  requires (Any..isfrom_bool(v2)==>Any..as_bool!(v2)) && (Any..isfrom_int(v2)==>Any..as_int!(v2)!=0)
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int( bool_to_int(Any..as_bool!(v1)) / bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) / Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) / bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_int(Any..as_int!(v1) / Any..as_int!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

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

function PLt (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) < bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) < Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_int!(v1) < bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_bool(bool_to_real(Any..as_bool!(v1)) < Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_float!(v1) < bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_int!(v1) < Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_bool(int_to_real(Any..as_int!(v1)) < Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_float!(v1) < int_to_real(Any..as_int!(v2)))
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_bool(Any..as_float!(v1) < Any..as_float!(v2))
  else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then
    from_bool(string_lt(Any..as_string!(v1), Any..as_string!(v2)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then
    from_bool(List_lt(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then
    from_bool(Any..as_datetime!(v1) <Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PLe (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) <= bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) <= Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_int!(v1) <= bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_bool(bool_to_real(Any..as_bool!(v1)) <= Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_float!(v1) <= bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_int!(v1) <= Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_bool(int_to_real(Any..as_int!(v1)) <= Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_float!(v1) <= int_to_real(Any..as_int!(v2)))
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_bool(Any..as_float!(v1) <= Any..as_float!(v2))
  else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then
    from_bool(string_le(Any..as_string!(v1), Any..as_string!(v2)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then
    from_bool(List_le(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then
    from_bool(Any..as_datetime!(v1) <=Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PGt (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) > bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) > Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_int!(v1) > bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_bool(bool_to_real(Any..as_bool!(v1)) > Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_float!(v1) > bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_int!(v1) > Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_bool(int_to_real(Any..as_int!(v1)) > Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_float!(v1) > int_to_real(Any..as_int!(v2)))
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_bool(Any..as_float!(v1) > Any..as_float!(v2))
  else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then
    from_bool(string_gt(Any..as_string!(v1), Any..as_string!(v2)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then
    from_bool(List_gt(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then
    from_bool(Any..as_datetime!(v1) >Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PGe (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) >= bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_bool(bool_to_int(Any..as_bool!(v1)) >= Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_int!(v1) >= bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_float(v2) then
    from_bool(bool_to_real(Any..as_bool!(v1)) >= Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_bool(v2) then
    from_bool(Any..as_float!(v1) >= bool_to_real(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_int!(v1) >= Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_float(v2) then
    from_bool(int_to_real(Any..as_int!(v1)) >= Any..as_float!(v2))
  else if Any..isfrom_float(v1) && Any..isfrom_int(v2) then
    from_bool(Any..as_float!(v1) >= int_to_real(Any..as_int!(v2)))
  else if Any..isfrom_float(v1) && Any..isfrom_float(v2) then
    from_bool(Any..as_float!(v1) >= Any..as_float!(v2))
  else if Any..isfrom_str(v1) && Any..isfrom_str(v2) then
    from_bool(string_ge(Any..as_string!(v1), Any..as_string!(v2)))
  else if Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2) then
    from_bool(List_ge(Any..as_ListAny!(v1),Any..as_ListAny!(v2)))
  else if Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2) then
    from_bool(Any..as_datetime!(v1) >=Any..as_datetime!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) == normalize_any (v'))
};

function PNEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) != normalize_any (v'))
};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python Boolean operations And and Or
// /////////////////////////////////////////////////////////////////////////////////////

function PAnd (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else
  if ! Any_to_bool (v1) then v1 else v2
};

function POr (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else
  if Any_to_bool (v1) then v1 else v2
};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python arithmetic and bitwise operations
// /////////////////////////////////////////////////////////////////////////////////////
// int_pow, int_rshift, and float_pow are provided by the factory (PyFactory.lean) with concreteEval.
// Declared here as external so PPow/PRShift can reference them; they are filtered
// during Laurel-to-Core translation and the factory provides the Core versions.
function int_pow (base: int, exp: int) : int
  external;
function int_rshift (x: int, n: int) : int
  external;
function float_pow (base: real, exp: real) : real
  external;

function PPow (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0) then
    from_int(int_pow(Any..as_int!(v1), Any..as_int!(v2)))
  else if (Any..isfrom_int(v1) && Any..isfrom_int(v2)) then
    from_float(float_pow(int_to_real(Any..as_int!(v1)), int_to_real(Any..as_int!(v2))))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0) then
    from_int(int_pow(bool_to_int(Any..as_bool!(v1)), Any..as_int!(v2)))
  else if (Any..isfrom_bool(v1) && Any..isfrom_int(v2)) then
    from_float(float_pow(bool_to_real(Any..as_bool!(v1)), int_to_real(Any..as_int!(v2))))
  else if (Any..isfrom_int(v1) && Any..isfrom_bool(v2)) then
    from_int(int_pow(Any..as_int!(v1), bool_to_int(Any..as_bool!(v2))))
  else
    exception(UnimplementedError("Pow is not defined on these input types"))
};

function PMod (v1: Any, v2: Any) : Any
  requires (Any..isfrom_bool(v2)==>Any..as_bool!(v2)) && (Any..isfrom_int(v2)==>Any..as_int!(v2)!=0)
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int( bool_to_int(Any..as_bool!(v1)) % bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) % Any..as_int!(v2))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) % bool_to_int(Any..as_bool!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) then
    from_int(Any..as_int!(v1) % Any..as_int!(v2))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling of Python bitwise shift operations
// /////////////////////////////////////////////////////////////////////////////////////

function PLShift (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0 then
    from_int(Any..as_int!(v1) * int_pow(2, Any..as_int!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0 then
    from_int(bool_to_int(Any..as_bool!(v1)) * int_pow(2, Any..as_int!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(Any..as_int!(v1) * int_pow(2, bool_to_int(Any..as_bool!(v2))))
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int(bool_to_int(Any..as_bool!(v1)) * int_pow(2, bool_to_int(Any..as_bool!(v2))))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

function PRShift (v1: Any, v2: Any) : Any
{
  if Any..isexception(v1) then v1 else if Any..isexception(v2) then v2
  else if Any..isfrom_int(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0 then
    from_int(int_rshift(Any..as_int!(v1), Any..as_int!(v2)))
  else if Any..isfrom_bool(v1) && Any..isfrom_int(v2) && Any..as_int!(v2) >= 0 then
    from_int(int_rshift(bool_to_int(Any..as_bool!(v1)), Any..as_int!(v2)))
  else if Any..isfrom_int(v1) && Any..isfrom_bool(v2) then
    from_int(int_rshift(Any..as_int!(v1), bool_to_int(Any..as_bool!(v2))))
  else if Any..isfrom_bool(v1) && Any..isfrom_bool(v2) then
    from_int(int_rshift(bool_to_int(Any..as_bool!(v1)), bool_to_int(Any..as_bool!(v2))))
  else
    exception(UndefinedError ("Operand Type is not defined"))
};

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling some datetime-related Python operations, for testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

function to_string(a: Any) : string;

function to_string_any(a: Any) : Any {
  from_str(to_string(a))
};

function datetime_strptime(dtstring: Any, format: Any) : Any;

procedure datetime_tostring_cancel(dt: Any)
  invokeOn datetime_strptime(to_string_any(dt), from_str ("%Y-%m-%d"))
  opaque
  ensures datetime_strptime(to_string_any(dt), from_str ("%Y-%m-%d")) == dt;

procedure datetime_date(d: Any) returns (ret: Any, error: Error)
  requires Any..isfrom_datetime(d) summary "(Origin_datetime_date_Requires)d_type"
  opaque
  ensures Any..isfrom_datetime(ret) && Any..as_datetime!(ret) <= Any..as_datetime!(d) summary "ret_type"
{
  var timedt: int;
  if Any..isfrom_datetime(d) then {
    // summary "timedt_le";
    assume timedt <= Any..as_datetime!(d);
    ret := from_datetime(timedt);
    error := NoError()
  }
  else {
    ret := from_None();
    error := TypeError("Input must be datetime")
  }
};

procedure datetime_now(tz: Any) returns (ret: Any)
  opaque
  ensures Any..isfrom_datetime(ret) summary "ret_type"
{
  var d: int;
  ret := from_datetime(d)
};

procedure timedelta_func(days: Any, hours: Any) returns (delta : Any, maybe_except: Error)
  requires Any..isfrom_None(days) || Any..isfrom_int(days) summary "(Origin_timedelta_Requires)"
  requires Any..isfrom_None(hours) || Any..isfrom_int(hours) summary "(Origin_timedelta_Requires)hours_type"
  requires Any..isfrom_int(days) ==> Any..as_int!(days)>=0 summary "(Origin_timedelta_Requires)days_pos"
  requires Any..isfrom_int(hours) ==> Any..as_int!(hours)>=0 summary "(Origin_timedelta_Requires)hours_pos"
  opaque
  ensures Any..isfrom_int(delta) && Any..as_int!(delta)>=0 summary "ret_pos"
{
  var days_i : int := 0;
  if Any..isfrom_int(days) then {
        days_i := Any..as_int!(days)
  };
  var hours_i : int := 0;
  if Any..isfrom_int(hours) then {
        hours_i := Any..as_int!(hours)
  };
  delta := from_int ((((days_i * 24) + hours_i) * 3600) * 1000000)
};

// /////////////////////////////////////////////////////////////////////////////////////
// For testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

procedure test_helper_procedure(req_name : Any, opt_name : Any) returns (ret: Any, maybe_except: Error)
  requires req_name == from_str("foo") summary "(Origin_test_helper_procedure_Requires)req_name_is_foo"
  requires (Any..isfrom_None(opt_name)) || (Any..isfrom_str(opt_name)) summary "(Origin_test_helper_procedure_Requires)req_opt_name_none_or_str"
  requires (opt_name == from_None()) || (opt_name == from_str("bar")) summary "(Origin_test_helper_procedure_Requires)req_opt_name_none_or_bar"
  opaque
  ensures (Error..isNoError(maybe_except)) summary "ensures_maybe_except_none"
{
  assert req_name == from_str("foo") summary "assert_name_is_foo";
  assert (Any..isfrom_None(opt_name)) || (Any..isfrom_str(opt_name)) summary "assert_opt_name_none_or_str";
  assert (opt_name == from_None()) || (opt_name == from_str("bar")) summary "assert_opt_name_none_or_bar";
  assume (Error..isNoError(maybe_except)) // summary "assume_maybe_except_none"
};

procedure print(msg : Any, opt : Any, sep : Any, end : Any, file : Any, flush : Any) returns ();

#end

/--
Parse the Laurel DDM prelude into a Laurel Program.
-/

-- Prelude functions that may return an exception value as Any.
-- We should make sure that all functions in this list propagate the exceptions from their arguments.
def AnyMaybeExceptionList := ["Any_get!", "Any_set!", "Any_sets!", "PNeg", "PBitNot", "PNot", "PAdd", "PSub", "PMul",
   "PFloorDiv", "PLt", "PLe", "PGt", "PGe", "PPow", "PMod", "PLShift", "PRShift", "PAnd", "POr"]

public def pythonRuntimeLaurelPart : Laurel.Program :=
  match Laurel.TransM.run (some $ .file "") (Laurel.parseProgram pythonRuntimeLaurelPartDDM) with
  | .ok p =>
    let addExceptionMd := p.staticProcedures.map (λ f =>
      if f.name.text ∈ AnyMaybeExceptionList then
        {f with name := {f.name with md := f.name.md.pushElem (.label "maybeException") (.switch true) }}
      else f)
    {p with staticProcedures := addExceptionMd}
  | .error e => dbg_trace s!"SOUND BUG: Failed to parse Python runtime Laurel part: {e}"; default

end Python
end Strata
