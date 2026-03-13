/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- After merging, rename file to PythonRuntimeCorePart
import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
public import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

/--
Core-only prelude declarations for the Python-through-Laurel pipeline.

This contains declarations that cannot be expressed in Laurel grammar:
- Axioms
- Parameterized datatypes (`Except`)
- Type synonyms (`ExceptErrorRegex`)
- Functions using `regex` type
- Procedures using discriminator access (`..`)
- Procedures with labeled requires/ensures

Types already defined in `PythonRuntimeLaurelPart.lean` are forward-declared
here so the DDM parser can resolve references. At the Core level, the
Laurel-translated declarations take precedence and these forward declarations
are filtered out.

The original `CorePrelude.lean` remains unchanged for the Python-through-Core pipeline.
-/
private def pythonRuntimeCorePartDDM :=
#strata
program Core;

// =====================================================================
// Forward declarations of types defined in PythonRuntimeLaurelPart.
// These are needed so the DDM parser can resolve references in axioms
// and procedures below. They will be filtered out when merging with
// the Laurel-translated declarations.
// =====================================================================

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
}

datatype ListAny () {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
}

datatype DictStrAny () {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
};

function to_string(a: Any) : string;
function datetime_strptime(dtstring: Any, format: Any) : Any;
function to_string_any(a: Any) : Any;

function int_to_real (i: int) : real;
function bool_to_int (bval: bool) : int;
function bool_to_real (b: bool) : real;
function string_repeat (s: string, i: int) : string;

type CoreOnlyDelimiter;

// =====================================================================
// Core-only declarations (not expressed in Laurel)
// =====================================================================


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
// Modelling of Python unary operations
// /////////////////////////////////////////////////////////////////////////////////////

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

// /////////////////////////////////////////////////////////////////////////////////////
// Modelling some datetime-related Python operations, for testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

axiom [datetime_tostring_cancel]: forall dt: Any ::
  datetime_strptime(to_string_any(dt), from_string ("%Y-%m-%d")) == dt;

#end

public section
/--
Get the Core-only prelude declarations for the Laurel pipeline.
These are declarations that cannot be expressed in Laurel grammar.
The returned program includes forward declarations of types from the
Laurel prelude; callers should filter out duplicates when merging.
-/
def pythonRuntimeCorePart : Core.Program :=
  Core.getProgram pythonRuntimeCorePartDDM |>.fst

/--
Get only the Core-only declarations, dropping the forward declarations
that precede the `type CoreOnlyDelimiter;` sentinel (and the sentinel itself).
Everything after the delimiter is a genuine Core-only declaration.
-/
def coreOnlyFromRuntimeCorePart : List Core.Decl :=
  let decls := pythonRuntimeCorePart.decls
  -- Drop everything up to and including the CoreOnlyDelimiter sentinel
  match decls.dropWhile (fun d => d.name.name != "CoreOnlyDelimiter") with
  | _ :: rest => rest   -- drop the delimiter itself
  | [] => dbg_trace "SOUND BUG: CoreOnlyDelimiter sentinel not found in pythonRuntimeCorePart"; []

end -- public section

end Python
end Strata
