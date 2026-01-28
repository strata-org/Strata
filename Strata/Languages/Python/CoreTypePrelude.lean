/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata

def CoreTypePrelude :=
#strata
program Core;

type Datetime;

// Class type
type ClassInstance;
type InstanceAttributes;
type Dict;


// Any and ListAny types

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

datatype Any () {
  from_none (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_string (as_string : string),
  from_Datetime (as_datetime : Datetime),
  from_Dict (as_Dict: Dict),
  from_ListAny (as_ListAny : List Any),
  from_ClassInstance (classname : string, instance_attributes: InstanceAttributes)
};

type ListAny := List Any;

// Accessible to users
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

inline function isDatetime (v: Any) : Any {
  from_bool (Any..isfrom_Datetime(v))
}

inline function isDict (v: Any) : Any {
  from_bool (Any..isfrom_Dict(v))
}

inline function isList (v: Any) : Any {
  from_bool (Any..isfrom_ListAny(v))
}

inline function isClassIntance (v: Any) : Any {
  from_bool (Any..isfrom_ClassInstance(v))
}

inline function is_instance_of_Class (v: Any, cn: string) : Any {
  from_bool (Any..isfrom_ClassInstance(v) && Any..classname(v) == cn)
}

inline function isInstance_of_Int (v: Any) : Any {
  from_bool (Any..isfrom_int(v) || Any..isfrom_bool(v))
}

inline function isInstance_of_Float (v: Any) : Any {
  from_bool (Any..isfrom_float(v) || Any..isfrom_int(v) || Any..isfrom_bool(v))
}

inline function Any_to_bool (v: Any) : bool {
  if (Any..isfrom_bool(v)) then Any..as_bool(v) else
  if (Any..isfrom_none(v)) then false else
  if (Any..isfrom_string(v)) then !(Any..as_string(v) == "") else
  if (Any..isfrom_int(v)) then !(Any..as_int(v) == 0) else
  false
  //TOBE MORE
}


// ListAny functions
function List_contains (l : ListAny, x: Any) : bool;
function List_len (l : ListAny) : int;
function List_extend (l1 : ListAny, l2: ListAny) : ListAny;
function List_append (l: ListAny, x: Any) : ListAny;
function List_get_func (l : ListAny, i : int) : Any;
function List_reverse (l: ListAny) : ListAny;
function List_index! (l: ListAny, v: Any): int;
function List_index (l: ListAny, v: Any): int;
function List_repeat (l: ListAny, n: int): ListAny;
function List_insert (l: ListAny, i: int, v: Any): ListAny;
function List_remove (l: ListAny, v: Any): ListAny;
function List_pop (l: ListAny, i: int): ListAny;
function List_lt (l1: ListAny, L2: ListAny): bool;
function List_le (l1: ListAny, L2: ListAny): bool;
function List_gt (l1: ListAny, L2: ListAny): bool;
function List_ge (l1: ListAny, L2: ListAny): bool;


datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string)
};

// Accessible to users
inline function isTypeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
}

inline function isAttributeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
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

inline function isError (e: Error) : Any {
  from_bool (! Error..isNoError(e))
}




// Class types
//Dup type for InstanceAttributes,
type InstanceAttributesDup := Map string Any;
function InstanceAttributes_from_Dup(ia: InstanceAttributesDup): InstanceAttributes;
function InstanceAttributes_to_Dup(ia: InstanceAttributes): InstanceAttributesDup;
axiom [IA_constr_destr_cancel]: forall ia: InstanceAttributesDup :: {InstanceAttributes_to_Dup(InstanceAttributes_from_Dup(ia))}
  InstanceAttributes_to_Dup(InstanceAttributes_from_Dup(ia)) == ia;
axiom [IA_destr_constr_cancel]: forall ia: InstanceAttributes :: {InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(ia))}
  InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(ia)) == ia;


function InstanceAttributes_empty() : InstanceAttributes;
axiom [AttributeAnys_empty_def]: forall a: string :: {InstanceAttributes_to_Dup(InstanceAttributes_empty())[a]}
  InstanceAttributes_to_Dup(InstanceAttributes_empty())[a] == from_none();

function ClassInstance_empty (c: string) : Any {
  from_ClassInstance(c,InstanceAttributes_empty())
}


procedure ClassInstance_init_InstanceAttribute(ci: Any, attribute: string, v: Any) returns (ret: Any, error: Error)
{
  if (Any..isfrom_ClassInstance(ci)) {
    ret := from_ClassInstance(Any..classname(ci), InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(Any..instance_attributes(ci))[attribute := v]));
    error := NoError ();
  }
  else {
    error := TypeError ("Not a Class");
  }
};

procedure ClassInstance_get_InstanceAttribute(ci: Any, attribute: string) returns (ret: Any, error: Error) {
  if (Any..isfrom_ClassInstance(ci))
  {
    ret := InstanceAttributes_to_Dup(Any..instance_attributes(ci))[attribute];
    if (Any..isfrom_none(ret)) {
      error := AttributeError("Attribute not in ClassInstance Attributes");
    } else {
      error := NoError ();
    }
  } else {
    ret := from_none();
    error := TypeError ("Not a Class");
  }
};

procedure ClassInstance_set_InstanceAttribute(ci: Any, attribute: string, v: Any) returns (ret: Any, error: Error)
{
  var attval : Any;
  if (Any..isfrom_ClassInstance(ci))
  {
    attval := InstanceAttributes_to_Dup(Any..instance_attributes(ci))[attribute];
    if (Any..isfrom_none(attval)) {
      error := AttributeError("Attribute not in ClassInstance Attributes");
    } else {
      ret := from_ClassInstance(Any..classname(ci), InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(Any..instance_attributes(ci))[attribute := v]));
      error := NoError ();
    }
  } else {
    ret := ci;
    error := TypeError ("Not a Class");
  }
};

function hasAttribute(ci: Any, attribute: string): bool {
  if (Any..isfrom_ClassInstance(ci)) then
    !(InstanceAttributes_to_Dup(Any..instance_attributes(ci))[attribute] == from_none())
  else false
}


function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;
// to be extended
function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
}

// Dict type
type DictDup := Map Any Any;
function Dict_from_DictDup(d: DictDup): Dict;
function Dict_to_DictDup(d: Dict): DictDup;
axiom [Dict_constr_destr_cancel]: forall d: DictDup :: {Dict_to_DictDup(Dict_from_DictDup(d))}
  Dict_to_DictDup(Dict_from_DictDup(d)) == d;
axiom [Dict_destr_constr_cancel]: forall d: Dict :: {Dict_from_DictDup(Dict_to_DictDup(d))}
  Dict_from_DictDup(Dict_to_DictDup(d)) == d;


inline function Dict_set_func (d: Dict, k: Any, v: Any) : Dict {
  Dict_from_DictDup(Dict_to_DictDup(d)[normalize_any(k):= v])
}

inline function Dict_get_func (d: Dict, k: Any) : Any {
  Dict_to_DictDup(d)[normalize_any(k)]
}

function Dict_remove_func (d: Dict, k: Any) : Dict {
  Dict_from_DictDup(Dict_to_DictDup(d)[normalize_any(k):= from_none()])
}

inline function Dict_contains (d: Dict, k: Any) : bool {
  Dict_get_func (d,k) != from_none()
}

function Any_to_DictDup (d: Any): DictDup {
  Dict_to_DictDup(Any..as_Dict(d))
}

inline function Any_in_Dict (a: Any, d: Any) : Any {
  from_bool(Any_to_DictDup(d)[a]!= from_none())
}

function Dict_empty() : Dict;
axiom [emptydict_def]: forall k: Any :: {Dict_get_func (Dict_empty(),k)} Dict_get_func (Dict_empty(),k) == from_none();

procedure Dict_set (d: Any, k: Any, v: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_Dict(d)) {
    error := NoError();
    ret := from_Dict(Dict_set_func (Dict_from_DictDup(Any_to_DictDup(d)), k , v));
  } else
  {
    error := TypeError("Not a Dict type");
    ret := d;
  }
};

procedure Dict_get (d: Any, k: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_Dict(d)) {
    ret := Dict_get_func (Dict_from_DictDup(Any_to_DictDup(d)), k);
    if (!Any..isfrom_none(ret))
    {
      error := IndexError("Key not in Dict");
    } else
    {
      error := NoError();
    }
  } else
  {
    error := TypeError("Not a Dict type");
    ret := from_none();
  }
};

procedure List_get (l: Any, k: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_ListAny(l) && Any..isfrom_int(k)) {
    if (Any..as_int(k) < List_len(Any..as_ListAny(l)))
    {
      ret := List_get_func (Any..as_ListAny(k), Any..as_int(k));
      error := NoError();
    }
    else
    {
      error := IndexError("Index out of bound");
      ret:= from_none();
    }

  } else
  {
    error := TypeError("List index type error");
    ret := from_none();
  }
};

procedure Any_get (l: Any, k: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_ListAny(l)){
    call ret, error := List_get (l,k);
  }
  else { if (Any..isfrom_Dict(l))
  {
    call ret, error := Dict_get (l,k);
  }
  else {
    error := TypeError("Undefined subscription type");
    ret := from_none();
  }
  }
};

procedure Dummy () returns ()
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
};

type kwargs := Map string Any;
//Dictionary functions
function kwargs_empty() : kwargs;
axiom [kwargs_empty_def]: forall k: string :: {kwargs_empty() [k]} kwargs_empty()[k] == from_none();
function kwargs_set (kwa: kwargs, k: string, v: Any) : kwargs {
  kwa[k:= v]
}
function kwargs_get (kwa: kwargs, k: string) : Any {
  kwa[k]
}
function kwargs_contains (d: kwargs, k: string) : bool {
  kwargs_get (d,k) != from_none()
}


function int_to_real (i: int) : real;
inline function bool_to_int (b: bool) : int {if b then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

function string_repeat (s: string, i: int) : string;

// Unary operations
procedure PNeg (v: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v))
  {
    ret:= from_int(- bool_to_int(Any..as_bool(v)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v))
  {
    ret:= from_int(- Any..as_int(v));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v))
  {
    ret:= from_float(- Any..as_float(v));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}
};

procedure PNot (v: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v))
  {
    ret:= from_bool(!(Any..as_bool(v)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v))
  {
    ret:= from_bool(!(Any..as_int(v) == 0));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v))
  {
    ret:= from_bool(!(Any..as_float(v) == 0.0));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v))
  {
    ret:= from_bool(!(Any..as_string(v) == ""));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v))
  {
    ret:= from_bool(!(List_len(Any..as_ListAny(v)) == 0));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}
};


//Binary operations
function string_lt (s1: string, s2: string) : bool;
function string_le (s1: string, s2: string) : bool;
function string_gt (s1: string, s2: string) : bool;
function string_ge (s1: string, s2: string) : bool;

procedure PAdd (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) + bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) + bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) + bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) + int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v1))
  {
    ret:= from_string(str.concat(Any..as_string(v1),Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}
};



procedure PSub (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) - bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) - Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) - bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) - Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) - bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) - Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) - Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) - int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) - Any..as_float(v2));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}
};

procedure PMul (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) * bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) * Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) * bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) * bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_string(v2))
  {
    ret:= if Any..as_bool(v1) then v2 else from_string("");
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_bool(v2))
  {
    ret:= if Any..as_bool(v2) then v1 else from_string("");
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) + int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_string(v2))
  {
    ret:= from_string(string_repeat(Any..as_string(v2), Any..as_int(v1)));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_int(v2))
  {
    ret:= from_string(string_repeat(Any..as_string(v1), Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_repeat(Any..as_ListAny(v2), Any..as_int(v1)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_int(v2))
  {
    ret:= from_ListAny(List_repeat(Any..as_ListAny(v1), Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_string(str.concat(Any..as_string(v1),Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}}}}}}
};

procedure PLt (v1: Any, v2: Any) returns (ret: bool, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) < bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) < Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_int(v1) < bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= bool_to_real(Any..as_bool(v1)) < Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_float(v1) < bool_to_real(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_int(v1) < Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= int_to_real(Any..as_int(v1)) < Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_float(v1) < int_to_real(Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= Any..as_float(v1) < Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= string_lt(Any..as_string(v1), Any..as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_lt(Any..as_ListAny(v1),Any..as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}
};

procedure PLe (v1: Any, v2: Any) returns (ret: bool, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) <= bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) <= Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_int(v1) <= bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= bool_to_real(Any..as_bool(v1)) <= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_float(v1) <= bool_to_real(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_int(v1) <= Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= int_to_real(Any..as_int(v1)) <= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_float(v1) <= int_to_real(Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= Any..as_float(v1) <= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= string_le(Any..as_string(v1), Any..as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_le(Any..as_ListAny(v1),Any..as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := UndefinedError("Operand Type is not defined");
  }
  }}}}}}}}}}
};


procedure PGt (v1: Any, v2: Any) returns (ret: bool, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) > bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) > Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_int(v1) > bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= bool_to_real(Any..as_bool(v1)) > Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_float(v1) > bool_to_real(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_int(v1) > Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= int_to_real(Any..as_int(v1)) > Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_float(v1) > int_to_real(Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= Any..as_float(v1) > Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= string_gt(Any..as_string(v1), Any..as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_gt(Any..as_ListAny(v1),Any..as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}
};

procedure PGe (v1: Any, v2: Any) returns (ret: bool, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) >= bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= bool_to_int(Any..as_bool(v1)) >= Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_int(v1) >= bool_to_int(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= bool_to_real(Any..as_bool(v1)) >= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= Any..as_float(v1) >= bool_to_real(Any..as_bool(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_int(v1) >= Any..as_int(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= int_to_real(Any..as_int(v1)) >= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= Any..as_float(v1) >= int_to_real(Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= Any..as_float(v1) >= Any..as_float(v2);
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= string_ge(Any..as_string(v1), Any..as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_ge(Any..as_ListAny(v1),Any..as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}
};


procedure PIn (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_Dict(v2))
  {
    ret:= Any_in_Dict(v1, v2);
    error := NoError ();
  }
  else { if (Any..isfrom_ListAny(v2))
  {
    ret := from_bool(List_contains(Any..as_ListAny(v2), v1));
    error := NoError ();
  }
  else {
    ret := from_bool(false);
    error := UndefinedError ("Operand type not supported");
  }
  }
};

function PEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) == normalize_any (v'))
}



#end

--#eval verify "cvc5" CoreTypePrelude
--#eval boogieTypePrelude.format

def PyOps := ["PNot", "PNeg", "PAdd", "PMul", "PSub", "PLt", "PLe", "PGt", "PGe", "PIn"]

def Core.Typeprelude : Core.Program :=
   Core.getProgram Strata.CoreTypePrelude |>.fst

end Strata
