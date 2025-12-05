/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Verifier

namespace Strata

def boogieTypePrelude :=
#strata
program Boogie;

//Generic tag for List
type List_tag;
const CONS : List_tag;
const NIL : List_tag;
axiom [list_tag_unique]: CONS != NIL;

//Will be merged with BoogiePrelude.lean
type Error;
function Error_message (s: string): Error;

// Value and ListValue types
type Value;
type ListValue;
// Constructors
function Value_bool (b : bool) : (Value);
function Value_int (i : int) : (Value);
function Value_float (f : real) : (Value);
function Value_str (s : string) : (Value);
function Value_none() : (Value);
function Value_Exception (e : Error): (Value);
function Value_List (lv : ListValue) : (Value);
function ListValue_nil() : (ListValue);
function ListValue_cons(x0 : Value, x1 : ListValue) : (ListValue);
//Tags
function ListValue_tag (l: ListValue) : List_tag;
axiom [ListValue_tag_nil_def]: (ListValue_tag (ListValue_nil()) == NIL);
axiom [ListValue_tag_cons_def]: (forall v: Value, vs: ListValue ::{ListValue_cons(v, vs)} (ListValue_tag (ListValue_cons(v, vs)) == CONS));

// Types of Value
type ValueType;
type ListValueType;
const BOOL : ValueType;
const INT : ValueType;
const FLOAT : ValueType;
const STR : ValueType;
const NONE : ValueType;
const EXCEPTION : ValueType;
//Uniqueness axioms
axiom [unique_ValueType_bool]: BOOL != INT && BOOL != FLOAT && BOOL != STR && BOOL != NONE && BOOL != EXCEPTION;
axiom [unique_ValueType_int]: INT != STR && INT != FLOAT && INT != NONE && INT != EXCEPTION;
axiom [unique_ValueType_float]: FLOAT != STR && FLOAT != NONE && FLOAT != EXCEPTION;
axiom [unique_ValueType_str]: STR != NONE && STR != EXCEPTION;
axiom [unique_ValueType_none]: NONE != EXCEPTION;
//Eq axioms
axiom [value_int_eq]: forall i: int, j: int :: {Value_int(i) == Value_int(j)} (Value_int(i) == Value_int(j)) == (i == j);
axiom [value_bool_eq]: forall b1: bool, b2: bool :: {Value_bool(b1) == Value_bool(b2)} (Value_bool(b1) == Value_bool(b2)) == (b1 == b2);
axiom [value_float_eq]: forall r1: real, r2: real :: {Value_float(r1) == Value_float(r2)} (Value_float(r1) == Value_float(r2)) == (r1 == r2);
axiom [value_str_eq]: forall s1: string, s2: string :: {Value_str(s1) == Value_str(s2)} (Value_str(s1) == Value_str(s2)) == (s1 == s2);


//Constructors and tag functions of ListType
function ListType_nil() : (ListValueType);
function ListType_cons(x0 : ValueType, x1 : ListValueType) : (ListValueType);
function ValueType_List (l: ListValueType) : ValueType;
function ListValueType_tag (l: ListValueType) : List_tag;
axiom [ListValueType_tag_nil_def]: (ListValueType_tag (ListType_nil()) == NIL);
axiom [ListValueType_tag_cons_def]: (forall t: ValueType, ts: ListValueType ::{ListType_cons(t, ts)} (ListValueType_tag (ListType_cons(t, ts)) == CONS));
function isList (v: Value): bool;


// TypeOf and TypesOf functions
function TypeOf (v : Value) : (ValueType);
function TypesOf (v: ListValue) : ListValueType;
// Definitions
axiom [TypesOf_nil_def]: (TypesOf(ListValue_nil()) == ListType_nil());
axiom [TypesOf_cons_def]: (forall v: Value, vs: ListValue ::{ListValue_cons(v, vs)} (TypesOf(ListValue_cons(v, vs)) == ListType_cons(TypeOf(v), TypesOf(vs))));
axiom [TypeOf_list_def]: (forall l: ListValue ::{Value_List(l)} (TypeOf(Value_List(l)) ==  ValueType_List(TypesOf(l))));
axiom [TypeOf_ret_set]: (forall v: Value :: {TypeOf(v)} ((TypeOf(v) == BOOL) || (TypeOf(v) == INT) || (TypeOf(v) == FLOAT) || (TypeOf(v) == STR) || (TypeOf(v) == NONE) || (TypeOf(v) == EXCEPTION)) || isList(v));
axiom [TypeOf_bool_constr]: (forall b: bool :: {TypeOf(Value_bool(b))} ((TypeOf(Value_bool(b)) == BOOL)));
axiom [TypeOf_int_constr]: (forall i: int :: {Value_int(i)} ((TypeOf(Value_int(i)) == INT)));
axiom [TypeOf_float_constr]: (forall f: real :: {Value_float(f)} ((TypeOf(Value_float(f)) == FLOAT)));
axiom [TypeOf_str_constr]: (forall s: string :: {Value_str(s)} ((TypeOf(Value_str(s)) == STR)));
axiom [TypeOf_list_constr]: (forall l: ListValue :: {Value_List(l)} ((TypeOf(Value_List(l)) == ValueType_List(TypesOf(l)))));
axiom [TypeOf_exception_constr]: (forall e: Error :: {Value_Exception(e)} ((TypeOf(Value_Exception(e)) == EXCEPTION)));
axiom [TypeOf_none_constr]: (((TypeOf(Value_none()) == NONE)));

axiom [isList_def]: (forall l: ListValue :: {Value_List(l)} (isList(Value_List(l))));
axiom [list_neq_single_type]: forall v: Value :: {} ! ((TypeOf(v) == BOOL) || (TypeOf(v) == INT) || (TypeOf(v) == FLOAT) || (TypeOf(v) == STR) || (TypeOf(v) == NONE) || (TypeOf(v) == EXCEPTION)) == (isList(v));
axiom [list_neq_single_type']: forall l: ListValue :: {Value_List(l)} TypeOf(Value_List(l))!=BOOL && TypeOf(Value_List(l))!=INT && TypeOf(Value_List(l))!=FLOAT && TypeOf(Value_List(l))!=STR && TypeOf(Value_List(l))!=NONE && TypeOf(Value_List(l))!=EXCEPTION;

// isSubType functions
function isSubType (t1: ValueType, t2: ValueType) : bool;
function isSubTypes (t1: ListValueType, t2: ListValueType) : bool;
//Definitions
axiom [isSubTypes_nil_def]: (isSubTypes(ListType_nil(), ListType_nil()));
axiom [not_isSubTypes_nil]: forall ty: ValueType, l: ListValueType :: !isSubTypes(ListType_nil(), ListType_cons(ty,l));
axiom [not_isSubTypes_nil']: forall ty: ValueType, l: ListValueType :: !isSubTypes(ListType_cons(ty,l), ListType_nil());
axiom [isSubTypes_cons_def]: (forall t: ValueType, ts: ListValueType, t': ValueType, ts': ListValueType  ::{ListType_cons(t, ts), ListType_cons(t', ts')} isSubTypes(ListType_cons(t, ts), ListType_cons(t', ts')) == (isSubType(t, t') && isSubTypes(ts, ts')));
axiom [isSubType_list_def]: (forall l: ListValueType, l': ListValueType :: {ValueType_List(l), ValueType_List(l')} (isSubType(ValueType_List(l), ValueType_List(l')) == isSubTypes(l, l')));
axiom [bool_substype_int]: (isSubType(BOOL, INT));
axiom [int_substype_float]: (isSubType(INT, FLOAT));
axiom [not_isSubstype_string]: (forall t: ValueType ::{} (t == STR || (!isSubType(STR, t) && !isSubType(t,STR))));
axiom [not_isSubstype_none]: (forall t: ValueType ::{} (t == NONE || (!isSubType(NONE, t) && !isSubType(t,NONE))));
axiom [not_isSubstype_exception]: (forall t: ValueType ::{} (t == EXCEPTION || (!isSubType(EXCEPTION, t) && !isSubType(t, EXCEPTION))));
// Supporting lemmas
axiom [isSubtype_rfl]: (forall t: ValueType::{isSubType (t,t)} (isSubType (t,t)));
axiom [isSubtype_mono]: (forall t1: ValueType, t2: ValueType ::{} (!isSubType (t1,t2) || (t1 == t2 || !isSubType(t2,t1))) );
axiom [isSubtype_trans]: (forall t1: ValueType, t2: ValueType, t3: ValueType::{} (!(isSubType(t1, t2) && isSubType(t2, t3)) || isSubType(t1, t3)));


// isInstance function:
function isInstance (v: Value, vt: ValueType) : bool;
axiom [isInstance_of_isSubtype]: (forall v: Value, t: ValueType::{isInstance(v,t)} (isInstance(v,t) == isSubType(TypeOf(v), t)));

function is_IntReal (v: Value) : bool;
function Value_real_to_int (v: Value) : int;
// to be extended
function normalize_value (v : Value) : Value {
  if v == Value_bool(true) then Value_int(1)
  else (if v == Value_bool(false) then Value_int(0) else
        if TypeOf(v) == FLOAT && is_IntReal(v) then Value_int(Value_real_to_int(v)) else
        v)
}

// ListValue functions
function List_contains (l : ListValue, x: Value) : bool;
function List_len (l : ListValue) : int;
function List_extend (l1 : ListValue, l2: ListValue) : ListValue;
function List_append (l: ListValue, x: Value) : ListValue;
function List_index (l : ListValue, i : int) : Value;
function List_reverse (l: ListValue) : ListValue;

//List function axioms
axiom [List_contains_nil_def]: (forall x : Value ::{List_contains(ListValue_nil(), x)} !List_contains(ListValue_nil(), x));
axiom [List_contains_cons_def]: (forall x : Value, h : Value, t : ListValue ::{} List_contains(ListValue_cons(h,t),x) == ((normalize_value(x)==normalize_value(h)) || List_contains(t, x)));
axiom [List_len_nil_def]: (List_len (ListValue_nil()) == 0);
axiom [List_len_cons_def]: (forall h : Value, t : ListValue ::{} (List_len (ListValue_cons(h,t)) == 1 + List_len(t)));
axiom [List_len_nonneg]: forall l: ListValue :: List_len(l) >= 0 ;
axiom [List_extend_nil_def]: (forall l1: ListValue ::{List_extend (l1, ListValue_nil())} (List_extend (l1, ListValue_nil()) == l1));
axiom [List_nil_extend_def]: (forall l1: ListValue ::{List_extend (ListValue_nil(), l1)} (List_extend (ListValue_nil(), l1) == l1));
axiom [List_cons_extend_def]: (forall h: Value, t: ListValue, l2: ListValue  ::{} (List_extend (ListValue_cons(h,t), l2) == ListValue_cons(h, List_extend(t,l2))));
axiom [List_cons_extend_contains]: (forall x: Value, l1: ListValue, l2: ListValue  ::{List_contains (List_extend(l1,l2), x)} (List_contains (List_extend(l1,l2), x) == List_contains (l1,x) || List_contains(l2,x)));
axiom [List_cons_extend_contains_symm]: (forall x: Value, l1: ListValue, l2: ListValue  ::{List_contains (List_extend(l1,l2), x)} (List_contains (List_extend(l1,l2), x) == List_contains (List_extend(l2,l1), x)));
axiom [List_len_extend]: (forall l1: ListValue, l2: ListValue  ::{List_len (List_extend(l1,l2))} (List_len (List_extend(l1,l2)) == List_len (l1) + List_len(l2)));
axiom [List_index_nil]: (forall i : int ::{List_index (ListValue_nil(), i)} (List_index (ListValue_nil(), i)) == Value_Exception(Error_message("index out of bound")));
axiom [List_index_zero]: (forall h : Value, t : ListValue ::{List_index (ListValue_cons(h,t), 0)} (List_index (ListValue_cons(h,t), 0)) == h);
axiom [List_index_ind]: (forall h : Value, t : ListValue, i : int ::{List_index (ListValue_cons(h,t), i)} (!(i>0) || (List_index (ListValue_cons(h,t), i)) == List_index (t, i - 1)));
axiom [List_index_contains]: forall l: ListValue, i: int, x: Value :: {} !(List_index(l,i) == x) || List_contains(l,x);
axiom [List_index_ok]: forall l: ListValue, i: int:: {List_index(l,i)} ((List_index(l,i)) != Value_Exception(Error_message("index out of bound"))) == (i < List_len(l));
axiom [List_extend_get_shift]: forall l1: ListValue, l2: ListValue, i: int :: List_index(l1, i) == List_index(List_extend(l2,l1), i + List_len(l2));
axiom [List_extend_assoc]: forall l1: ListValue, l2: ListValue, l3: ListValue :: List_extend(List_extend(l1,l2), l3) == List_extend(l1,List_extend(l2,l3));
axiom [List_append_def]: forall l: ListValue, x: Value :: List_append(l,x) == List_extend(l, ListValue_cons(x, ListValue_nil()));
axiom [List_reverse_def_nil]: List_reverse(ListValue_nil()) == ListValue_nil();
axiom [List_reverse_def_cons]: forall h: Value, t: ListValue:: {List_reverse(ListValue_cons(h,t))} List_reverse(ListValue_cons(h,t)) == List_append(List_reverse(t), h);
axiom [List_reverse_len]: forall l: ListValue :: {List_len(List_reverse(l))} List_len(l) == List_len(List_reverse(l));
axiom [List_reverse_index]: forall l: ListValue, i: int :: List_index(l, i) == List_index(List_reverse(l), List_len(l)-1-i);
axiom [List_reverse_extend]: forall l1: ListValue, l2: ListValue :: {List_reverse(List_extend(l1,l2))} List_reverse(List_extend(l1,l2)) == List_extend(List_reverse(l2), List_reverse(l1));
axiom [List_reverse_contain]: forall l: ListValue, v: Value :: {List_contains (List_reverse(l), v)} List_contains (List_reverse(l), v) == List_contains(l,v);

// Dict type
type Dict;
const EMPTYDICT : Dict;


//Dictionary functions
function Dict_insert (d: Dict, k: Value, v: Value) : Dict;
function Dict_get (d: Dict, k: Value) : Value;
function Dict_remove (d: Dict, k: Value) : Dict;
inline function Dict_contains (d: Dict, k: Value) : bool {
  Dict_get (d,k) != Value_none()
}


//function upType (v: Value) : Value;

//Dictionary axioms
axiom [emptydict_def]: forall k: Value :: Dict_get(EMPTYDICT, k) == Value_none();
axiom [Dict_insert_def1']: forall k: Value, v: Value, d: Dict ::{Dict_insert(d,k,v)} Dict_get(Dict_insert(d,k,v), normalize_value(k)) == v;
axiom [Dict_insert_def2]: forall k: Value, k': Value, v: Value, d: Dict ::{Dict_insert(d,k,v)} (normalize_value(k) == normalize_value(k')) || Dict_get(Dict_insert(d,k,v), k') == Dict_get(d,k');
axiom [Dict_get_upType]: forall k: Value, d: Dict ::{Dict_get(d,k)} Dict_get(d, k) == Dict_get(d, normalize_value(k));
axiom [Dict_remove_def1]: forall k: Value, d: Dict ::{Dict_remove(d,k)} Dict_get(Dict_remove(d,k), normalize_value(k)) == Value_none();
axiom [Dict_remove_def2]: forall k: Value, k': Value, d: Dict ::{Dict_remove(d,k)} (normalize_value(k) == normalize_value(k')) || Dict_get(Dict_remove(d,k), k') == Dict_get(d,k');


// List of pairs of Value, used to construct Dict
type DictList;
// Constructor
function DictList_nil(): DictList;
function DictList_cons(k: Value, v: Value, d: DictList): DictList;
//Tag and tag functions
type DictListTag;
function DictList_tag (dl: DictList) : DictListTag;
const DICTLISTNIL : DictListTag;
const DICTLISTCONS : DictListTag;
axiom [DistListTag_unique]: DICTLISTCONS != DICTLISTNIL;
axiom [DistListTag_nil_def]: DictList_tag (DictList_nil()) == DICTLISTNIL;
axiom [DistListTag_cons_def]: forall k: Value, v: Value, d: DictList ::{DictList_cons(k,v,d)} DictList_tag (DictList_cons(k,v,d)) == DICTLISTCONS;
// as a constructor for Dict
function Dict_from_DicList (l : DictList) : Dict;
function Dict_from_DicList_rev (l : DictList, acc: Dict) : Dict;
axiom [Dict_from_DicList_rev_nil]: forall acc: Dict ::  Dict_from_DicList_rev(DictList_nil(), acc) == acc;
axiom [Dict_from_DicList_rev_cons]: forall k: Value, v: Value, d: DictList, acc: Dict ::  Dict_from_DicList_rev(DictList_cons(k,v,d), acc) == Dict_from_DicList_rev(d,Dict_insert(acc, k, v));
axiom [Dict_from_DicList_def]: forall dl: DictList:: {Dict_from_DicList(dl)} Dict_from_DicList(dl) == Dict_from_DicList_rev(dl, EMPTYDICT);
axiom [remove_insert_eq]: forall d: Dict, k: Value, v: Value:: !(Dict_get(d,k) == v) || (Dict_insert(Dict_remove(d,k), k, v)) == d;

//Binary op function
function int_to_real (i: int) : real;
function str_repeat (s: string, i: int) : string;
function Py_add (v1: Value, v2: Value) : (Value);
function Py_sub (v1: Value, v2: Value) : (Value);
function Py_mul (v1: Value, v2: Value) : (Value);
inline function bool_to_int (b: bool) : (int) {if b then 1 else 0}
inline function bool_to_real (b: bool) : (real) {if b then 1.0 else 0.0}


axiom [Py_add_ints]: (forall i1: int, i2: int :: {Value_int(i1), Value_int(i2)} ((Py_add(Value_int(i1), Value_int(i2)) == Value_int(i1 + i2))));
axiom [Py_add_floats]: (forall f1: real, f2: real :: {Value_float(f1), Value_float(f2)} ((Py_add(Value_float(f1), Value_float(f2)) == Value_float(f1 + f2))));
axiom [Py_add_bools]: (forall b1: bool, b2: bool :: {Value_bool(b1), Value_bool(b2)} ((Py_add(Value_bool(b1), Value_bool(b2)) == Value_int(bool_to_int(b1) + bool_to_int(b2)))));
axiom [Py_add_int_bool]: (forall i: int, b: bool :: {Value_int(i), Value_bool(b)} ((Py_add(Value_int(i), Value_bool(b)) == Value_int(i + bool_to_int(b)))));
axiom [Py_add_bool_int]: (forall b: bool, i: int :: {Value_bool(b), Value_int(i)} ((Py_add(Value_bool(b), Value_int(i)) == Value_int(bool_to_int(b) + i))));
axiom [Py_add_int_float]: (forall i: int, r: real :: {Value_int(i), Value_float(r)} ((Py_add(Value_int(i), Value_float(r)) == Value_float(r + int_to_real(i)))));
axiom [Py_add_float_int]: (forall r: real, i: int :: {Value_float(r), Value_int(i)} ((Py_add(Value_float(r), Value_int(i)) == Value_float(int_to_real(i) + r))));
axiom [Py_add_float_bool]: (forall r: real, b: bool :: {Value_float(r), Value_bool(b)} ((Py_add(Value_float(r), Value_bool(b)) == Value_float(r + bool_to_real(b)))));
axiom [Py_add_bool_float]: (forall b: bool, r: real :: {Value_bool(b), Value_float(r)} ((Py_add(Value_bool(b), Value_float(r)) == Value_float(bool_to_real(b) + r))));
axiom [Py_add_none]: (forall v: Value :: {} ((Py_add(v, Value_none()) == Value_Exception(Error_message("Operand is None")))));
axiom [Py_none_add]: (forall v: Value :: {} ((Py_add(Value_none(), v) == Value_Exception(Error_message("Operand is None")))));
axiom [Py_add_exception]: (forall v: Value, e: Error :: {Value_Exception(e)} ((Py_add(v, Value_Exception(e)) == Value_Exception(Error_message("Operand is Exception")))));
axiom [Py_exception_add]: (forall v: Value, e: Error :: {Value_Exception(e)} ((Py_add(Value_Exception(e), v) == Value_Exception(Error_message("Operand is Exception")))));
axiom [Py_add_strs]: (forall s1: string, s2: string :: {Value_str(s1), Value_str(s2)} ((Py_add(Value_str(s1), Value_str(s2)) == Value_str(str.concat(s1, s2)))));
axiom [Py_add_str_int]: (forall s: string, i: int :: {Value_str(s), Value_int(i)} ((Py_add(Value_str(s), Value_int(i)) == Value_Exception(Error_message("Cannot add string to int")))));
axiom [Py_add_int_str]: (forall s: string, i: int :: {Value_str(s), Value_int(i)} ((Py_add(Value_int(i), Value_str(s)) == Value_Exception(Error_message("Cannot add string to int")))));
axiom [Py_add_str_bool]: (forall s: string, b: bool :: {Value_str(s), Value_bool(b)} ((Py_add(Value_str(s), Value_bool(b)) == Value_Exception(Error_message("Cannot add string to bool")))));
axiom [Py_add_bool_str]: (forall s: string, b: bool :: {Value_str(s), Value_bool(b)} ((Py_add(Value_bool(b), Value_str(s)) == Value_Exception(Error_message("Cannot add bool to string")))));

axiom [Py_mul_ints]: (forall i1: int, i2: int :: {Value_int(i1), Value_int(i2)} ((Py_mul(Value_int(i1), Value_int(i2)) == Value_int(i1 * i2))));
axiom [Py_mul_bools]: (forall b1: bool, b2: bool :: {Value_bool(b1), Value_bool(b2)} ((Py_mul(Value_bool(b1), Value_bool(b2)) == Value_int(bool_to_int(b1) * bool_to_int(b2)))));
axiom [Py_mul_int_bool]: (forall i: int, b: bool :: {Value_int(i), Value_bool(b)} ((Py_mul(Value_int(i), Value_bool(b)) == Value_int(i * bool_to_int(b)))));
axiom [Py_mul_bool_int]: (forall b: bool, i: int :: {Value_bool(b), Value_int(i)} ((Py_mul(Value_bool(b), Value_int(i)) == Value_int(bool_to_int(b) * i))));
axiom [Py_mul_none]: (forall v: Value :: {} ((Py_mul(v, Value_none()) == Value_Exception(Error_message("Operand is None")))));
axiom [Py_mul_add]: (forall v: Value :: {} ((Py_mul(Value_none(), v) == Value_Exception(Error_message("Operand is None")))));
axiom [Py_mul_exception]: (forall v: Value, e: Error :: {Value_Exception(e)} ((Py_mul(v, Value_Exception(e)) == Value_Exception(Error_message("Operand is Exception")))));
axiom [Py_exception_mul]: (forall v: Value, e: Error :: {Value_Exception(e)} ((Py_mul(Value_Exception(e), v) == Value_Exception(Error_message("Operand is Exception")))));
axiom [Py_mul_strs]: (forall s1: string, s2: string :: {Value_str(s1), Value_str(s2)} ((Py_mul(Value_str(s1), Value_str(s2)) == Value_Exception(Error_message("Cannot multiply two strings")))));
axiom [Py_mul_str_int]: (forall s: string, i: int :: {Value_str(s), Value_int(i)} ((Py_add(Value_str(s), Value_int(i)) == Value_str(str_repeat(s, i)))));
axiom [Py_mul_int_str]: (forall s: string, i: int :: {Value_str(s), Value_int(i)} ((Py_add(Value_int(i), Value_str(s)) == Value_str(str_repeat(s, i)))));
axiom [Py_mul_str_bool]: (forall s: string, b: bool :: {Value_str(s), Value_bool(b)} ((Py_add(Value_str(s), Value_bool(b)) == Value_str(if b then s else ""))));
axiom [Py_mul_bool_str]: (forall s: string, b: bool :: {Value_str(s), Value_bool(b)} ((Py_add(Value_bool(b), Value_str(s)) ==  Value_str(if b then s else ""))));


//Testing
procedure list_functions_test() returns ()
{
  var l1: ListValue, l2: ListValue;
  l1 := ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3), ListValue_nil())));
  assert [index_1]: List_index(l1,1) == Value_int(2);
  assert [contain_true]: List_contains(l1, Value_bool(true));
  assert [ValueEq]: !(Value_int(4) == Value_int(3));
  assert [normalize_value]: !(normalize_value(Value_int(4)) == Value_int(3));
  assert [contain_3]: List_contains(l1, Value_int(2));
};

procedure list_generic_test() returns () {
  var l1: ListValue;
  assert [contains_append]: forall l: ListValue, x: Value :: List_contains(List_append(l,x), x);
  assert [len_append]: forall l: ListValue, x: Value :: List_len(List_append(l,x)) == List_len(l) + 1;
  l1 := ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3), ListValue_nil())));
  assert [l1_contains_3]: List_contains (l1, Value_int(3));
  assert [l1l2_contains_3]: forall l2: ListValue :: List_contains (List_extend(l1, l2), Value_int(3));
  assert [revl1_contain_3]: List_contains (List_reverse(l1), Value_int(3));
  assert [rev_contain]: forall l: ListValue, v: Value :: List_contains (List_reverse(l), v) == List_contains(l,v);
  assert [l1r_l2_contains_3]: forall l2: ListValue :: List_contains (List_extend(List_reverse(l1), l2), Value_int(3));
  assert [l1r_l2_contains_3']: forall l2: ListValue :: List_contains (List_reverse(List_extend(List_reverse(l1), l2)), Value_int(3));
};


procedure simple_call(v1: Value, v2: Value) returns ()
  spec {
    requires [v1_type]: isInstance(v1, BOOL) || isInstance(v1, STR);
    requires [v2_type]: isInstance(v2, ValueType_List(ListType_cons(INT, ListType_cons(INT, ListType_nil()))));
  }
{};

procedure test() returns () {
  var ty1: ValueType, ty2: ValueType, tl: ValueType;
  ty1 := TypeOf(Value_int(5));
  ty2 := TypeOf(Value_bool(true));
  assert [subtype1]: isSubType(ty2,ty1);
  assert [subtypeList]: forall l: ListValueType :: isSubType (ValueType_List(ListType_cons(ty2, l)), ValueType_List(ListType_cons(ty1, l)));
  assert [subtypeList2]: forall l1: ListValueType, l2: ListValueType :: !(isSubTypes(l1,l2)) || isSubType (ValueType_List(ListType_cons(ty2, l1)), ValueType_List(ListType_cons(ty1, l2)));
};

procedure test_simple_call_argument_typecheck() returns () {
  var arg1: Value, arg2: Value;
  arg1 := Value_bool(true);
  arg2 := Value_List(ListValue_cons(Value_int(3), ListValue_cons (Value_bool(true), ListValue_nil())));
  assert [subtype_bool]: isInstance(arg1,BOOL);
  call simple_call(arg1, arg2);
};

procedure dict_functions_test () returns () {
  var d1: Dict, d2: Dict, d3: Dict;
  d1:= Dict_insert(EMPTYDICT, Value_int(1), Value_int(1));
  d2:= Dict_insert(d1, Value_bool(true), Value_int(2));
  assert [uptype]: normalize_value(Value_bool(true)) == Value_int(1);
  assert [uptype2]: normalize_value(Value_int(1)) == Value_int(1);
  assert [uptype3]: normalize_value(Value_str("fd")) == Value_str("fd");
  assert [get_1]: Dict_get(d2, Value_int(1)) == Value_int(2);
};


procedure test_dict_listconstructor () returns () {
  var d: Dict, dl: DictList, d2: Dict, d3: Dict;
  dl := DictList_cons(Value_bool(true), Value_int(10), DictList_cons(Value_int(1), Value_int(11), DictList_nil()));
  d := Dict_from_DicList(dl);
  assert [get_1]: Dict_get(d, Value_int(1)) == Value_int(11);
  assert [get_true]: Dict_get(d, Value_bool(true)) == Value_int(11);
  d2 := Dict_insert(Dict_insert(d, Value_int(10), Value_int(8)), Value_int(1), Value_str("abc"));
  assert [get_true2]: Dict_get(d2, Value_bool(true)) == Value_str("abc");
  d3 := Dict_remove(d2, Value_bool(true));
  assert [get_1_d3]: Dict_get(d3, Value_int(1)) == Value_none();
  assert [ncontain]: !Dict_contains(d3, Value_bool(true));
};

procedure forall_dict_test () returns () {
  assert [ncontain_general]: forall d: Dict, k: Value :: !Dict_contains(Dict_remove(d,k), k);
  assert [ncontain_general']: forall d: Dict, k: Value :: !Dict_contains(Dict_remove(d,normalize_value(k)), k);
  assert [contain_general]: forall d: Dict, k: Value, v: Value :: (v == Value_none()) || Dict_contains(Dict_insert(d,k,v), k);
  assert [remove_insert]: forall d: Dict, k: Value, v: Value, k': Value :: !(Dict_get(d,k) == v) || Dict_get((Dict_insert(Dict_remove(d,k), k, v)), k') == Dict_get(d, k');
};

#end

#eval verify "cvc5" boogieTypePrelude


def Boogie.prelude : Boogie.Program :=
   Boogie.getProgram Strata.boogieTypePrelude |>.fst

end Strata
