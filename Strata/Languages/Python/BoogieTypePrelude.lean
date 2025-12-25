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
axiom [all_list_tag]: forall lt: List_tag :: lt == CONS || lt == NIL;

//Will be merged with BoogiePrelude.lean
type Error;
function Error_message (s: string): Error;
type Error_tag;
const OK : Error_tag;
const ERR : Error_tag;
axiom [error_tag_unique]: OK != ERR;
axiom [all_error_tag]: forall et: Error_tag :: et == OK || et == ERR;

// Value and ListValue types
type Value;
type ListValue;

// Class type
type Class;
type AttributeValues := Map string Value;
type ClassInstance;

// Constructors
function Value_bool (b : bool) : Value;
function Value_int (i : int) : Value;
function Value_float (f : real) : Value;
function Value_str (s : string) : Value;
function Value_none() : Value;
function Value_exception (e : Error): Value;
function Value_list (lv : ListValue) : Value;
function Value_class (ci: ClassInstance) : Value;

function ListValue_nil() : ListValue;
function ListValue_cons(x0 : Value, x1 : ListValue) : ListValue;
//Tags
function ListValue_tag (l: ListValue) : List_tag;
axiom [ListValue_tag_nil_def]: ListValue_tag (ListValue_nil()) == NIL;
axiom [ListValue_tag_cons_def]: forall v: Value, vs: ListValue ::{ListValue_cons(v, vs)} ListValue_tag (ListValue_cons(v, vs)) == CONS;

// Types of Value
type ValueType;
type ListValueType;
const BOOL : ValueType;
const INT : ValueType;
const FLOAT : ValueType;
const STR : ValueType;
const NONE : ValueType;
const EXCEPTION : ValueType;
function ValueType_class(c: Class): ValueType;

function isListValueType (t: ValueType): bool;
function isClassValueType (t: ValueType): bool;
axiom [isClassType_def]: forall c: Class :: {isClassValueType(ValueType_class(c))} isClassValueType(ValueType_class(c));

function isList (v: Value): bool;
function isClassInstance (v: Value): bool;


//Uniqueness axioms
axiom [unique_ValueType_bool]: BOOL != INT && BOOL != FLOAT && BOOL != STR && BOOL != NONE && BOOL != EXCEPTION && !isListValueType(BOOL) && !(isClassValueType(BOOL));
axiom [unique_ValueType_int]: INT != STR && INT != FLOAT && INT != NONE && INT != EXCEPTION && !isListValueType(INT) && !(isClassValueType(INT));
axiom [unique_ValueType_float]: FLOAT != STR && FLOAT != NONE && FLOAT != EXCEPTION && !isListValueType(FLOAT) && !(isClassValueType(FLOAT));
axiom [unique_ValueType_str]: STR != NONE && STR != EXCEPTION && !isListValueType(STR) && !(isClassValueType(STR));
axiom [unique_ValueType_none]: NONE != EXCEPTION && !isListValueType(NONE) && !(isClassValueType(NONE));
axiom [unique_ValueType_exception]: !isListValueType(EXCEPTION) && !(isClassValueType(EXCEPTION));
axiom [classtype_ne_listtype]: forall t: ValueType :: {isListValueType (t), isClassValueType (t)} !(isListValueType (t) && isClassValueType (t));
axiom [all_ValueType_cases]: forall t: ValueType ::
  t == BOOL ||
  t == INT ||
  t == FLOAT ||
  t == STR ||
  t == NONE ||
  t == EXCEPTION ||
  isListValueType (t) ||
  isClassValueType (t);

//Eq axioms
axiom [value_int_eq]: forall i: int, j: int :: {Value_int(i) == Value_int(j)} (Value_int(i) == Value_int(j)) == (i == j);
axiom [value_bool_eq]: forall b1: bool, b2: bool :: {Value_bool(b1) == Value_bool(b2)} (Value_bool(b1) == Value_bool(b2)) == (b1 == b2);
axiom [value_float_eq]: forall r1: real, r2: real :: {Value_float(r1) == Value_float(r2)} (Value_float(r1) == Value_float(r2)) == (r1 == r2);
axiom [value_str_eq]: forall s1: string, s2: string :: {Value_str(s1) == Value_str(s2)} (Value_str(s1) == Value_str(s2)) == (s1 == s2);

//Constructors and tag functions of ListType
function ListType_nil() : (ListValueType);
function ListType_cons(x0 : ValueType, x1 : ListValueType) : ListValueType;
function ValueType_List (l: ListValueType) : ValueType;
function ListValueType_tag (l: ListValueType) : List_tag;
axiom [ListValueType_tag_nil_def]: ListValueType_tag (ListType_nil()) == NIL;
axiom [ListValueType_tag_cons_def]: forall t: ValueType, ts: ListValueType ::{ListType_cons(t, ts)} (ListValueType_tag (ListType_cons(t, ts)) == CONS);
axiom [isListValueType_def]: forall l: ListValueType ::{isListValueType(ValueType_List (l))} isListValueType(ValueType_List (l));

// TypeOf and TypesOf functions
function TypeOf (v : Value) : ValueType;
function TypesOf (v: ListValue) : ListValueType;
// Definitions
axiom [TypesOf_nil_def]: TypesOf(ListValue_nil()) == ListType_nil();
axiom [TypesOf_cons_def]: forall v: Value, vs: ListValue ::{ListValue_cons(v, vs)} TypesOf(ListValue_cons(v, vs)) == ListType_cons(TypeOf(v), TypesOf(vs));
axiom [TypeOf_list_def]: forall l: ListValue ::{Value_list(l)} TypeOf(Value_list(l)) ==  ValueType_List(TypesOf(l));
axiom [TypeOf_bool]: forall b: bool :: {TypeOf(Value_bool(b))} TypeOf(Value_bool(b)) == BOOL;
axiom [TypeOf_int]: forall i: int :: {Value_int(i)} TypeOf(Value_int(i)) == INT;
axiom [TypeOf_float]: forall f: real :: {Value_float(f)} TypeOf(Value_float(f)) == FLOAT;
axiom [TypeOf_str]: forall s: string :: {Value_str(s)} TypeOf(Value_str(s)) == STR;
axiom [TypeOf_exception]: forall e: Error :: {Value_exception(e)} TypeOf(Value_exception(e)) == EXCEPTION;
axiom [TypeOf_none]: TypeOf(Value_none()) == NONE;
axiom [TypeOf_list]: forall l: ListValue :: {Value_list(l)} TypeOf(Value_list(l)) == ValueType_List(TypesOf(l));

axiom [TypeOf_bool_exists]: forall v: Value :: {TypeOf(v) == BOOL} TypeOf(v) == BOOL ==> exists b: bool :: v == Value_bool(b);
axiom [TypeOf_int_exists]: forall v: Value :: {TypeOf(v) == INT} TypeOf(v) == INT ==> exists i: int :: v == Value_int(i);
axiom [TypeOf_float_exists]: forall v: Value :: {TypeOf(v) == FLOAT} TypeOf(v) == FLOAT ==> exists r: real :: v == Value_float(r);
axiom [TypeOf_string_exists]: forall v: Value :: {TypeOf(v) == STR} TypeOf(v) == STR ==> exists s: string :: v == Value_str(s);
axiom [TypeOf_exception_exists]: forall v: Value :: {TypeOf(v) == EXCEPTION} TypeOf(v) == EXCEPTION ==> exists e: Error :: v == Value_exception(e);
axiom [TypeOf_none']: forall v: Value :: {TypeOf(v) == NONE} (TypeOf(v) == NONE) == (v == Value_none()) ;
axiom [TypeOf_list_exists]: forall v: Value :: {isList(v)} isList(v) ==> exists l: ListValue :: v == Value_list(l);
axiom [TypeOf_class_exists]: forall v: Value :: {isClassInstance(v)} isClassInstance(v) ==> exists ci: ClassInstance :: v == Value_class(ci);

axiom [isList_def]: forall l: ListValue :: {Value_list(l)} isList(Value_list(l));
axiom [isList_def']: forall v: Value :: {isListValueType(TypeOf(v))} isList(v) == isListValueType(TypeOf(v));
axiom [isClassInstance_def]: forall ci: ClassInstance :: {Value_class(ci)} isClassInstance(Value_class(ci));
axiom [isClassInstance_def']: forall v: Value :: {isClassValueType(TypeOf(v))} isClassInstance(v) == isClassValueType(TypeOf(v));

// isSubType functions
function isSubType (t1: ValueType, t2: ValueType) : bool;
function isSubTypes (t1: ListValueType, t2: ListValueType) : bool;
//Definitions
axiom [isSubTypes_nil_def]: isSubTypes(ListType_nil(), ListType_nil());
axiom [not_isSubTypes_nil]: forall ty: ValueType, l: ListValueType :: !isSubTypes(ListType_nil(), ListType_cons(ty,l));
axiom [not_isSubTypes_nil']: forall ty: ValueType, l: ListValueType :: !isSubTypes(ListType_cons(ty,l), ListType_nil());
axiom [isSubTypes_cons_def]:forall t: ValueType, ts: ListValueType, t': ValueType, ts': ListValueType  ::{ListType_cons(t, ts), ListType_cons(t', ts')}
  isSubTypes(ListType_cons(t, ts), ListType_cons(t', ts')) == (isSubType(t, t') && isSubTypes(ts, ts'));
axiom [isSubType_list_def]: forall l: ListValueType, l': ListValueType :: {ValueType_List(l), ValueType_List(l')}
  isSubType(ValueType_List(l), ValueType_List(l')) == isSubTypes(l, l');
axiom [bool_substype_int]: isSubType(BOOL, INT);
axiom [int_substype_float]: isSubType(INT, FLOAT);
axiom [not_isSubstype_string]: forall t: ValueType ::{isSubType(STR, t), isSubType(t,STR)}
  t == STR || (!isSubType(STR, t) && !isSubType(t,STR));
axiom [not_isSubstype_none]: forall t: ValueType ::{isSubType(NONE, t), isSubType(NONE, t)}
  t == NONE || (!isSubType(NONE, t) && !isSubType(t,NONE));
axiom [not_isSubstype_exception]: forall t: ValueType ::{isSubType(EXCEPTION, t), isSubType(t, EXCEPTION)}
  t == EXCEPTION || (!isSubType(EXCEPTION, t) && !isSubType(t, EXCEPTION));
axiom [not_isSubstype_list]: forall t: ValueType, t': ValueType ::{isSubType(t, t')}
  ((isListValueType(t) && !isListValueType(t')) || (!isListValueType(t) && isListValueType(t'))) ==> (!isSubType(t, t') && !isSubType(t', t));
axiom [not_isSubstype_class_othertypes]: forall t: ValueType, t': ValueType ::{isSubType(t, t')}
  ((isClassValueType(t) && !isClassValueType(t')) || (!isClassValueType(t) && isClassValueType(t'))) ==> (!isSubType(t, t') && !isSubType(t', t));
axiom [not_isSubstype_class]: forall t: ValueType, c: Class ::{isSubType(ValueType_class(c), t), isSubType(t,ValueType_class(c))}
  t != ValueType_class(c) ==> (!isSubType(ValueType_class(c), t) && !isSubType(t,ValueType_class(c)));
// Supporting lemmas
axiom [isSubtype_rfl]: forall t: ValueType::{isSubType (t,t)} isSubType (t,t);
axiom [isSubtype_mono]: forall t1: ValueType, t2: ValueType ::{isSubType (t1,t2)} !isSubType (t1,t2) || (t1 == t2 || !isSubType(t2,t1));
axiom [isSubtype_trans]: forall t1: ValueType, t2: ValueType, t3: ValueType::{isSubType(t1, t2)} !(isSubType(t1, t2) && isSubType(t2, t3)) || isSubType(t1, t3);

// isInstance function:
function isInstance (v: Value, vt: ValueType) : bool;
axiom [isInstance_of_isSubtype]: forall v: Value, t: ValueType::{isInstance(v,t)} isInstance(v,t) == isSubType(TypeOf(v), t);

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
function List_get (l : ListValue, i : int) : Value;
function List_reverse (l: ListValue) : ListValue;
function List_index! (l: ListValue, v: Value): int;
function List_index (l: ListValue, v: Value): Value;
function List_repeat (l: ListValue, n: int): ListValue;
function List_insert (l: ListValue, i: int, v: Value): ListValue;
function List_remove (l: ListValue, v: Value): ListValue;
//TO BE done
function List_pop (l: ListValue, i: int): ListValue;


//List function axioms
axiom [List_contains_nil_def]: forall x : Value ::{List_contains(ListValue_nil(), x)}
  !List_contains(ListValue_nil(), x);
axiom [List_contains_cons_def]: forall x : Value, h : Value, t : ListValue ::{List_contains(ListValue_cons(h,t),x)}
  List_contains(ListValue_cons(h,t),x) == ((normalize_value(x)==normalize_value(h)) || List_contains(t, x));

axiom [List_len_nil_def]: List_len (ListValue_nil()) == 0;
axiom [List_len_cons_def]: forall h : Value, t : ListValue ::{List_len (ListValue_cons(h,t))}
  List_len (ListValue_cons(h,t)) == 1 + List_len(t);
axiom [List_len_nonneg]: forall l: ListValue :: {List_len(l)} List_len(l) >= 0 ;
axiom [List_nil_of_len_zero]: forall l: ListValue :: {List_len(l) == 0}
  (List_len(l) == 0) == (l == ListValue_nil());

axiom [List_extend_nil_def]: forall l1: ListValue ::{List_extend (l1, ListValue_nil())}
  List_extend (l1, ListValue_nil()) == l1;
axiom [List_nil_extend_def]: forall l1: ListValue ::{List_extend (ListValue_nil(), l1)}
  List_extend (ListValue_nil(), l1) == l1;
axiom [List_cons_extend_def]: forall h: Value, t: ListValue, l2: ListValue  ::{List_extend (ListValue_cons(h,t), l2)}
  List_extend (ListValue_cons(h,t), l2) == ListValue_cons(h, List_extend(t,l2));

axiom [List_cons_extend_contains]: forall x: Value, l1: ListValue, l2: ListValue  ::{List_contains (List_extend(l1,l2), x)}
  List_contains (List_extend(l1,l2), x) == (List_contains (l1,x) || List_contains(l2,x));
axiom [List_len_extend]: forall l1: ListValue, l2: ListValue  ::{List_len (List_extend(l1,l2))}
  List_len (List_extend(l1,l2)) == List_len (l1) + List_len(l2);
axiom [List_extend_assoc]: forall l1: ListValue, l2: ListValue, l3: ListValue :: {List_extend(List_extend(l1,l2), l3)}
  List_extend(List_extend(l1,l2), l3) == List_extend(l1,List_extend(l2,l3));

axiom [List_get_nil]: forall i : int ::{List_get (ListValue_nil(), i)}
  List_get (ListValue_nil(), i) == Value_exception(Error_message("index out of bound"));
axiom [List_get_zero]: forall h : Value, t : ListValue ::{List_get (ListValue_cons(h,t), 0)}
  List_get (ListValue_cons(h,t), 0) == h;
axiom [List_get_ind]: forall h : Value, t : ListValue, i : int ::{List_get (ListValue_cons(h,t), i)}
  (i > 0) ==> (List_get (ListValue_cons(h,t), i)) == List_get (t, i - 1);
axiom [List_get_contains]: forall l: ListValue, i: int, x: Value :: {List_contains(l,x), List_get(l,i)}
  (List_get(l,i) == x && TypeOf(x)!= EXCEPTION) ==> List_contains(l,x);
axiom [List_get_ok]: forall l: ListValue, i: int:: {List_get(l,i)}
  ((List_get(l,i)) != Value_exception(Error_message("index out of bound"))) == (i < List_len(l) && i >= 0);
axiom [List_get_ok']: forall l: ListValue, i: int:: {List_get(l,i)}
  (TypeOf(List_get(l,i)) != EXCEPTION) == (i < List_len(l) && i >= 0);
axiom [List_extend_get]: forall l1: ListValue, l2: ListValue, i: int :: {List_get(List_extend(l1,l2), i)}
  List_get(List_extend(l1,l2), i) == if i < List_len(l1) then List_get(l1, i) else List_get(l2, i - List_len(l1));

axiom [List_append_def]: forall l: ListValue, x: Value :: {List_append(l,x)}
  List_append(l,x) == List_extend(l, ListValue_cons(x, ListValue_nil()));

axiom [List_reverse_def_nil]: List_reverse(ListValue_nil()) == ListValue_nil();
axiom [List_reverse_def_cons]: forall h: Value, t: ListValue:: {List_reverse(ListValue_cons(h,t))}
  List_reverse(ListValue_cons(h,t)) == List_append(List_reverse(t), h);
axiom [List_reverse_len]: forall l: ListValue :: {List_len(List_reverse(l))}
  List_len(l) == List_len(List_reverse(l));
axiom [List_reverse_contain]: forall l: ListValue, v: Value :: {List_contains (List_reverse(l), v)}
  List_contains (List_reverse(l), v) == List_contains(l,v);
axiom [List_reverse_index]: forall l: ListValue, i: int :: {List_get(List_reverse(l), i)}
  List_get(List_reverse(l), i) == List_get(l, List_len(l)-1-i);
axiom [List_reverse_reverse]: forall l: ListValue :: {List_reverse(List_reverse(l))}
  List_reverse(List_reverse(l)) == l;
axiom [List_reverse_extend]: forall l1: ListValue, l2: ListValue :: {List_reverse(List_extend(l1,l2))}
  List_reverse(List_extend(l1,l2)) == List_extend(List_reverse(l2), List_reverse(l1));

axiom [List_index!_nil_def]: forall v: Value :: {List_index!(ListValue_nil(), v)}
  List_index!(ListValue_nil(), v) == 0;
axiom [List_index!_cons_def_1]: forall h: Value, t: ListValue :: {List_index!(ListValue_cons(h,t), h)}
  List_index!(ListValue_cons(h,t), h) == 0;
axiom [List_index!_cons_def_2]: forall v: Value, h: Value, t: ListValue :: {List_index!(ListValue_cons(h,t), v)}
  !(normalize_value(v)==normalize_value(h)) ==> List_index!(ListValue_cons(h,t), v) == List_index!(t, v) + 1;
axiom [List_index_def]: forall v: Value, l: ListValue :: {List_index(l, v)}
  List_index(l,v) ==  if (List_index!(l,v) == List_len(l)) then Value_exception(Error_message("List does not contain element"))
                      else Value_int(List_index!(l,v));

axiom [List_repeat_def]: forall l: ListValue, n: int :: {List_repeat(l, n)}
  List_repeat(l, n) ==  if (n <= 0) then ListValue_nil() else
                        if (n == 1) then l else  List_extend(l, List_repeat(l, n-1));
axiom [List_repeat_mul]: forall l: ListValue, n: int, m: int :: {List_repeat(List_repeat(l, n),m)}
  List_repeat(List_repeat(l, n),m) == List_repeat(l, n * m);
axiom [List_repeat_contain]: forall l: ListValue, v: Value, n: int :: {List_contains(List_repeat(l, n), v)}
  n > 0 ==> (List_contains(List_repeat(l, n), v) == List_contains(l, v));
axiom [List_repeat_get]: forall l: ListValue, v: Value, i: int, n: int, m: int :: {List_get(List_repeat(l, n), i + m * List_len(l))}
  (i >= 0 && i < List_len(l) && m >= 0 && m < n) ==> (List_get(List_repeat(l, n), i + m * List_len(l)) == List_get(l, i));

axiom [List_insert_def0]: forall i: int, v: Value :: {List_insert(ListValue_nil(), i, v)}
  List_insert(ListValue_nil(), i, v) == ListValue_cons(v, ListValue_nil());
axiom [List_insert_def1]: forall l: ListValue, i: int, v: Value :: {List_insert(l, i, v)}
  List_insert(l, 0, v) == ListValue_cons(v, l);
axiom [List_insert_def2]: forall h: Value, t: ListValue, i: int, v: Value :: {List_insert(ListValue_cons(h,t), i, v)}
  (i > 0) ==> List_insert(ListValue_cons(h,t), i, v) == ListValue_cons(h, List_insert(t, i-1, v));
axiom [List_insert_def3]: forall h: Value, t: ListValue, i: int, v: Value :: {List_insert(ListValue_cons(h,t), i, v)}
  (i < 0) ==> List_insert(ListValue_cons(h,t), i, v) == List_insert(ListValue_cons(h,t), i mod (List_len(t)+1) , v);
axiom [List_insert_len]: forall l: ListValue, i: int, v: Value :: {List_len(List_insert(l, i, v))}
  List_len(List_insert(l, i, v)) == List_len(l) + 1;
axiom [List_insert_get0]: forall l: ListValue, p: int, v: Value:: {List_get(List_insert(l, p, v), p)}
  (p >= 0 && p < List_len(l)) ==> (List_get(List_insert(l, p, v), p) == v);
axiom [List_insert_get1]: forall l: ListValue, p: int, v: Value:: {List_get(List_insert(l, p, v), p)}
  p >= List_len(l) ==> (List_get(List_insert(l, p, v), List_len(l)) == v);
axiom [List_insert_get2]: forall l: ListValue, p: int, v: Value, i: int :: {List_get(List_insert(l, p, v), i)}
  (p >= List_len(l) && i < List_len(l)) ==> (List_get(List_insert(l, p, v),i) == List_get(l, i));
axiom [List_insert_get3]: forall l: ListValue, p: int, v: Value, i: int:: {List_get(List_insert(l, p, v), i)}
  (p >= 0 && p < List_len(l) && i < p) ==> (List_get(List_insert(l, p, v), i) == List_get(l,i));
axiom [List_insert_get4]: forall l: ListValue, p: int, v: Value, i: int:: {List_get(List_insert(l, p, v), i)}
  (p >= 0 && p < List_len(l) && i > p) ==> (List_get(List_insert(l, p, v), i) == List_get(l,i -1));
axiom [List_insert_get5]: forall l: ListValue, p: int, v: Value, i: int:: {List_get(List_insert(l, p, v), i)}
  (p < 0 && i < p mod List_len(l)) ==> (List_get(List_insert(l, p, v), i) == List_get(l,i));
axiom [List_insert_get6]: forall l: ListValue, p: int, v: Value, i: int:: {List_get(List_insert(l, p, v), i)}
  (p < 0 && i > p mod List_len(l)) ==> (List_get(List_insert(l, p, v), i) == List_get(l,i -1));

axiom [List_remove_nil_def]: forall x : Value ::{List_remove(ListValue_nil(), x)}
  List_remove(ListValue_nil(), x) == ListValue_nil();
axiom [List_remove_cons_def]: forall x : Value, h : Value, t : ListValue ::{List_remove(ListValue_cons(h,t),x)}
  List_remove(ListValue_cons(h,t),x) == if (normalize_value(x)==normalize_value(h)) then t
                                        else ListValue_cons(h, List_remove(t, x));

// Dict type
type Dict := Map Value Value;

//Dictionary functions
function Dict_empty() : Dict;
function Dict_insert (d: Dict, k: Value, v: Value) : Dict;
function Dict_get (d: Dict, k: Value) : Value;
function Dict_remove (d: Dict, k: Value) : Dict;
function Dict_contains (d: Dict, k: Value) : bool;

//Dictionary axioms
axiom [emptydict_def]: forall k: Value :: {Dict_empty() [k]} Dict_empty() [k] == Value_none();
axiom [Dict_get_def]: forall d: Dict, k: Value :: {Dict_get(d,k)} Dict_get(d,k) == d[normalize_value(k)];
axiom [Dict_insert_def]: forall d: Dict, k: Value, v: Value :: {Dict_insert(d,k,v)} Dict_insert(d,k,v) == d[normalize_value(k):= v];
axiom [Dict_remove_def]: forall d: Dict, k: Value :: {Dict_remove(d,k)} Dict_remove(d,k) == d[normalize_value(k):= Value_none()];
axiom [Dict_contains_def]: forall d: Dict, k: Value :: {Dict_contains(d,k)} Dict_contains(d,k) == (Dict_get (d,k) != Value_none());

// List of pairs of Value, used to construct Dict
type DictList;
// Constructor
function DictList_nil(): DictList;
function DictList_cons(k: Value, v: Value, d: DictList): DictList;
//Tag and tag functions
function DictList_tag (dl: DictList) : List_tag;
axiom [DistListTag_nil_def]: DictList_tag (DictList_nil()) == NIL;
axiom [DistListTag_cons_def]: forall k: Value, v: Value, d: DictList ::{DictList_cons(k,v,d)} DictList_tag (DictList_cons(k,v,d)) == CONS;
// as a constructor for Dict
function Dict_from_DicList (l : DictList) : Dict;
function Dict_from_DicList_rev (l : DictList, acc: Dict) : Dict;
axiom [Dict_from_DicList_rev_nil]: forall acc: Dict ::  Dict_from_DicList_rev(DictList_nil(), acc) == acc;
axiom [Dict_from_DicList_rev_cons]: forall k: Value, v: Value, d: DictList, acc: Dict ::
  Dict_from_DicList_rev(DictList_cons(k,v,d), acc) == Dict_from_DicList_rev(d,Dict_insert(acc, k, v));
axiom [Dict_from_DicList_def]: forall dl: DictList:: {Dict_from_DicList(dl)}
  Dict_from_DicList(dl) == Dict_from_DicList_rev(dl, Dict_empty());

type AttributeNames;
function AttributeNames_nil() : (AttributeNames);
function AttributeNames_cons(x0 : string, x1 : AttributeNames) : (AttributeNames);
function AttributeNames_tag (f: AttributeNames) : List_tag;
function AttributeNames_contains (l : AttributeNames, x: string) : bool;
function AttributeNames_len (l : AttributeNames) : int;
function AttributeNames_index (l : AttributeNames, i : int) : string;
function AttributeName_to_index (l : AttributeNames, f: string) : int;

axiom [AttributeNames_len_nil_def]: AttributeNames_len (AttributeNames_nil()) == 0;
axiom [AttributeNames_len_cons_def]: forall h : string, t : AttributeNames ::{AttributeNames_len (AttributeNames_cons(h,t))}
  AttributeNames_len (AttributeNames_cons(h,t)) == 1 + AttributeNames_len(t);
axiom [AttributeNames_tag_nil_def]: AttributeNames_tag(AttributeNames_nil()) == NIL;
axiom [AttributeNames_tag_cons_def]: forall h : string, t : AttributeNames ::{} AttributeNames_tag (AttributeNames_cons(h,t)) == CONS;
axiom [AttributeNames_contains_nil_def]: (forall x : string ::{AttributeNames_contains(AttributeNames_nil(), x)}
  !AttributeNames_contains(AttributeNames_nil(), x));
axiom [AttributeNames_contains_cons_def]: forall x : string, h : string, t : AttributeNames ::{AttributeNames_contains(AttributeNames_cons(h,t),x)}
  AttributeNames_contains(AttributeNames_cons(h,t),x) == ((x==h) || AttributeNames_contains(t,x));
axiom [AttributeNames_len_nonneg]: forall l: AttributeNames :: {AttributeNames_len(l)} AttributeNames_len(l) >= 0;
axiom [AttributeNames_index_nil]: forall i : int ::{AttributeNames_index (AttributeNames_nil(), i)} (AttributeNames_index (AttributeNames_nil(), i)) == "";
axiom [AttributeNames_index_zero]: forall h : string, t : AttributeNames ::{AttributeNames_index (AttributeNames_cons(h,t), 0)}
  AttributeNames_index (AttributeNames_cons(h,t), 0) == h;
axiom [AttributeNames_index_ind]: forall h : string, t : AttributeNames, i : int ::{AttributeNames_index (AttributeNames_cons(h,t), i)}
  (i > 0) ==> (AttributeNames_index (AttributeNames_cons(h,t), i)) == AttributeNames_index (t, i - 1);
axiom [AttributeNames_index_contains]: forall l: AttributeNames, i: int, x: string :: {AttributeNames_index(l,i), AttributeNames_contains(l,x)}
  (AttributeNames_index(l,i) == x) ==> AttributeNames_contains(l,x);
axiom [AttributeNames_index_ok]: forall l: AttributeNames, i: int:: {AttributeNames_index(l,i)}
  ((AttributeNames_index(l,i)) != "") == (i < AttributeNames_len(l));
axiom [AttributeName_to_index_nil_def]: forall f: string :: {AttributeName_to_index(AttributeNames_nil(), f)}
  AttributeName_to_index(AttributeNames_nil(), f) == 0;
axiom [AttributeName_to_index_cons_def_1]: forall h: string, t: AttributeNames :: {AttributeName_to_index(AttributeNames_cons(h,t), h)}
  AttributeName_to_index(AttributeNames_cons(h,t), h) == 0;
axiom [AttributeName_to_index_cons_def_2]: forall f: string, h: string, t: AttributeNames :: {AttributeName_to_index(AttributeNames_cons(h,t), f)}
  !(h == f) ==> AttributeName_to_index(AttributeNames_cons(h,t), f) == AttributeName_to_index(t, f) + 1;

function Class_mk (name: string, attributes: AttributeNames): Class;
function Class_attributes (c: Class) : AttributeNames;
function Class_name (c: Class): string;
axiom [Class_attributes_def]: forall name: string, attributes: AttributeNames :: {Class_mk (name, attributes)}
  Class_attributes(Class_mk (name, attributes)) == attributes;
axiom [Class_name_def]: forall name: string, attributes: AttributeNames :: {Class_mk (name, attributes)}
  Class_name(Class_mk (name, attributes)) == name;
axiom [Class_eq_def]: forall c: Class, c': Class :: {c == c'}
  (c == c') == (Class_name(c) == Class_name(c'));

function Class_hasAttribute (c: Class, attribute: string): bool;
axiom [Class_hasAttribute_def]: forall c: Class, attribute: string :: {Class_hasAttribute(c, attribute)}
  Class_hasAttribute(c, attribute) == AttributeNames_contains(Class_attributes(c), attribute);

function Class_err() : Class;
axiom [Class_err_attributes_def]: Class_attributes(Class_err()) == AttributeNames_nil();

function AttributeValues_empty (c: Class) : AttributeValues;
axiom [AttributeValues_empty_def_valid]: forall c: Class, attribute: string :: {AttributeValues_empty(c)[attribute]}
  Class_hasAttribute(c, attribute) ==> AttributeValues_empty(c)[attribute] == Value_none();
axiom [AttributeValues_empty_def_invalid]: forall c: Class, attribute: string :: {AttributeValues_empty(c)[attribute]}
  !Class_hasAttribute(c, attribute) ==> AttributeValues_empty(c)[attribute] == Value_exception(Error_message("Invalid Attribute of Class"));

function AttributeValues_err () : AttributeValues;
axiom [AttributeValues_err_def]: forall attribute: string :: {AttributeValues_err[attribute]}
  AttributeValues_err()[attribute] == Value_exception(Error_message("Error ClassInstance"));

function ClassInstance_mk (c: Class, av: AttributeValues) : ClassInstance;

function ClassInstance_getAttributeValues (ci: ClassInstance) : AttributeValues;
axiom [getAttributeValues_def]: forall c: Class, av: AttributeValues :: { ClassInstance_getAttributeValues(ClassInstance_mk (c, av))}
  ClassInstance_getAttributeValues(ClassInstance_mk (c, av)) == av;

function ClassInstance_getClass (ci: ClassInstance) : Class;
axiom [get_Class_def]: forall c: Class, av: AttributeValues :: {ClassInstance_getClass(ClassInstance_mk (c, av))}
  ClassInstance_getClass(ClassInstance_mk (c, av)) == c;

axiom [TypeOf_class]: forall ci: ClassInstance :: {TypeOf(Value_class(ci))} TypeOf(Value_class(ci)) == ValueType_class(ClassInstance_getClass(ci));

function ClassInstance_empty (c: Class) : ClassInstance;
axiom [ClassInstance_mk_empty_get_attributevalues]: forall c: Class :: {ClassInstance_getAttributeValues(ClassInstance_empty (c))}
  ClassInstance_getAttributeValues(ClassInstance_empty (c)) == AttributeValues_empty(c);
axiom [ClassInstance_mk_empty_get_class]: forall c: Class :: {ClassInstance_getClass(ClassInstance_empty (c))}
  ClassInstance_getClass(ClassInstance_empty (c)) == c;

function ClassInstance_err (err: string) : ClassInstance;
function ClassInstance_errortag (ci: ClassInstance): Error_tag;
axiom [ClassInstance_err_tag]: forall err: string :: {ClassInstance_errortag(ClassInstance_err(err))}
  ClassInstance_errortag(ClassInstance_err(err)) == ERR;
axiom [ClassInstance_err_get_class_def]: forall err: string :: {ClassInstance_getClass(ClassInstance_err(err)) }
  ClassInstance_getClass(ClassInstance_err(err)) == Class_err();
axiom [ClassInstance_err_get_attributevalues_def]: forall err: string :: {ClassInstance_getAttributeValues(ClassInstance_err (err))}
  ClassInstance_getAttributeValues(ClassInstance_err (err)) == AttributeValues_err();

function ClassInstance_get_attribute(ci: ClassInstance, attribute: string) : Value;
axiom [ClassInstance_get_attribute_def]: forall ci: ClassInstance, attribute: string ::{ClassInstance_get_attribute(ci, attribute)}
  ClassInstance_get_attribute(ci, attribute) == ClassInstance_getAttributeValues(ci)[attribute];

function ClassInstance_set_attribute (ci: ClassInstance, attribute: string, value: Value): ClassInstance;
axiom [ClassInstance_set_attribute_def]: forall ci: ClassInstance, attribute: string, v: Value:: {ClassInstance_set_attribute(ci, attribute, v)}
  ClassInstance_set_attribute(ci, attribute, v) == if Class_hasAttribute(ClassInstance_getClass(ci), attribute) then
                                                      ClassInstance_mk(ClassInstance_getClass(ci), ClassInstance_getAttributeValues(ci)[attribute:=v])
                                                  else ClassInstance_err("Set value for invalid");

function get_ClassInstance (v: Value) : ClassInstance;
axiom [get_ClassInstance_valid]: forall ci: ClassInstance :: {get_ClassInstance(Value_class(ci))}
  get_ClassInstance(Value_class(ci)) == ci;
axiom [get_ClassInstance_invalid]: forall v: Value :: {get_ClassInstance(v)}
  !isClassInstance(v) ==> get_ClassInstance(v) == ClassInstance_err ("Not of Class type");

function get_attribute(v: Value, attribute: string) : Value;
axiom [get_attribute_def]: forall v: Value, attribute: string ::{get_attribute(v, attribute)}
  get_attribute(v, attribute) == if isClassInstance(v) then
                                    ClassInstance_get_attribute(get_ClassInstance(v), attribute)
                                else Value_exception(Error_message("Not of Class type"));

function set_attribute(v: Value, attribute: string, v': Value) : Value;
axiom [set_attribute_def]: forall v: Value, attribute: string, v': Value ::{set_attribute(v, attribute, v')}
  set_attribute(v, attribute, v') == if isClassInstance(v) then
                                      Value_class(ClassInstance_set_attribute(get_ClassInstance(v), attribute, v'))
                                    else Value_exception(Error_message("Not of Class type"));

function get_Class (v: Value) : Class {
  ClassInstance_getClass(get_ClassInstance (v))
}

function hasAttribute(v: Value, attribute: string): bool {
  Class_hasAttribute (get_Class(v), attribute)
}

//Binary op function
function int_to_real (i: int) : real;
function str_repeat (s: string, i: int) : string;
function Py_add (v1: Value, v2: Value) : Value;
function Py_sub (v1: Value, v2: Value) : Value;
function Py_mul (v1: Value, v2: Value) : Value;
function Py_gt (v1: Value, v2: Value) : Value;
function Py_lt (v1: Value, v2: Value) : Value;
function Py_eq (v1: Value, v2: Value) : bool;
inline function bool_to_int (b: bool) : int {if b then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

axiom [Py_add_ints]: forall i1: int, i2: int :: {Py_add(Value_int(i1), Value_int(i2))}
  Py_add(Value_int(i1), Value_int(i2)) == Value_int(i1 + i2);
axiom [Py_add_floats]: forall f1: real, f2: real :: {Py_add(Value_float(f1), Value_float(f2))}
  Py_add(Value_float(f1), Value_float(f2)) == Value_float(f1 + f2);
axiom [Py_add_bools]: forall b1: bool, b2: bool :: {Py_add(Value_bool(b1), Value_bool(b2))}
  Py_add(Value_bool(b1), Value_bool(b2)) == Value_int(bool_to_int(b1) + bool_to_int(b2));
axiom [Py_add_int_bool]: forall i: int, b: bool :: {Py_add(Value_int(i), Value_bool(b))}
  Py_add(Value_int(i), Value_bool(b)) == Value_int(i + bool_to_int(b));
axiom [Py_add_bool_int]: forall b: bool, i: int :: {Py_add(Value_bool(b), Value_int(i))}
  Py_add(Value_bool(b), Value_int(i)) == Value_int(bool_to_int(b) + i);
axiom [Py_add_int_float]: forall i: int, r: real :: {Py_add(Value_int(i), Value_float(r))}
  Py_add(Value_int(i), Value_float(r)) == Value_float(r + int_to_real(i));
axiom [Py_add_float_int]: forall r: real, i: int :: {Py_add(Value_float(r), Value_int(i))}
  Py_add(Value_float(r), Value_int(i)) == Value_float(int_to_real(i) + r);
axiom [Py_add_float_bool]: forall r: real, b: bool :: {Py_add(Value_float(r), Value_bool(b))}
  Py_add(Value_float(r), Value_bool(b)) == Value_float(r + bool_to_real(b));
axiom [Py_add_bool_float]: forall b: bool, r: real :: {Py_add(Value_bool(b), Value_float(r))}
  Py_add(Value_bool(b), Value_float(r)) == Value_float(bool_to_real(b) + r);
axiom [Py_add_strs]: forall s1: string, s2: string :: {Py_add(Value_str(s1), Value_str(s2))}
  Py_add(Value_str(s1), Value_str(s2)) == Value_str(str.concat(s1, s2));
axiom [Py_add_lists]: forall l1: ListValue, l2: ListValue :: {Py_add(Value_list(l1), Value_list(l2))}
  Py_add(Value_list(l1), Value_list(l2)) == Value_list(List_extend(l1, l2));
axiom [Py_add_unsupport]: forall v1: Value, v2: Value :: {Py_add(v1,v2)}
  !((isInstance(v1, FLOAT) && isInstance(v2, FLOAT)) ||
    (TypeOf(v1) == STR && TypeOf(v2) == STR) ||
    (isList(v1) && isList(v2)))
  ==> Py_add(v1, v2) == Value_exception(Error_message("Operand Type is not supported"));

axiom [Py_sub_ints]: forall i1: int, i2: int :: {Py_sub(Value_int(i1), Value_int(i2))}
  Py_sub(Value_int(i1), Value_int(i2)) == Value_int(i1 - i2);
axiom [Py_sub_floats]: forall f1: real, f2: real :: {Py_sub(Value_float(f1), Value_float(f2))}
  Py_sub(Value_float(f1), Value_float(f2)) == Value_float(f1 - f2);
axiom [Py_sub_bools]: forall b1: bool, b2: bool :: {Py_sub(Value_bool(b1), Value_bool(b2))}
  Py_sub(Value_bool(b1), Value_bool(b2)) == Value_int(bool_to_int(b1) - bool_to_int(b2));
axiom [Py_sub_int_bool]: forall i: int, b: bool :: {Py_sub(Value_int(i), Value_bool(b))}
  Py_sub(Value_int(i), Value_bool(b)) == Value_int(i - bool_to_int(b));
axiom [Py_sub_bool_int]: forall b: bool, i: int :: {Py_sub(Value_bool(b), Value_int(i))}
  Py_sub(Value_bool(b), Value_int(i)) == Value_int(bool_to_int(b) - i);
axiom [Py_sub_int_float]: forall i: int, r: real :: {Py_sub(Value_int(i), Value_float(r))}
  Py_sub(Value_int(i), Value_float(r)) == Value_float(r - int_to_real(i));
axiom [Py_sub_float_int]: forall r: real, i: int :: {Py_sub(Value_float(r), Value_int(i))}
  Py_sub(Value_float(r), Value_int(i)) == Value_float(int_to_real(i) - r);
axiom [Py_sub_float_bool]: forall r: real, b: bool :: {Py_sub(Value_float(r), Value_bool(b))}
  Py_sub(Value_float(r), Value_bool(b)) == Value_float(r - bool_to_real(b));
axiom [Py_sub_bool_float]: forall b: bool, r: real :: {Py_sub(Value_bool(b), Value_float(r))}
  Py_sub(Value_bool(b), Value_float(r)) == Value_float(bool_to_real(b) - r);
axiom [Py_sub_unsupport]: forall v1: Value, v2: Value :: {Py_sub(v1,v2)}
  !(isInstance(v1, FLOAT) && isInstance(v2, FLOAT)) ==>
  Py_sub(v1, v2) == Value_exception(Error_message("Operand Type is not supported"));

axiom [Py_mul_ints]: forall i1: int, i2: int :: {Py_mul(Value_int(i1), Value_int(i2))}
  Py_mul(Value_int(i1), Value_int(i2)) == Value_int(i1 * i2);
axiom [Py_mul_bools]: forall b1: bool, b2: bool :: {Py_mul(Value_bool(b1), Value_bool(b2))}
  Py_mul(Value_bool(b1), Value_bool(b2)) == Value_int(bool_to_int(b1) * bool_to_int(b2));
axiom [Py_mul_int_bool]: forall i: int, b: bool :: {Py_mul(Value_int(i), Value_bool(b))}
  Py_mul(Value_int(i), Value_bool(b)) == Value_int(i * bool_to_int(b));
axiom [Py_mul_bool_int]: forall b: bool, i: int :: {Py_mul(Value_bool(b), Value_int(i))}
  Py_mul(Value_bool(b), Value_int(i)) == Value_int(bool_to_int(b) * i);
axiom [Py_mul_str_int]: forall s: string, i: int :: {Py_mul(Value_str(s), Value_int(i))}
  Py_mul(Value_str(s), Value_int(i)) == Value_str(str_repeat(s, i));
axiom [Py_mul_int_str]: forall s: string, i: int :: {Py_mul(Value_int(i), Value_str(s))}
  Py_mul(Value_int(i), Value_str(s)) == Value_str(str_repeat(s, i));
axiom [Py_mul_str_bool]: forall s: string, b: bool :: {Py_mul(Value_str(s), Value_bool(b))}
  Py_mul(Value_str(s), Value_bool(b)) == Value_str(if b then s else "");
axiom [Py_mul_bool_str]: forall s: string, b: bool :: {Py_mul(Value_bool(b), Value_str(s)) }
  Py_mul(Value_bool(b), Value_str(s)) ==  Value_str(if b then s else "");
axiom [Py_mul_list_int]: forall l: ListValue, i: int :: {Py_mul(Value_list(l), Value_int(i))}
  Py_mul(Value_list(l), Value_int(i)) == Value_list(List_repeat(l, i));
axiom [Py_mul_int_list]: forall l: ListValue, i: int :: {Py_mul(Value_int(i), Value_list(l))}
  Py_mul(Value_int(i), Value_list(l)) == Value_list(List_repeat(l, i));
axiom [Py_mul_list_bool]: forall l: ListValue, b: bool :: {Py_mul(Value_list(l), Value_bool(b))}
  Py_mul(Value_list(l), Value_bool(b)) == Value_list(if b then l else ListValue_nil());
axiom [Py_mul_bool_list]: forall l: ListValue, b: bool :: {Py_mul(Value_bool(b), Value_list(l)) }
  Py_mul(Value_bool(b), Value_list(l)) ==  Value_list(if b then l else ListValue_nil());
axiom [Py_mul_unsupport]: forall v1: Value, v2: Value :: {Py_add(v1,v2)}
  !((isInstance(v1, FLOAT) && isInstance(v2, FLOAT)) ||
    (TypeOf(v1) == STR && isInstance(v2, INT)) ||
    (TypeOf(v2) == STR && isInstance(v1, INT)) ||
    (isList(v1) && isInstance(v2, INT)) ||
    (isList(v2) && isInstance(v1, INT)) )
  ==> Py_mul(v1, v2) == Value_exception(Error_message("Operand Type is not supported"));

axiom [Py_lt_ints]: forall i1: int, i2: int :: {Py_lt(Value_int(i1), Value_int(i2))}
  Py_lt(Value_int(i1), Value_int(i2)) == Value_bool(i1 < i2);
axiom [Py_lt_floats]: forall f1: real, f2: real :: {Py_lt(Value_float(f1), Value_float(f2))}
  Py_lt(Value_float(f1), Value_float(f2)) == Value_bool(f1 < f2);
axiom [Py_lt_bools]: forall b1: bool, b2: bool :: {Py_lt(Value_bool(b1), Value_bool(b2))}
  Py_lt(Value_bool(b1), Value_bool(b2)) == Value_bool(bool_to_int(b1) < bool_to_int(b2));
axiom [Py_lt_int_bool]: forall i: int, b: bool :: {Py_lt(Value_int(i), Value_bool(b))}
  Py_lt(Value_int(i), Value_bool(b)) == Value_bool(i < bool_to_int(b));
axiom [Py_lt_bool_int]: forall b: bool, i: int :: {Py_lt(Value_bool(b), Value_int(i))}
  Py_lt(Value_bool(b), Value_int(i)) == Value_bool(bool_to_int(b) < i);
axiom [Py_lt_int_float]: forall i: int, r: real :: {Py_lt(Value_int(i), Value_float(r))}
  Py_lt(Value_int(i), Value_float(r)) == Value_bool(r < int_to_real(i));
axiom [Py_lt_float_int]: forall r: real, i: int :: {Py_lt(Value_float(r), Value_int(i))}
  Py_lt(Value_float(r), Value_int(i)) == Value_bool(int_to_real(i) < r);
axiom [Py_lt_float_bool]: forall r: real, b: bool :: {Py_lt(Value_float(r), Value_bool(b))}
  Py_lt(Value_float(r), Value_bool(b)) == Value_bool(r < bool_to_real(b));
axiom [Py_lt_bool_float]: forall b: bool, r: real :: {Py_lt(Value_bool(b), Value_float(r))}
  Py_lt(Value_bool(b), Value_float(r)) == Value_bool(bool_to_real(b) < r);
axiom [Py_lt_unsupport]: forall v1: Value, v2: Value :: {Py_lt(v1,v2)}
  !(isInstance(v1, FLOAT) && isInstance(v2, FLOAT)) ==>
  Py_lt(v1, v2) == Value_exception(Error_message("Operand Type is not supported"));

axiom [Py_gt_ints]: forall i1: int, i2: int :: {Py_gt(Value_int(i1), Value_int(i2))}
  Py_gt(Value_int(i1), Value_int(i2)) == Value_bool(i1 > i2);
axiom [Py_gt_floats]: forall f1: real, f2: real :: {Py_gt(Value_float(f1), Value_float(f2))}
  Py_gt(Value_float(f1), Value_float(f2)) == Value_bool(f1 > f2);
axiom [Py_gt_bools]: forall b1: bool, b2: bool :: {Py_gt(Value_bool(b1), Value_bool(b2))}
  Py_gt(Value_bool(b1), Value_bool(b2)) == Value_bool(bool_to_int(b1) > bool_to_int(b2));
axiom [Py_gt_int_bool]: forall i: int, b: bool :: {Py_gt(Value_int(i), Value_bool(b))}
  Py_gt(Value_int(i), Value_bool(b)) == Value_bool(i > bool_to_int(b));
axiom [Py_gt_bool_int]: forall b: bool, i: int :: {Py_gt(Value_bool(b), Value_int(i))}
  Py_gt(Value_bool(b), Value_int(i)) == Value_bool(bool_to_int(b) > i);
axiom [Py_gt_int_float]: forall i: int, r: real :: {Py_gt(Value_int(i), Value_float(r))}
  Py_gt(Value_int(i), Value_float(r)) == Value_bool(r > int_to_real(i));
axiom [Py_gt_float_int]: forall r: real, i: int :: {Py_gt(Value_float(r), Value_int(i))}
  Py_gt(Value_float(r), Value_int(i)) == Value_bool(int_to_real(i) > r);
axiom [Py_gt_float_bool]: forall r: real, b: bool :: {Py_gt(Value_float(r), Value_bool(b))}
  Py_gt(Value_float(r), Value_bool(b)) == Value_bool(r > bool_to_real(b));
axiom [Py_gt_bool_float]: forall b: bool, r: real :: {Py_gt(Value_bool(b), Value_float(r))}
  Py_gt(Value_bool(b), Value_float(r)) == Value_bool(bool_to_real(b) > r);
axiom [Py_gt_unsupport]: forall v1: Value, v2: Value :: {Py_gt(v1,v2)}
  !(isInstance(v1, FLOAT) && isInstance(v2, FLOAT)) ==>
  Py_gt(v1, v2) == Value_exception(Error_message("Operand Type is not supported"));

axiom [Py_eq_def]: forall v: Value, v': Value :: {Py_eq(v, v')}
  Py_eq(v, v') == (normalize_value(v) == normalize_value (v'));

//Testing
procedure non_contradiction_test() returns () {
  assert [one_eq_two]: 1 == 2;
};

procedure binary_op_and_types_test () returns () {
  assert [int_add_ok]: forall i: int :: TypeOf(Py_add(Value_int(1), Value_int(i))) != EXCEPTION;
  assert [int_add_class_except]: forall v: Value :: isClassInstance(v) ==> TypeOf(Py_add(Value_int(1), v)) == EXCEPTION;
  assert [int_add_class_except']: forall v: Value :: hasAttribute(v, "a") ==> TypeOf(Py_add(Value_int(1), v)) == EXCEPTION;
  assert [float_add_isInstance_int_ok]: forall v: Value :: isInstance(v,INT) ==> TypeOf(Py_add(Value_float(1.1), v)) != EXCEPTION;
  //assert [exists_type1]: exists t: ValueType, v: Value :: (TypeOf(Py_add(Value_int(1), v)) != EXCEPTION) && (TypeOf(v) == t);
  //assert [exist_value]: exists v: Value:: TypeOf(Py_add(Value_int(1), v)) != EXCEPTION;
  //assert [exist_value'']: exists i: int :: {Value_int(2)} TypeOf(Py_add(Value_int(1), Value_int(i))) != EXCEPTION;
  //assert [exists_type3]: exists v: Value :: (TypeOf(Py_add(Value_none(), v)) == STR);
};

procedure list_functions_test() returns ()
{
  var l1: ListValue, l2: ListValue;
  l1 := ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3), ListValue_nil())));
  l2 := ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3),
        ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3), ListValue_nil()))))));
  assert [index_1]: List_get(l1,1) == Value_int(2);
  assert [contain_true]: List_contains(l1, Value_bool(true));
  assert [ValueEq]: !(Value_int(4) == Value_int(3));
  assert [normalize_value]: !(normalize_value(Value_int(4)) == Value_int(3));
  assert [contain_3]: List_contains(l1, Value_int(2));
  assert [list_index_test1]: List_index(l1, Value_int(3)) == Value_int(2);
  assert [list_index_test2]: TypeOf(List_index(l1, Value_int(9))) == EXCEPTION;
  assert [list_extend]: List_extend(l1, l1) == l2;
  assert [list_repeat1]: List_repeat(l1, 2) == l2;
  assert [list_repeat2]: List_repeat(l1, 6) == List_repeat(l2, 3);
};

procedure list_generic_test() returns () {
  var l1: ListValue;
  assert [contains_append]: forall l: ListValue, x: Value :: List_contains(List_append(l,x), x);
  assert [len_append]: forall l: ListValue, x: Value :: List_len(List_append(l,x)) == List_len(l) + 1;
  l1 := ListValue_cons(Value_int(1), ListValue_cons(Value_int(2), ListValue_cons (Value_int(3), ListValue_nil())));
  assert [l1_contains_3]: List_contains (l1, Value_int(3));
  assert [contains_len]: forall l: ListValue, x: Value:: List_contains(l,x) ==> (List_len(l) >0);
  assert [l1l2_contains_3]: forall l2: ListValue :: List_contains (List_extend(l1, l2), Value_int(3));
  assert [revl1_contain_3]: List_contains (List_reverse(l1), Value_int(3));
  assert [rev_contain]: forall l: ListValue, v: Value :: List_contains (List_reverse(l), v) == List_contains(l,v);
  assert [l1r_l2_contains_3]: forall l2: ListValue :: List_contains (List_extend(List_reverse(l1), l2), Value_int(3));
  assert [l1r_l2_contains_3']: forall l2: ListValue :: List_contains (List_reverse(List_extend(List_reverse(l1), l2)), Value_int(3));
  assert [List_cons_extend_contains_symm]: forall x: Value, l1: ListValue, l2: ListValue ::
    List_contains (List_extend(l1,l2), x) == List_contains (List_extend(l2,l1), x);
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
  arg2 := Value_list(ListValue_cons(Value_int(3), ListValue_cons (Value_bool(true), ListValue_nil())));
  assert [subtype_bool]: isInstance(arg1,BOOL);
  call simple_call(arg1, arg2);
};

procedure dict_functions_test () returns () {
  var d1: Dict, d2: Dict, d3: Dict;
  d1:= Dict_insert(Dict_empty(), Value_int(1), Value_int(1));
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

procedure ValueClass_test() returns () {
  var c: Class, ci: Value, ci': Value, v: Value;
  c := Class_mk ("point", AttributeNames_cons("x", AttributeNames_cons("y", AttributeNames_nil())));
  ci := Value_class(ClassInstance_empty (c));
  assert [has_x]: hasAttribute(ci,"x");
  assert [nhas_z]: !hasAttribute(ci,"z");
  assert [isInstance_class]: isInstance(ci, ValueType_class(c));
  assert [get_x_empty]: get_attribute(ci, "x") == Value_none();
  assert [get_y_empty]: get_attribute(ci, "y") == Value_none();
  assert [get_x']: get_attribute(set_attribute(ci, "x", Value_int(1)), "x") == Value_int(1);
  ci := set_attribute(ci, "x", Value_int(1));
  assert [get_x]: get_attribute(ci, "x") == Value_int(1);
  assert [get_y]: get_attribute(ci, "y") == Value_none();
};

#end

#eval verify "cvc5" boogieTypePrelude

def Boogie.prelude : Boogie.Program :=
   Boogie.getProgram Strata.boogieTypePrelude |>.fst

end Strata
