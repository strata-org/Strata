type:
None
Type Arguments:
[]
Constructors:
[Name: None_none Args: [] Tester: None..isNone_none ]

type Core.Boundedness.Infinite Object []
func Object_len :  ((x : Object)) → int;
axiom Object_len_ge_zero: (∀ (((~Int.Ge : (arrow int (arrow int bool))) ((~Object_len : (arrow Object int)) %0)) #0));
func inheritsFrom :  ((child : string) (parent : string)) → bool;
axiom inheritsFrom_refl: (∀ (((~inheritsFrom : (arrow string (arrow string bool))) %0) %0));
type:
Error
Type Arguments:
[]
Constructors:
[Name:
 Error_TypeError
 Args:
 [(getTypeError, string)]
 Tester:
 Error..isError_TypeError
 ,
 Name:
 Error_AttributeError
 Args:
 [(getAttributeError, string)]
 Tester:
 Error..isError_AttributeError
 ,
 Name:
 Error_RePatternError
 Args:
 [(getRePatternError, string)]
 Tester:
 Error..isError_RePatternError
 ,
 Name:
 Error_Unimplemented
 Args:
 [(getUnimplemented, string)]
 Tester:
 Error..isError_Unimplemented
 ]

type:
Except
Type Arguments:
[err, ok]
Constructors:
[Name:
 Except_mkOK
 Args:
 [(Except_getOK, ok)]
 Tester:
 Except..isExcept_mkOK
 ,
 Name:
 Except_mkErr
 Args:
 [(Except_getErr, err)]
 Tester:
 Except..isExcept_mkErr
 ]

type ExceptErrorRegex := (Except Error regex)
func PyReMatchRegex :  ((pattern : regex) (str : string) (flags : int)) → bool;
axiom PyReMatchRegex_def_noFlg: (∀ (∀ (((((~PyReMatchRegex : (arrow regex (arrow string (arrow int bool)))) %1) %0) #0) == (((~Str.InRegEx : (arrow string (arrow regex bool))) %0) %1))));
func PyReMatchStr :  ((pattern : string) (str : string) (flags : int)) → (Except Error bool);
type:
ListStr
Type Arguments:
[]
Constructors:
[Name:
 ListStr_nil
 Args:
 []
 Tester:
 ListStr..isListStr_nil
 ,
 Name:
 ListStr_cons
 Args:
 [(head, string), (tail, ListStr)]
 Tester:
 ListStr..isListStr_cons
 ]

type:
ExceptOrNone
Type Arguments:
[]
Constructors:
[Name:
 ExceptOrNone_mk_code
 Args:
 [(code_val, string)]
 Tester:
 ExceptOrNone..isExceptOrNone_mk_code
 ,
 Name:
 ExceptOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 ExceptOrNone..isExceptOrNone_mk_none
 ]

type:
IntOrNone
Type Arguments:
[]
Constructors:
[Name:
 IntOrNone_mk_int
 Args:
 [(int_val, int)]
 Tester:
 IntOrNone..isIntOrNone_mk_int
 ,
 Name:
 IntOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 IntOrNone..isIntOrNone_mk_none
 ]

type:
StrOrNone
Type Arguments:
[]
Constructors:
[Name:
 StrOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 StrOrNone..isStrOrNone_mk_str
 ,
 Name:
 StrOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 StrOrNone..isStrOrNone_mk_none
 ]

func strOrNone_toObject :  ((v : StrOrNone)) → Object;
axiom axiom_3: (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) ((~Bool.Not : (arrow bool bool)) (%1 == %0))) ((~Bool.Not : (arrow bool bool)) (((~strOrNone_toObject : (arrow StrOrNone Object)) %1) == ((~strOrNone_toObject : (arrow StrOrNone Object)) %0))))));
axiom axiom_4: (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) ((~StrOrNone..isStrOrNone_mk_str : (arrow StrOrNone bool)) %0)) (((~Object_len : (arrow Object int)) ((~strOrNone_toObject : (arrow StrOrNone Object)) %0)) == ((~Str.Length : (arrow string int)) ((~StrOrNone..str_val : (arrow StrOrNone string)) %0)))));
type:
AnyOrNone
Type Arguments:
[]
Constructors:
[Name:
 AnyOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 AnyOrNone..isAnyOrNone_mk_str
 ,
 Name:
 AnyOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 AnyOrNone..isAnyOrNone_mk_none
 ]

type:
BoolOrNone
Type Arguments:
[]
Constructors:
[Name:
 BoolOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 BoolOrNone..isBoolOrNone_mk_str
 ,
 Name:
 BoolOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 BoolOrNone..isBoolOrNone_mk_none
 ]

type:
BoolOrStrOrNone
Type Arguments:
[]
Constructors:
[Name:
 BoolOrStrOrNone_mk_bool
 Args:
 [(bool_val, bool)]
 Tester:
 BoolOrStrOrNone..isBoolOrStrOrNone_mk_bool
 ,
 Name:
 BoolOrStrOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 BoolOrStrOrNone..isBoolOrStrOrNone_mk_str
 ,
 Name:
 BoolOrStrOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 BoolOrStrOrNone..isBoolOrStrOrNone_mk_none
 ]

type:
DictStrStrOrNone
Type Arguments:
[]
Constructors:
[Name:
 DictStrStrOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 DictStrStrOrNone..isDictStrStrOrNone_mk_str
 ,
 Name:
 DictStrStrOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 DictStrStrOrNone..isDictStrStrOrNone_mk_none
 ]

type:
BytesOrStrOrNone
Type Arguments:
[]
Constructors:
[Name:
 BytesOrStrOrNone_mk_none
 Args:
 [(none_val, None)]
 Tester:
 BytesOrStrOrNone..isBytesOrStrOrNone_mk_none
 ,
 Name:
 BytesOrStrOrNone_mk_str
 Args:
 [(str_val, string)]
 Tester:
 BytesOrStrOrNone..isBytesOrStrOrNone_mk_str
 ]

type Core.Boundedness.Infinite DictStrAny []
func DictStrAny_mk :  ((s : string)) → DictStrAny;
type Core.Boundedness.Infinite ListDictStrAny []
func ListDictStrAny_nil :  () → ListDictStrAny;
type:
Client
Type Arguments:
[]
Constructors:
[Name: Client_S3 Args: [] Tester: Client..isClient_S3 , Name: Client_CW Args: [] Tester: Client..isClient_CW ]

(procedure timedelta :  ((days : IntOrNone) (hours : IntOrNone)) → ((delta : int) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: init (days_i : int) := #0
#[<[fileRange]: :5165-5258>] if ((~IntOrNone..isIntOrNone_mk_int : (arrow IntOrNone bool)) (days : IntOrNone)) then {days_i := ((~IntOrNone..int_val : (arrow IntOrNone int)) (days : IntOrNone))}
else{}
init (hours_i : int) := #0
#[<[fileRange]: :5284-5380>] if ((~IntOrNone..isIntOrNone_mk_int : (arrow IntOrNone bool)) (hours : IntOrNone)) then {hours_i := ((~IntOrNone..int_val : (arrow IntOrNone int)) (hours : IntOrNone))}
else{}
assume [assume_timedelta_sign_matches] ((delta : int) == (((~Int.Mul : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (((~Int.Add : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (days_i : int)) #24)) (hours_i : int))) #3600)) #1000000))

func Timedelta_mk :  ((days : int) (seconds : int) (microseconds : int)) → int :=
  ((((~Int.Add : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (((~Int.Add : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (days : int)) #3600)) #24)) (seconds : int))) #1000000)) (microseconds : int)))
func Timedelta_get_days :  ((timedelta : int)) → int;
func Timedelta_get_seconds :  ((timedelta : int)) → int;
func Timedelta_get_microseconds :  ((timedelta : int)) → int;
axiom Timedelta_deconstructors: (∀ (∀ (∀ (∀ (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) %5) %4) %3) == ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) %2) %1) %0))) (((~Int.Le : (arrow int (arrow int bool))) #0) %0))) (((~Int.Lt : (arrow int (arrow int bool))) %0) #1000000))) (((~Int.Le : (arrow int (arrow int bool))) #0) %1))) (((~Int.Lt : (arrow int (arrow int bool))) %1) (((~Int.Mul : (arrow int (arrow int int))) #3600) #24)))) (((~Int.Le : (arrow int (arrow int bool))) ((~Int.Neg : (arrow int int)) #999999999)) %2))) (((~Int.Le : (arrow int (arrow int bool))) %2) #999999999))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Timedelta_get_days : (arrow int int)) ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) %5) %4) %3)) == %2)) (((~Timedelta_get_seconds : (arrow int int)) ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) %5) %4) %3)) == %1))) (((~Timedelta_get_microseconds : (arrow int int)) ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) %5) %4) %3)) == %0)))))))));
type Core.Boundedness.Infinite Datetime []
type Core.Boundedness.Infinite Datetime_base []
func Datetime_get_base :  ((d : Datetime)) → Datetime_base;
func Datetime_get_timedelta :  ((d : Datetime)) → int;
(procedure datetime_now :  () → ((d : Datetime) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: (datetime_now_ensures_0, (((~Datetime_get_timedelta : (arrow Datetime int)) (d : Datetime)) == ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) #0) #0) #0)))
body: assume [assume_datetime_now] (((~Datetime_get_timedelta : (arrow Datetime int)) (d : Datetime)) == ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) #0) #0) #0))

(procedure datetime_utcnow :  () → ((d : Datetime) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: (datetime_utcnow_ensures_0, (((~Datetime_get_timedelta : (arrow Datetime int)) (d : Datetime)) == ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) #0) #0) #0)))
body: assume [assume_datetime_now] (((~Datetime_get_timedelta : (arrow Datetime int)) (d : Datetime)) == ((((~Timedelta_mk : (arrow int (arrow int (arrow int int)))) #0) #0) #0))

func Datetime_add :  ((d : Datetime) (timedelta : int)) → Datetime;
func Datetime_sub :  ((d : Datetime) (timedelta : int)) → Datetime :=
  ((((~Datetime_add : (arrow Datetime (arrow int Datetime))) (d : Datetime)) ((~Int.Neg : (arrow int int)) (timedelta : int))))
axiom Datetime_add_ax: (∀ (∀ (((~Bool.And : (arrow bool (arrow bool bool))) (((~Datetime_get_base : (arrow Datetime Datetime_base)) (((~Datetime_add : (arrow Datetime (arrow int Datetime))) %1) %0)) == ((~Datetime_get_base : (arrow Datetime Datetime_base)) %1))) (((~Datetime_get_timedelta : (arrow Datetime int)) (((~Datetime_add : (arrow Datetime (arrow int Datetime))) %1) %0)) == (((~Int.Add : (arrow int (arrow int int))) ((~Datetime_get_timedelta : (arrow Datetime int)) %1)) %0)))));
func Datetime_lt :  ((d1 : Datetime) (d2 : Datetime)) → bool;
axiom Datetime_lt_ax: (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (((~Datetime_get_base : (arrow Datetime Datetime_base)) %1) == ((~Datetime_get_base : (arrow Datetime Datetime_base)) %0))) ((((~Datetime_lt : (arrow Datetime (arrow Datetime bool))) %1) %0) == (((~Int.Lt : (arrow int (arrow int bool))) ((~Datetime_get_timedelta : (arrow Datetime int)) %1)) ((~Datetime_get_timedelta : (arrow Datetime int)) %0))))));
type Core.Boundedness.Infinite Date []
(procedure datetime_date :  ((dt : Datetime)) → ((d : Datetime) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

func datetime_to_str :  ((dt : Datetime)) → string;
func datetime_to_int :  () → int;
(procedure datetime_strptime :  ((time : string) (format : string)) → ((d : Datetime) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: (req_format_str, ((format : string) == #%Y-%m-%d))
postconditions: (ensures_str_strp_reverse, (∀ (((~Bool.Equiv : (arrow bool (arrow bool bool))) ((time : string) == ((~datetime_to_str : (arrow Datetime string)) %0))) ((d : Datetime) == %0))))
body: assume [assume_str_strp_reverse] (∀ (((~Bool.Equiv : (arrow bool (arrow bool bool))) ((time : string) == ((~datetime_to_str : (arrow Datetime string)) %0))) ((d : Datetime) == %0)))

(procedure importFrom :  ((module : string) (names : ListStr) (level : int)) → ())
modifies: []
preconditions: 
postconditions: 
body: 

(procedure import :  ((names : ListStr)) → ())
modifies: []
preconditions: 
postconditions: 
body: 

(procedure print :  ((msg : string) (opt : StrOrNone)) → ())
modifies: []
preconditions: 
postconditions: 
body: 

(procedure json_dumps :  ((msg : DictStrAny) (opt_indent : IntOrNone)) → ((s : string) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

(procedure json_loads :  ((msg : string)) → ((d : DictStrAny) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

(procedure input :  ((msg : string)) → ((result : string) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

(procedure random_choice :  ((l : ListStr)) → ((result : string) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

func str_in_list_str :  ((s : string) (l : ListStr)) → bool;
func str_in_dict_str_any :  ((s : string) (l : DictStrAny)) → bool;
func list_str_get :  ((l : ListStr) (i : int)) → string;
func str_len :  ((s : string)) → int;
func dict_str_any_get :  ((d : DictStrAny) (k : string)) → DictStrAny;
func dict_str_any_get_list_str :  ((d : DictStrAny) (k : string)) → ListStr;
func dict_str_any_get_str :  ((d : DictStrAny) (k : string)) → string;
func dict_str_any_length :  ((d : DictStrAny)) → int;
(procedure str_to_float :  ((s : string)) → ((result : string) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: 

func Float_gt :  ((lhs : string) (rhs : string)) → bool;
(procedure test_helper_procedure :  ((req_name : string) (opt_name : StrOrNone)) → ((maybe_except : ExceptOrNone)))
modifies: []
preconditions: (req_name_is_foo, ((req_name : string) == #foo)) (req_opt_name_none_or_str, (if ((~Bool.Not : (arrow bool bool)) ((~StrOrNone..isStrOrNone_mk_none : (arrow StrOrNone bool)) (opt_name : StrOrNone))) then ((~StrOrNone..isStrOrNone_mk_str : (arrow StrOrNone bool)) (opt_name : StrOrNone)) else #true)) (req_opt_name_none_or_bar, (if ((~StrOrNone..isStrOrNone_mk_str : (arrow StrOrNone bool)) (opt_name : StrOrNone)) then (((~StrOrNone..str_val : (arrow StrOrNone string)) (opt_name : StrOrNone)) == #bar) else #true))
postconditions: (ensures_maybe_except_none, ((~ExceptOrNone..isExceptOrNone_mk_none : (arrow ExceptOrNone bool)) (maybe_except : ExceptOrNone)))
body: assert [assert_name_is_foo] ((req_name : string) == #foo)
assert [assert_opt_name_none_or_str] (if ((~Bool.Not : (arrow bool bool)) ((~StrOrNone..isStrOrNone_mk_none : (arrow StrOrNone bool)) (opt_name : StrOrNone))) then ((~StrOrNone..isStrOrNone_mk_str : (arrow StrOrNone bool)) (opt_name : StrOrNone)) else #true)
assert [assert_opt_name_none_or_bar] (if ((~StrOrNone..isStrOrNone_mk_str : (arrow StrOrNone bool)) (opt_name : StrOrNone)) then (((~StrOrNone..str_val : (arrow StrOrNone string)) (opt_name : StrOrNone)) == #bar) else #true)
assume [assume_maybe_except_none] ((~ExceptOrNone..isExceptOrNone_mk_none : (arrow ExceptOrNone bool)) (maybe_except : ExceptOrNone))

var (__name__ : string) := #__main__
type Core.Boundedness.Infinite CircularBuffer []
(procedure main :  () → ((maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: init (my_buf : CircularBuffer) := DUMMY_CircularBuffer
havoc my_buf
init (exception_ty_matches : bool) := #false
havoc exception_ty_matches
call [my_buf, maybe_except] := CircularBuffer___init__([#5])
call print([#Bye, (~StrOrNone_mk_none ~None_none)])
end : {}

(procedure CircularBuffer___init__ :  ((n : int)) → ((ret : CircularBuffer) (maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: init (exception_ty_matches : bool) := #false
havoc exception_ty_matches
call print([#Hi, (~StrOrNone_mk_none ~None_none)])
end : {}

(procedure __main__ :  () → ((maybe_except : ExceptOrNone)))
modifies: []
preconditions: 
postconditions: 
body: init (exception_ty_matches : bool) := #false
havoc exception_ty_matches
call import([(((~ListStr_cons : (arrow string (arrow ListStr ListStr))) #test_helper) (~ListStr_nil : ListStr))])
call importFrom([#typing,
 (((~ListStr_cons : (arrow string (arrow ListStr ListStr))) #List) (~ListStr_nil : ListStr)),
 #0])
if (__name__ == #__main__) then {call [maybe_except] := main([])
 if (~ExceptOrNone..isExceptOrNone_mk_code maybe_except) then {goto end} else{}}
else{}
end : {}
