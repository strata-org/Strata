/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Python

/--
Python prelude declarations expressed in Laurel grammar.
This covers datatypes, opaque types, and function/procedure signatures
that can be represented in Laurel syntax.

Core-specific constructs (axioms, type synonyms, functions with Core expression
bodies, discriminator access) remain in `CorePrelude.lean` and are combined
at the Core level in StrataMain.
-/
private def pythonPreludeLaurelDDM :=
#strata
program Laurel;

// =====================================================================
// Basic Types
// =====================================================================

type Object;
type Date;
type Datetime;
type Datetime_base;
type DictStrAny;
type ListDictStrAny;

// =====================================================================
// None Type
// =====================================================================

datatype None {
  None_none()
}

// =====================================================================
// Error / Exception Types
// =====================================================================

datatype Error {
  Error_TypeError(getTypeError: string),
  Error_AttributeError(getAttributeError: string),
  Error_RePatternError(getRePatternError: string),
  Error_Unimplemented(getUnimplemented: string)
}
datatype ExceptOrNone {
  ExceptOrNone_mk_code(code_val: string),
  ExceptOrNone_mk_none(none_val: None)
}

datatype IntOrNone {
  IntOrNone_mk_int(int_val: int),
  IntOrNone_mk_none(none_val: None)
}

datatype StrOrNone {
  StrOrNone_mk_str(str_val: string),
  StrOrNone_mk_none(none_val: None)
}

datatype AnyOrNone {
  AnyOrNone_mk_str(str_val: string),
  AnyOrNone_mk_none(none_val: None)
}

datatype BoolOrNone {
  BoolOrNone_mk_str(str_val: string),
  BoolOrNone_mk_none(none_val: None)
}

datatype BoolOrStrOrNone {
  BoolOrStrOrNone_mk_bool(bool_val: bool),
  BoolOrStrOrNone_mk_str(str_val: string),
  BoolOrStrOrNone_mk_none(none_val: None)
}

datatype DictStrStrOrNone {
  DictStrStrOrNone_mk_str(str_val: string),
  DictStrStrOrNone_mk_none(none_val: None)
}

datatype BytesOrStrOrNone {
  BytesOrStrOrNone_mk_none(none_val: None),
  BytesOrStrOrNone_mk_str(str_val: string)
}

datatype ListStr {
  ListStr_nil(),
  ListStr_cons(head: string, tail: ListStr)
}

datatype Client {
  Client_S3(),
  Client_CW()
}

datatype PyAnyType {
  PyAnyType_Inhabitant()
}
// =====================================================================
// Function Declarations (without bodies)
// =====================================================================

function Object_len(x: Object): int
function inheritsFrom(child: string, parent: string): bool
function strOrNone_toObject(v: StrOrNone): Object
function DictStrAny_mk(s: string): DictStrAny
function ListDictStrAny_nil(): ListDictStrAny

// Timedelta functions
function Timedelta_get_days(timedelta: int): int
function Timedelta_get_seconds(timedelta: int): int
function Timedelta_get_microseconds(timedelta: int): int

// Datetime functions
function Datetime_get_base(d: Datetime): Datetime_base
function Datetime_get_timedelta(d: Datetime): int
function Datetime_add(d: Datetime, timedelta: int): Datetime
function Datetime_lt(d1: Datetime, d2: Datetime): bool
function datetime_to_str(dt: Datetime): string
function datetime_to_int(): int

// String/collection functions
function str_in_list_str(s: string, l: ListStr): bool
function str_in_dict_str_any(s: string, l: DictStrAny): bool
function list_str_get(l: ListStr, i: int): string
function str_len(s: string): int
function dict_str_any_get(d: DictStrAny, k: string): DictStrAny
function dict_str_any_get_list_str(d: DictStrAny, k: string): ListStr
function dict_str_any_get_str(d: DictStrAny, k: string): string
function dict_str_any_length(d: DictStrAny): int
function Float_gt(lhs: string, rhs: string): bool

// =====================================================================
// Function Declarations (with bodies)
// =====================================================================

function Timedelta_mk(days: int, seconds: int, microseconds: int): int {
  ((days * 3600 * 24) + seconds) * 1000000 + microseconds
}

function Datetime_sub(d: Datetime, timedelta: int): Datetime {
  Datetime_add(d, -timedelta)
}

// =====================================================================
// Procedure Declarations (without bodies)
// =====================================================================

procedure importFrom(module: string, names: ListStr, level: int)
procedure import(names: ListStr)
procedure print(msg: string, opt: StrOrNone)

procedure json_dumps(msg: DictStrAny, opt_indent: IntOrNone)
  returns (s: string, maybe_except: ExceptOrNone)

procedure json_loads(msg: string)
  returns (d: DictStrAny, maybe_except: ExceptOrNone)

procedure input(msg: string)
  returns (result: string, maybe_except: ExceptOrNone)

procedure random_choice(l: ListStr)
  returns (result: string, maybe_except: ExceptOrNone)

procedure str_to_float(s: string)
  returns (result: string, maybe_except: ExceptOrNone)

procedure datetime_date(dt: Datetime)
  returns (d: Datetime, maybe_except: ExceptOrNone)

// =====================================================================
// Procedure Declarations (with ensures/bodies)
// =====================================================================

procedure datetime_now()
  returns (d: Datetime, maybe_except: ExceptOrNone)
  ensures Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0)
{
  assume Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0);
}

procedure datetime_utcnow()
  returns (d: Datetime, maybe_except: ExceptOrNone)
  ensures Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0)
{
  assume Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0);
}

procedure timedelta(days: IntOrNone, hours: IntOrNone)
  returns (delta: int, maybe_except: ExceptOrNone)
 {
   var days_i : int := 0;
   if (IntOrNone..isIntOrNone_mk_int(days)) {
         days_i := IntOrNone..int_val!(days);
   }
   var hours_i : int := 0;
   if (IntOrNone..isIntOrNone_mk_int(hours)) {
         hours_i := IntOrNone..int_val!(hours);
   }
   // [assume_timedelta_sign_matches]:
   assume (delta == (((days_i * 24) + hours_i) * 3600) * 1000000);
 }

// Works around the end macro being parsed as field selection by changing the parser state
// Better fix is to require laurel procedures to end with ;
datatype Workaround { Dummy() }

#end

/--
Parse the Laurel DDM prelude into a Laurel Program.
-/
def pythonPreludeInLaurel : Laurel.Program :=
  let uri := Strata.Uri.file "Strata/Languages/Python/PythonPreludeInLaurel.lean"
  match Laurel.TransM.run uri (Laurel.parseProgram pythonPreludeLaurelDDM) with
  | .ok p => p
  | .error e => panic! s!"Failed to parse Python Laurel prelude: {e}"

end Python
end Strata
