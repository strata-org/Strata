/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

namespace Strata
namespace Python

/-
The Python Laurel prelude, written in Laurel syntax via the `#strata program Laurel` macro.

Translation notes vs CorePrelude:
- Core `datatype T (err: Type, ok: Type) { ... }` with type parameters → Laurel datatypes
  don't support type parameters yet. `Except` is written as a monomorphic datatype
  (Except_getOK: string, Except_getErr: Error). TODO: add type-parameter support to Laurel.
- Core `type ExceptErrorRegex := Except Error regex` → no type alias in Laurel yet; omitted.
- Core `regex` type → not in Laurel grammar types; `PyReMatchRegex` uses `string` for pattern.
- Core `axiom [PyReMatchRegex_def_noFlg]: (forall ...)` → complex SMT axiom, not expressible
  as `ensures`; omitted (PyReMatchRegex is left as an opaque procedure without postcondition).
- Core `axiom (forall s1:StrOrNone, s2:StrOrNone :: ...)` injectivity axiom for
  `strOrNone_toObject` → multi-variable forall, not expressible as `ensures`; omitted.
- Core `axiom (forall s:StrOrNone :: ... Object_len(...) == str.len(...))` → uses
  datatype discriminator `StrOrNone..isStrOrNone_mk_str` not available in Laurel; omitted.
- Core `axiom [Timedelta_deconstructors]: (forall days0, seconds0, msecs0, days, seconds, msecs :: ...)`
  → multi-variable forall with complex body; not expressible as `ensures`; omitted.
- Core `axiom [Datetime_add_ax]` has two conjuncts (base preserved AND timedelta updated);
  Laurel `ensures` can only express one postcondition per clause — both are included as
  separate `ensures` clauses.
- Core `axiom [Datetime_lt_ax]: (forall d1, d2 :: ... ==> Datetime_lt(...) == ...)` →
  conditional equality with forall; not expressible as `ensures`; omitted.
- Core `datetime_strptime` has `ensures (forall dt :: ...)` → forall in ensures; omitted.
- Core `test_helper_procedure` uses datatype discriminator expressions
  (`StrOrNone..isStrOrNone_mk_none`, `StrOrNone..isStrOrNone_mk_str`, `StrOrNone..str_val`)
  and a body with `assert`/`assume` — these use Core-specific syntax not available in Laurel.
  The procedure is included with only the first `requires` clause expressible in Laurel.
- Core `timedelta` has a real body with `if (IntOrNone..isIntOrNone_mk_int(...))` — uses
  datatype discriminator syntax not available in Laurel; included as opaque.
- Core `Timedelta_mk` is a pure function with a definition body; translated as a procedure
  with `ensures` (Laurel has no `function` keyword).
- Core `Datetime_sub` is defined as `Datetime_add(d, -timedelta)`; translated as opaque
  procedure with `ensures` for base preservation.
- Core `datetime_to_int` is a 0-ary function; translated as a procedure with no parameters.
- Core `BoolOrNone_mk_str(str_val: string)` — preserved exactly (not `bool_val: bool`).
- Core `importFrom(module, names: ListStr, level)` — `names` parameter preserved.
- Core `import(names: ListStr)` — included.
-/
set_option maxRecDepth 10000 in
def laurelPreludeDDM :=
#strata
program Laurel;

datatype None { None_none() }

datatype Object {}

procedure Object_len(x: Object) returns (result: int)
  ensures result >= 0

procedure inheritsFrom(child: string, parent: string) returns (result: bool)

datatype Error {
  Error_TypeError(getTypeError: string),
  Error_AttributeError(getAttributeError: string),
  Error_RePatternError(getRePatternError: string),
  Error_Unimplemented(getUnimplemented: string)
}

// TODO: Except is generic in Core (Except (err: Type, ok: Type)); Laurel datatypes do not
// support type parameters yet. Monomorphised here as Except Error string.
datatype Except {
  Except_mkOK(Except_getOK: string),
  Except_mkErr(Except_getErr: Error)
}

// TODO: ExceptErrorRegex = Except Error regex — no type alias or regex type in Laurel yet.

// TODO: PyReMatchRegex axiom (forall pattern, str :: PyReMatchRegex(pattern,str,0) ==
// str.in.re(str,pattern)) uses regex type and SMT re semantics; not expressible in Laurel.
procedure PyReMatchRegex(pattern: string, str: string, flags: int) returns (result: bool)

procedure PyReMatchStr(pattern: string, str: string, flags: int) returns (result: Except)

datatype ListStr {
  ListStr_nil(),
  ListStr_cons(head: string, tail: ListStr)
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

// TODO: strOrNone_toObject injectivity axiom (forall s1, s2 :: s1 != s2 ==>
// strOrNone_toObject(s1) != strOrNone_toObject(s2)) — multi-variable forall, not
// expressible as ensures. Object_len axiom uses datatype discriminator syntax; omitted.
procedure strOrNone_toObject(v: StrOrNone) returns (result: Object)

datatype AnyOrNone {
  AnyOrNone_mk_str(str_val: string),
  AnyOrNone_mk_none(none_val: None)
}

// NOTE: BoolOrNone_mk_str has str_val: string (not bool_val: bool) — matches CorePrelude exactly.
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

datatype DictStrAny {}
procedure DictStrAny_mk(s: string) returns (result: DictStrAny)

datatype ListDictStrAny {}
procedure ListDictStrAny_nil( ) returns (result: ListDictStrAny)

datatype Client {
  Client_S3(),
  Client_CW()
}

// Timedelta is represented as an int (microseconds).
// TODO: timedelta body uses IntOrNone..isIntOrNone_mk_int discriminator syntax not
// available in Laurel; included as opaque.
procedure timedelta(days: IntOrNone, hours: IntOrNone) returns (delta: int, maybe_except: ExceptOrNone)

// Timedelta_mk: ((days * 3600 * 24) + seconds) * 1000000 + microseconds
procedure Timedelta_mk(days: int, seconds: int, microseconds: int) returns (result: int)
  ensures result == (((days * 3600 * 24) + seconds) * 1000000 + microseconds)

procedure Timedelta_get_days(td: int) returns (result: int)
procedure Timedelta_get_seconds(td: int) returns (result: int)
procedure Timedelta_get_microseconds(td: int) returns (result: int)

// TODO: Timedelta_deconstructors axiom (forall days0, seconds0, msecs0, days, seconds, msecs
// :: ...) — multi-variable forall with complex body; not expressible as ensures.

datatype Datetime {}
datatype Datetime_base {}

procedure Datetime_get_base(d: Datetime) returns (result: Datetime_base)
procedure Datetime_get_timedelta(d: Datetime) returns (result: int)

procedure datetime_now( ) returns (d: Datetime, maybe_except: ExceptOrNone)
  ensures Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0)

procedure datetime_utcnow( ) returns (d: Datetime, maybe_except: ExceptOrNone)
  ensures Datetime_get_timedelta(d) == Timedelta_mk(0, 0, 0)

// Datetime_add: both conjuncts from Core axiom [Datetime_add_ax] expressed as separate ensures.
procedure Datetime_add(d: Datetime, timedelta: int) returns (result: Datetime)
  ensures Datetime_get_base(result) == Datetime_get_base(d)
  ensures Datetime_get_timedelta(result) == (Datetime_get_timedelta(d) + timedelta)

// Datetime_sub is defined in Core as Datetime_add(d, -timedelta).
procedure Datetime_sub(d: Datetime, timedelta: int) returns (result: Datetime)
  ensures Datetime_get_base(result) == Datetime_get_base(d)
  ensures Datetime_get_timedelta(result) == (Datetime_get_timedelta(d) - timedelta)

// TODO: Datetime_lt axiom (forall d1, d2 :: Datetime_get_base(d1) == Datetime_get_base(d2)
// ==> Datetime_lt(d1,d2) == (Datetime_get_timedelta(d1) < Datetime_get_timedelta(d2))) —
// conditional forall, not expressible as ensures.
procedure Datetime_lt(d1: Datetime, d2: Datetime) returns (result: bool)

datatype Date {}

procedure datetime_date(dt: Datetime) returns (d: Datetime, maybe_except: ExceptOrNone)

procedure datetime_to_str(dt: Datetime) returns (result: string)

// datetime_to_int is a 0-ary function in Core; translated as a no-parameter procedure.
procedure datetime_to_int( ) returns (result: int)

// TODO: datetime_strptime ensures clause has (forall dt :: ...) — forall in ensures not
// expressible in Laurel; only the requires clause is preserved.
procedure datetime_strptime(time: string, format: string) returns (d: Datetime, maybe_except: ExceptOrNone)
  requires format == "%Y-%m-%d"

// TODO: importFrom in Core has names: ListStr parameter; preserved here.
procedure importFrom(module: string, names: ListStr, level: int) returns ( )

procedure import(names: ListStr) returns ( )

procedure print(msg: string, opt: StrOrNone) returns ( )

procedure json_dumps(msg: DictStrAny, opt_indent: IntOrNone) returns (s: string, maybe_except: ExceptOrNone)
procedure json_loads(msg: string) returns (d: DictStrAny, maybe_except: ExceptOrNone)
procedure input(msg: string) returns (result: string, maybe_except: ExceptOrNone)
procedure random_choice(l: ListStr) returns (result: string, maybe_except: ExceptOrNone)

procedure str_in_list_str(s: string, l: ListStr) returns (result: bool)
procedure str_in_dict_str_any(s: string, d: DictStrAny) returns (result: bool)
procedure list_str_get(l: ListStr, i: int) returns (result: string)
procedure str_len(s: string) returns (result: int)
procedure dict_str_any_get(d: DictStrAny, k: string) returns (result: DictStrAny)
procedure dict_str_any_get_list_str(d: DictStrAny, k: string) returns (result: ListStr)
procedure dict_str_any_get_str(d: DictStrAny, k: string) returns (result: string)
procedure dict_str_any_length(d: DictStrAny) returns (result: int)

procedure str_to_float(s: string) returns (result: string, maybe_except: ExceptOrNone)

procedure Float_gt(lhs: string, rhs: string) returns (result: bool)

// TODO: test_helper_procedure has requires/ensures using datatype discriminator expressions
// (StrOrNone..isStrOrNone_mk_none, StrOrNone..isStrOrNone_mk_str, StrOrNone..str_val) and
// a body with assert/assume — Core-specific syntax not available in Laurel. Only the first
// requires clause (req_name == "foo") is expressible in Laurel.
procedure test_helper_procedure(req_name: string, opt_name: StrOrNone) returns (maybe_except: ExceptOrNone)
  requires req_name == "foo"

datatype PyAnyType {
  PyAnyType_Inhabitant()
}

#end

/--
The Python Laurel prelude as a `Laurel.Program`, parsed at compile time via the
`#strata program Laurel` macro.
-/
def Laurel.prelude : Laurel.Program :=
  let uri := Strata.Uri.file "Strata/Languages/Python/LaurelPrelude.lean"
  match Laurel.TransM.run uri (Laurel.parseProgram laurelPreludeDDM) with
  | .ok program => program
  | .error e => panic! s!"Python LaurelPrelude parse error: {e}"

end Python
end Strata
