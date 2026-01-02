/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie

namespace Strata
namespace Python

/-- A type identifier in the Python Boogie prelude. -/
abbrev TypeId := String

/-- An argument declaration for a Python method -/
structure ArgDecl where
  name : String
  type : TypeId
deriving Inhabited

/-- A function signature with argument information. -/
structure FuncDecl where
  /-- Array of arguments. -/
  args : Array ArgDecl
  /--
  Number of position-only arguments.

  Position only arguments occur before other arguments.
  -/
  posOnlyCount : Nat := 0
  /--
  First index for keyword only arguments.

  Keyword only arguments appear after other arguments in args.
   -/
  keywordOnly : Nat := args.size
  /--
  Position only arguments are before start of keyword only.
  -/
  posOnlyBound : posOnlyCount <= keywordOnly := by omega
  /--
  Keyword only arguments (if any) come at end
  -/
  keywordBound : keywordOnly <= args.size := by omega
  /-- Map from argument names to their index in args. -/
  argIndexMap : Std.HashMap String (Fin args.size)

instance : Inhabited FuncDecl where
  default := { args := #[], argIndexMap := {} }

/-- The name of a Python method as encoded in the Boogie dialect-/
abbrev FuncName := String

/-- A collection of function signatures. -/
class Signatures where
  functions : Std.HashMap FuncName FuncDecl := {}
deriving Inhabited

namespace Signatures

def getFuncSigOrder (db : Signatures) (fname: FuncName) : List String :=
  match  db.functions[fname]? with
  | some decl => decl.args |>.map (·.name) |>.toList
  | none => panic! s!"Missing function signature : {fname}"

-- We should extract the function signatures from the prelude:
def getFuncSigType (db : Signatures) (fname: FuncName) (arg: String) : String :=
  match  db.functions[fname]? with
  | none => panic! s!"Missing function signature : {fname}"
  | some decl =>
    match decl.argIndexMap[arg]? with
    | none => panic! s!"Unrecognized arg : {arg}"
    | some idx => decl.args[idx].type

end Signatures

/--
Monad for extending a signatures collection.
-/
def SignatureM := StateM Signatures
deriving Monad, MonadState Signatures

namespace SignatureM

def run (m : SignatureM Unit) (init : Signatures := {}) : Signatures := m init |>.snd

def decl (name : FuncName) (args : List ArgDecl)
         (posOnlyCount : Nat := 0)
         (keywordOnly := args.length) : SignatureM Unit := do
  assert! name ∉ (←get).functions
  assert! posOnlyCount <= keywordOnly
  let args := args.toArray
  assert! keywordOnly <= args.size

  let argIndexMap : Std.HashMap String (Fin args.size) :=
    Fin.foldl args.size (init := {}) fun m i =>
      let a := args[i]
      assert! a.name ∉ m
      m.insert a.name i

  let .isTrue posOnlyBound := inferInstanceAs (Decidable (posOnlyCount <= keywordOnly))
    | return panic! "Invalid number of position-only parameters."
  let .isTrue keywordBound := inferInstanceAs (Decidable (keywordOnly <= args.size))
    | return panic! "Invalid start for keyword only parameters."

  let decl : FuncDecl := {
    args,
    posOnlyCount,
    keywordOnly,
    posOnlyBound,
    keywordBound,
    argIndexMap,
  }
  modify fun m => { m with functions := m.functions.insert name decl }

private def identToStr (t : Lean.TSyntax `ident) : Lean.StrLit :=
  match t.raw.isIdOrAtom? with
  | none => panic! "Unexpected string"
  | some s => Lean.Syntax.mkStrLit s

scoped macro v:ident ":<" t:ident : term => `(ArgDecl.mk $(identToStr v) $(identToStr t))

end SignatureM

section
open SignatureM

def addCoreDecls : SignatureM Unit := do
  decl "test_helper_procedure" [req_name :< string, opt_name :< StrOrNone]
  decl "print" [msg :< string, opt :< StrOrNone]
  decl "json_dumps" [msg :< DictStrAny, opt_indent :< IntOrNone]
  decl "json_loads" [msg :< string]
  decl "input" [msg :< string]
  decl "random_choice" [l :< ListStr]
  decl "datetime_now" []
  decl "datetime_utcnow" []
  decl "datetime_date" [dt :< Datetime]
  decl "timedelta" [ days :< IntOrNone, hours :< IntOrNone]
  decl "datetime_strptime" [time :< string, format :< string]
  decl "str_to_float" [s :< string]

def coreSignatures : Signatures := addCoreDecls |>.run

end

def TypeStrToBoogieExpr (ty: String) : Boogie.Expression.Expr :=
  if !ty.endsWith "OrNone" then
    panic! s!"Should only be called for possibly None types. Called for: {ty}"
  else
    match ty with
    | "StrOrNone" => .app () (.op () "StrOrNone_mk_none" none) (.op () "None_none" none)
    | "BoolOrNone" => .app () (.op () "BoolOrNone_mk_none" none) (.op () "None_none" none)
    | "BoolOrStrOrNone" => .app () (.op () "BoolOrStrOrNone_mk_none" none) (.op () "None_none" none)
    | "AnyOrNone" => .app () (.op () "AnyOrNone_mk_none" none) (.op () "None_none" none)
    | "IntOrNone" => .app () (.op () "IntOrNone_mk_none" none) (.op () "None_none" none)
    | "BytesOrStrOrNone" => .app () (.op () "BytesOrStrOrNone_mk_none" none) (.op () "None_none" none)
    | "DictStrStrOrNone" => .app () (.op () "DictStrStrOrNone_mk_none" none) (.op () "None_none" none)
    | _ => panic! s!"unsupported type: {ty}"

end Python
end Strata
