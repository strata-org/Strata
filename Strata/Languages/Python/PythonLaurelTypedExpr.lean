/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
# Typed Laurel Expression Builders for the Python Prelude

Type-safe wrappers around the Python Laurel prelude's runtime functions
(`from_int`, `Any..as_string!`, `DictStrAny_contains`, etc.).  These
enforce correct `HighType` at construction time so that type mismatches
are caught by the Lean type checker rather than surfacing as confusing
errors later in the Laurel or Core pipeline.

The wrapped functions correspond to declarations in
`PythonRuntimeLaurelPart.lean` and `PythonLaurelCorePrelude.lean`.
-/

public section
namespace Strata.Python.Laurel

open Strata.Laurel (HighType HighTypeMd StmtExpr StmtExprMd mkId)

abbrev Md := Imperative.MetaData Core.Expression

abbrev tyAny : HighType := .UserDefined "Any"

/--
A Laurel `StmtExprMd` tagged with its `HighType`.

The benefit is that composition of typed expressions is checked by the Lean type
system, catching mismatches like passing an `Int` where a `Bool` is expected.

The type parameter is not statically enforced; correctness depends on the helper
functions in this namespace producing the right type tag.  After a translation
error is reported, helpers may return a mistyped expression to allow continued
translation and further error collection.
-/
structure TypedStmtExpr (tp : HighType) where
  stmt : StmtExprMd

namespace TypedStmtExpr

def ofStmt {tp} (s : StmtExpr) (md : Md) (source : Option FileRange := none) : TypedStmtExpr tp :=
  { stmt := { val := s, source := source, md := md } }

def identifier (v : String) (tp : HighType) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr tp :=
  .ofStmt (.Identifier (mkId v)) md source

def literalBool (v : Bool) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr .TBool :=
  .ofStmt (.LiteralBool v) md source

def literalInt (v : Int) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr .TInt :=
  .ofStmt (.LiteralInt v) md source

def literalString (v : String) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr .TString :=
  .ofStmt (.LiteralString v) md source

def stringEq (x y : TypedStmtExpr .TString)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Eq [x.stmt, y.stmt]) md source

def intGeq (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Geq [x.stmt, y.stmt]) md source

def intLeq (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Leq [x.stmt, y.stmt]) md source

def intAdd (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.PrimitiveOp .Add [x.stmt, y.stmt]) md source

def intSub (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.PrimitiveOp .Sub [x.stmt, y.stmt]) md source

def intMul (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.PrimitiveOp .Mul [x.stmt, y.stmt]) md source

def intEq (x y : TypedStmtExpr .TInt)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Eq [x.stmt, y.stmt]) md source

def realGeq (x y : TypedStmtExpr .TReal)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Geq [x.stmt, y.stmt]) md source

def realLeq (x y : TypedStmtExpr .TReal)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Leq [x.stmt, y.stmt]) md source

def not (x : TypedStmtExpr .TBool)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Not [x.stmt]) md source

def implies (x y : TypedStmtExpr .TBool)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Implies [x.stmt, y.stmt]) md source

def or (x y : TypedStmtExpr .TBool)
    (md : Md := x.stmt.md) (source : Option FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Or [x.stmt, y.stmt]) md source

abbrev tyDictStrAny : HighType := .UserDefined "DictStrAny"

def anyIsfromNone (v : TypedStmtExpr tyAny)
    (md : Md := v.stmt.md) (source : Option FileRange := v.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "Any..isfrom_None") [v.stmt]) md source

def fromInt (v : TypedStmtExpr .TInt)
    (md : Md := v.stmt.md) (source : Option FileRange := v.stmt.source) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_int") [v.stmt]) md source

def anyAsInt (a : TypedStmtExpr tyAny)
    (md : Md := a.stmt.md) (source : Option FileRange := a.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.StaticCall (mkId "Any..as_int!") [a.stmt]) md source

def fromStr (v : TypedStmtExpr .TString) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_str") [v.stmt]) md source

def anyAsString (a : TypedStmtExpr tyAny)
    (md : Md := a.stmt.md) (source : Option FileRange := a.stmt.source) : TypedStmtExpr .TString :=
  .ofStmt (.StaticCall (mkId "Any..as_string!") [a.stmt]) md source

def anyAsFloat (a : TypedStmtExpr tyAny)
    (md : Md := a.stmt.md) (source : Option FileRange := a.stmt.source) : TypedStmtExpr .TReal :=
  .ofStmt (.StaticCall (mkId "Any..as_float!") [a.stmt]) md source

def anyAsDict (a : TypedStmtExpr tyAny)
    (md : Md := a.stmt.md) (source : Option FileRange := a.stmt.source) : TypedStmtExpr tyDictStrAny :=
  .ofStmt (.StaticCall (mkId "Any..as_Dict!") [a.stmt]) md source

def dictStrAnyContains (d : TypedStmtExpr tyDictStrAny) (k : TypedStmtExpr .TString)
    (md : Md := d.stmt.md) (source : Option FileRange := d.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "DictStrAny_contains") [d.stmt, k.stmt]) md source

def anyGet (a i : TypedStmtExpr tyAny) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "Any_get") [a.stmt, i.stmt]) md source

def strLength (a : TypedStmtExpr .TString)
    (md : Md := a.stmt.md) (source : Option FileRange := a.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.StaticCall (mkId "Str.Length") [a.stmt]) md source

def reSearchBool (pattern s : TypedStmtExpr .TString) (md : Md)
    (source : Option FileRange := none) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "re_search_bool") [pattern.stmt, s.stmt]) md source

end TypedStmtExpr

/--
A dependent pair that bundles a `HighType` and a `TypedStmtExpr` of that type.

This is used when the type is not statically known and must be checked at
runtime.
-/
abbrev SomeTypedStmtExpr := Σ(tp : HighType), TypedStmtExpr tp

namespace SomeTypedStmtExpr

def mkSome {tp} (e : TypedStmtExpr tp) : SomeTypedStmtExpr := ⟨tp, e⟩

instance : Inhabited SomeTypedStmtExpr where
  default :=
    let holeType : HighTypeMd := { val := tyAny, source := none }
    let stmt : StmtExprMd := { val := .Hole true (.some holeType), source := none }
    .mk tyAny { stmt := stmt }

end SomeTypedStmtExpr

end Strata.Python.Laurel
end
