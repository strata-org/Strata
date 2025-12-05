/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExprWF
import Strata.DL.Util.Maps

namespace Lambda

open Std (ToFormat Format format)

---------------------------------------------------------------------

/-! ### Variable scopes

We keep a stack of `Scopes`, where we map in-scope free variables to the
`LExpr` values.

While the evaluation of Lambda expressions does not strictly need the notion of
scopes, other dialects that include Lambda may need to do so. For the evaluation
of Lambda expressions in isolation, the stack can contain a single scope.
-/

variable {T : LExprParams} [Inhabited T.Metadata] [BEq T.Metadata] [DecidableEq T.IDMeta] [BEq T.IDMeta] [ToFormat T.IDMeta] [BEq (LExpr T.mono)] [ToFormat (LExpr T.mono)]

def Scope (T : LExprParams) : Type := Map T.Identifier (Option LMonoTy × (LExpr T.mono))

def Scope.ofMap (m : Map T.Identifier (Option LMonoTy × (LExpr T.mono))) : Scope T := m
def Scope.toMap (s : Scope T) : Map T.Identifier (Option LMonoTy × (LExpr T.mono)) := s

instance : BEq (Scope T) where
  beq m1 m2 := m1.toMap == m2.toMap

instance : Inhabited (Scope T) where
  default := Scope.ofMap []

private def Scope.format (m : Scope T) : Std.Format :=
  match m with
  | [] => ""
  | [(k, (ty, v))] => go k ty v
  | (k, (ty, v)) :: rest =>
    go k ty v ++ Format.line ++ Scope.format rest
  where go k ty v :=
    match ty with
    | some ty => f!"({k} : {ty}) → {v}"
    | none => f!"{k} → {v}"

instance (priority := high) : ToFormat (Scope T) where
  format := Scope.format

/--
Merge two maps `m1` and `m2`, where `m1` is assumed to be the map if `cond`
is `true` and `m2` when it is false.
-/
def Scope.merge (cond : LExpr T.mono) (m1 m2 : Scope T) : Scope T :=
  match m1 with
  | [] => m2.map (fun (i, (ty, e)) => (i, (ty, mkIte cond (.fvar (default : T.Metadata) i ty) e)))
  | (k, (ty1, e1)) :: rest =>
    match m2.find? k with
    | none =>
      (k, (ty1, mkIte cond e1 (.fvar (default : T.Metadata) k ty1))) ::
      Scope.merge cond rest m2
    | some (ty2, e2) =>
      if ty1 ≠ ty2 then
        panic! s!"[Scope.merge] Variable {Std.format k} is of two different types \
                  in the two varMaps\n\
                  {Std.format m1}\n{Std.format m2}"
      else
        (k, (ty1, mkIte cond e1 e2)) ::
      Scope.merge cond rest (m2.erase k)
  where mkIte (cond tru fals : LExpr T.mono) : LExpr T.mono :=
    if tru == fals then tru
    else (LExpr.ite (default : T.Metadata) cond tru fals)

section Scope.merge.tests
open LTy.Syntax LExpr.SyntaxMono

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

/--
info: (x : int) → #8
(z : int) → (if #true then #100 else (z : int))
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]
              [("x", (mty[int], .intConst () 8))]

/--
info: (x : int) → (if #true then #8 else (x : int))
(z : int) → (if #true then #100 else (z : int))
(y : int) → (if #true then (y : int) else #8)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]
              [("y", (mty[int], .intConst () 8))]

/--
info: (y : int) → (if #true then #8 else (y : int))
(x : int) → (if #true then (x : int) else #8)
(z : int) → (if #true then (z : int) else #100)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("y", (mty[int], .intConst () 8 ))]
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]

/--
info: (a : int) → (if #true then #8 else (a : int))
(x : int) → (if #true then #800 else #8)
(b : int) → (if #true then #900 else (b : int))
(z : int) → (if #true then (z : int) else #100)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
                [("a", (mty[int], (.intConst () 8))),
                 ("x", (mty[int], (.intConst () 800))),
                 ("b", (mty[int], (.intConst () 900)))]
                [("x", (mty[int], (.intConst () 8))),
                 ("z", (mty[int], (.intConst () 100)))]

end Scope.merge.tests

/--
A stack of scopes, where each scope maps the free variables
to their `LExpr` values.
-/
abbrev Scopes (T : LExprParams) := Maps T.Identifier (Option LMonoTy × LExpr T.mono)

/--
Merge two scopes, where `s1` is assumed to be the scope if `cond` is true, and
`s2` otherwise.
-/
def Scopes.merge (cond : LExpr T.mono) (s1 s2 : Scopes T) : Scopes T :=
  match s1, s2 with
  | [], _ => s2
  | _, [] => s1
  | x :: xrest, y :: yrest =>
    Scope.merge cond x y :: Scopes.merge cond xrest yrest

--------------------------------------------------------------------

end Lambda
