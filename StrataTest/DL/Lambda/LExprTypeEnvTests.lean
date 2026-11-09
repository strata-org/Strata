/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LTyWF

/-! ## Tests for LExprTypeEnv -/

meta section
namespace Lambda
open Std (ToFormat Format format)
open LTy.Syntax

-- Only `FooAlias` is dealiased, not `BarAlias`. Note that the type variables
-- are instantiated appropriately and the global substitution is updated.
-- See `resolveAliases` for a version that also de-aliases `BarAlias`.
/--
info: ok: Ans: (Foo p (BarAlias p p))
Subst:
[]
-/
#guard_msgs in
#eval do let (ans, Env) ← LMonoTy.aliasDef?
                            mty[FooAlias %p (BarAlias %p %p)]
                            ( (@TEnv.default String).updateContext
                              { aliases := [{ typeArgs := ["x", "y"],
                                                         name := "FooAlias",
                                                         type := mty[Foo %x %y]},
                                                       { typeArgs := ["a", "b"],
                                                         name := "BarAlias",
                                                         type := mty[Bar %a %b]
                                                       }
                                                      ]})
          return (format f!"Ans: {ans}\n\
                            Subst:\n{Env.stateSubstInfo.subst}")

/-- info: ok: (Foo p (BarAlias q p)) -/
#guard_msgs in
#eval do let (ans, _Env) ← LMonoTy.aliasDef?
          mty[FooAlias %p (BarAlias %q %p)]
          ( (@TEnv.default String).updateContext
            { aliases := [{ typeArgs := ["x", "y"],
                                       name := "FooAlias",
                                       type := mty[Foo %x %y]},
                                     { typeArgs := ["a", "b"],
                                       name := "BarAlias",
                                       type := mty[Bar %a %b]
                                     }
                                    ]} )
          return f!"{ans}"

/-- info: ok: int -/
#guard_msgs in
#eval do let (ans, _) ← LMonoTy.aliasDef? mty[myInt]
                        ( (@TEnv.default String).updateContext
                          { aliases := [{ typeArgs := [],
                                          name := "myInt",
                                          type := mty[int]}]} )
         return format ans

/-- info: ok: bool -/
#guard_msgs in
#eval do let (ans, _) ← LMonoTy.aliasDef?
                        mty[BadBoolAlias %p %q]
                        ( (@TEnv.default String).updateContext
                          { aliases := [{ typeArgs := ["x", "y"],
                                          name := "BadBoolAlias",
                                          type := mty[bool]}]} )
         return format ans

/-- info: ok: myInt -/
#guard_msgs in
#eval do let (ans, _) ← LMonoTy.aliasDef? mty[myInt]
                        ( (@TEnv.default String).updateContext
                          { aliases := [{
                             typeArgs := ["a"],
                             name := "myInt",
                             type := mty[int]}] })
         return format ans

/-- info: ok: (myDef int) -/
#guard_msgs in
#eval do let (ans, _) ← LMonoTy.aliasDef? mty[myAlias int bool]
                        ( (@TEnv.default String).updateContext
                          { aliases := [{
                            typeArgs := ["a", "b"],
                            name := "myAlias",
                            type := mty[myDef %a]}] })
         return format ans

/--
info: ok: De-aliased type: (Foo p (Bar p p))
Subst:
[]
-/
#guard_msgs in
#eval do let (ty, Env) ← LMonoTy.resolveAliases
          mty[FooAlias %p (BarAlias %p %p)]
          ((@TEnv.default String).updateContext
            { aliases := [{ typeArgs := ["x", "y"],
                                       name := "FooAlias",
                                       type := mty[Foo %x %y]},
                                     { typeArgs := ["a", "b"],
                                       name := "BarAlias",
                                       type := mty[Bar %a %b]
                                     }
                                    ]})
          return (format f!"De-aliased type: {ty}\n\
                            Subst:\n{Env.stateSubstInfo.subst}")

/-- info: ok: (arrow bool $__ty0) -/
#guard_msgs in
#eval do let (ans, _) ← LTy.resolveAliases
                        t[∀x. (FooAlias %x %x) → %x]
                        ((@TEnv.default String).updateContext { aliases := [{
                                                        typeArgs := ["x", "y"],
                                                        name := "FooAlias",
                                                        type := mty[bool]}]} )
          return (format ans)

/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[myTy (myTy)]
                            { LContext.default (T := ⟨Unit, String⟩) with
                                knownTypes := makeKnownTypes [LTy.toKnownType! t[∀a. myTy %a],
                                               LTy.toKnownType! t[int]] }

abbrev TTyDefault: LExprParams := {Metadata := Unit, IDMeta := TyIdentifier}

private def directTypeContext : LContext TTyDefault :=
  LContext.default

private def directTypeEnv : TEnv TyIdentifier :=
  (TEnv.default : TEnv TyIdentifier).updateContext {
    aliases := [{ name := "Identity", typeArgs := ["a"], type := mty[%a] }]
  }

-- A written type resolves through the alias `Identity`.
/-- info: ok: int -/
#guard_msgs in
#eval do
  let (resolved, _) ← mty[Identity int].typeCheckSource directTypeContext directTypeEnv
    TyVarAdmissibility.all
  return format resolved

-- A written alias applied to too many arguments is rejected.
/--
info: error: Type (Identity int int) is not an instance of a previously registered type: Type alias 'Identity' expects 1 type argument(s) but was given 2
-/
#guard_msgs in
#eval do
  let (resolved, _) ← mty[Identity int int].typeCheckSource directTypeContext directTypeEnv
    TyVarAdmissibility.all
  return format resolved

-- An arity mismatch nested inside an argument is rejected.
/--
info: error: Type (Identity (Identity int int)) is not an instance of a previously registered type: Type alias 'Identity' expects 1 type argument(s) but was given 2
-/
#guard_msgs in
#eval do
  let (resolved, _) ← mty[Identity (Identity int int)].typeCheckSource directTypeContext
    directTypeEnv TyVarAdmissibility.all
  return format resolved

-- A resolved type may not name an alias.
/--
info: error: Type (Identity int) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, int, bool]
-/
#guard_msgs in
#eval do
  let resolved ← mty[Identity int].typeCheckResolved directTypeContext TyVarAdmissibility.all
  return format resolved

-- A resolved type may use an admissible type variable.
/-- info: ok: a -/
#guard_msgs in
#eval do
  let resolved ← mty[%a].typeCheckResolved directTypeContext (fun v => v == "a")
  return format resolved

-- A resolved type may not use an inadmissible type variable.
/-- info: error: Type b contains a free type variable that is not admissible here. -/
#guard_msgs in
#eval do
  let resolved ← mty[%b].typeCheckResolved directTypeContext (fun v => v == "a")
  return format resolved
/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[Foo] (LContext.default (T := TTyDefault))

/--
info: error: Type (arrow int Foo) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, int, bool]
-/
#guard_msgs in
#eval do let ans ← t[int → Foo].instantiateWithCheck (LContext.default (T := TTyDefault)) (TEnv.default : TEnv TyIdentifier)
         return format ans

/-- info: ok: (arrow int bool) -/
#guard_msgs in
#eval do let ans ← t[int → bool].instantiateWithCheck (LContext.default (T := TTyDefault)) (TEnv.default : TEnv TyIdentifier)
         return format ans.fst

/-- info: ok: (arrow $__ty0 b) -/
#guard_msgs in
#eval do let ans ← LTy.instantiate t[∀a. %a → %b] (TGenEnv.default : TGenEnv String)
         return format ans.fst

/--
info: ok: (x : $__ty0) (y : int) (z : $__ty0)
-/
#guard_msgs in
#eval do let ans ← (LMonoTySignature.instantiate (LContext.default (T := {Metadata := Unit, IDMeta := Unit}))
                    ((@TEnv.default Unit).updateContext
                                          { aliases := [{ typeArgs := ["a", "b"],
                                                          name := "myInt",
                                                          type := mty[int]}] })
                    ["a", "b"]
                    [("x", mty[%a]), ("y", mty[myInt %a %b]), ("z", mty[%a])])
         return Signature.format ans.fst

/-! ### Tests for addTypeAlias: chained resolution and preserved typeArgs -/

section AddTypeAliasTests

open LTy.Syntax in
private def testContext : LContext TTyDefault :=
  { LContext.default (T := TTyDefault) with
    knownTypes := makeKnownTypes
      ([t[∀a b. %a → %b], t[bool], t[int], t[string], t[∀a. Foo %a]].map
        (fun k => LTy.toKnownType! k)) }

-- Test (a): Chained aliases are fully resolved.
-- `FooAlias a := Foo a` and `BarAlias a := FooAlias a` should result in
-- `resolveAliases (BarAlias int)` returning `Foo int`.
/-- info: ok: (Foo int) -/
#guard_msgs in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "FooAlias", type := mty[Foo %a] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "BarAlias", type := mty[FooAlias %a] } testContext Env
  let (resolved, _) ← LMonoTy.resolveAliases mty[BarAlias int] Env
  return format resolved

-- Test (b): Stored alias preserves user-supplied typeArgs.
-- After `addTypeAlias` with `typeArgs := ["a", "b"]`, the stored alias's
-- `typeArgs` equals `["a", "b"]`.
/-- info: ok: [a, b] -/
#guard_msgs in
#eval do
  let C : LContext TTyDefault :=
    { LContext.default (T := TTyDefault) with
      knownTypes := makeKnownTypes
        ([t[∀a b. %a → %b], t[bool], t[int], t[string], t[∀a b. Foo %a %b]].map
          (fun k => LTy.toKnownType! k)) }
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a", "b"], name := "MyAlias", type := mty[Foo %a %b] } C Env
  let stored := Env.context.aliases.head!
  return format stored.typeArgs

/-! #### Adding type aliases -/

-- A second alias of the same name and arity is rejected.
/--
info: error: This type declaration's name is already a type synonym!
T := bool
Existing type synonyms' names:
[T]
-/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[int] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[bool] } testContext Env
  return f!"{Env.context.aliases}"

-- A repeated alias name is rejected even at a different arity.
/--
info: error: This type declaration's name is already a type synonym!
∀[a]. (T a) := (Foo a)
Existing type synonyms' names:
[T]
-/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[int] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "T", type := mty[Foo %a] } testContext Env
  return f!"{Env.context.aliases}"

-- Two aliases with different names are accepted.
/-- info: ok: [U := bool, T := int] -/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[int] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "U", type := mty[bool] } testContext Env
  return f!"{Env.context.aliases}"

-- An alias body may refer to an earlier alias and resolves transitively.
/-- info: ok: [U := int, T := int] -/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[int] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "U", type := mty[T] } testContext Env
  return f!"{Env.context.aliases}"

-- A parameterized alias is accepted alongside a differently named alias.
/-- info: ok: [∀[a]. (MyFoo a) := (Foo a), T := int] -/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[int] } testContext Env
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "MyFoo", type := mty[Foo %a] } testContext Env
  return f!"{Env.context.aliases}"

-- `T a := int` is rejected: the parameter `a` does not occur in the body.
/-- info: error: Type synonym 'T': type argument 'a' is not used in the definition -/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "T", type := mty[int] } testContext Env
  return f!"{Env.context.aliases}"

-- `T := Bar int` is rejected: `Bar` is not a registered type constructor.
/--
info: error: Type (Bar int) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, ∀[0]. (Foo 0), int, bool]
-/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[Bar int] } testContext Env
  return f!"{Env.context.aliases}"

-- `T := Foo int bool` is rejected: `Foo` takes one argument.
/--
info: error: Type (Foo int bool) is not an instance of a previously registered type: Type constructor 'Foo' expects 1 type argument(s) but was given 2
-/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := [], name := "T", type := mty[Foo int bool] } testContext Env
  return f!"{Env.context.aliases}"

-- `T a := Foo b` is rejected: `b` is not a parameter of `T`.
/--
info: error: [TEnv.addTypeAlias] Type definition contains free type arguments!
Name: T
Type Arguments: [a]
Type Definition: (Foo b)
-/
#guard_msgs (whitespace := lax) in
#eval do
  let Env : TEnv TyIdentifier := TEnv.default
  let Env ← TEnv.addTypeAlias
    { typeArgs := ["a"], name := "T", type := mty[Foo %b] } testContext Env
  return f!"{Env.context.aliases}"

end AddTypeAliasTests

end Lambda
end
