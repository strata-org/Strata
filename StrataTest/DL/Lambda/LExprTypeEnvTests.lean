/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv

/-! ## Tests for LExprTypeEnv -/

namespace Lambda
open Std (ToFormat Format format)
open LTy.Syntax

-- Only `FooAlias` is dealiased, not `BarAlias`. Note that the type variables
-- are instantiated appropriately and the global substitution is updated.
-- See `resolveAliases` for a version that also de-aliases `BarAlias`.
/--
info: ok: Ans: (Foo $__ty0 (BarAlias $__ty0 $__ty0))
Subst:
[(p, $__ty0) ($__ty1, (BarAlias $__ty0 $__ty0))]
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

/-- info: ok: (Foo $__ty0 (BarAlias q $__ty0)) -/
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
info: ok: De-aliased type: (Foo $__ty2 (Bar $__ty2 $__ty2))
Subst:
[(p, $__ty2) ($__ty0, $__ty2) ($__ty1, $__ty2) ($__ty3, (Bar $__ty2 $__ty2))]
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
                            { @LContext.default ⟨Unit, String⟩ with
                                knownTypes := makeKnownTypes [LTy.toKnownType! t[∀a. myTy %a],
                                               LTy.toKnownType! t[int]] }

abbrev TTyDefault: LExprParams := {Metadata := Unit, IDMeta := TyIdentifier}
/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[Foo] (@LContext.default TTyDefault)

/--
info: error: Type (arrow int Foo) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, int, bool]
-/
#guard_msgs in
#eval do let ans ← t[int → Foo].instantiateWithCheck (@LContext.default TTyDefault) (@TEnv.default TyIdentifier)
         return format ans

/-- info: ok: (arrow int bool) -/
#guard_msgs in
#eval do let ans ← t[int → bool].instantiateWithCheck (@LContext.default TTyDefault) (@TEnv.default TyIdentifier)
         return format ans.fst

/-- info: (arrow $__ty0 b) -/
#guard_msgs in
#eval format $ (LTy.instantiate t[∀a. %a → %b] (@TGenEnv.default String)).fst

/--
info: ok: (x : $__ty0) (y : int) (z : $__ty0)
-/
#guard_msgs in
#eval do let ans ← (LMonoTySignature.instantiate (@LContext.default {Metadata := Unit, IDMeta := Unit})
                    ((@TEnv.default Unit).updateContext
                                          { aliases := [{ typeArgs := ["a", "b"],
                                                          name := "myInt",
                                                          type := mty[int]}] })
                    ["a", "b"]
                    [("x", mty[%a]), ("y", mty[myInt %a %b]), ("z", mty[%a])])
         return Signature.format ans.fst

end Lambda
