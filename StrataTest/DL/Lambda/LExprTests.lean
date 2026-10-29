/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LExpr

meta section

namespace Lambda.LExpr.SyntaxTests

open Lambda
open LExpr
open LExpr.SyntaxMono
open LTy.Syntax

-- Tests for mono syntax (esM[...])

/--
info: app () (absUntyped () (bvar () 0))
  (const () (LConst.intConst (Int.ofNat 5))) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[((λ %0) #5)]

/--
info: app () (abs () "" (some (LMonoTy.tcons "bool" [])) (bvar () 0))
  (const () (LConst.boolConst true)) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[((λ (bool): %0) #true)]

/--
info: allUntyped ()
  (eq () (bvar () 0) (const () (LConst.intConst (Int.ofNat 5)))) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[(∀ %0 == #5)]

/--
info: existUntyped ()
  (eq () (bvar () 0) (const () (LConst.intConst (Int.ofNat 5)))) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[(∃ %0 == #5)]

/--
info: exist () "" (some (LMonoTy.tcons "int" []))
  (eq () (bvar () 0) (const () (LConst.intConst (Int.ofNat 5)))) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[(∃ (int): %0 == #5)]

/--
info: fvar () { name := "x", metadata := () }
  (some (LMonoTy.tcons "bool" [])) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check esM[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all () "" (some (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]))
  (all () "" (some (LMonoTy.ftvar "k"))
    (all () "" (some (LMonoTy.ftvar "v"))
      (eq ()
        (app ()
          (app ()
            (op () { name := "select", metadata := () }
              (some
                (LMonoTy.tcons "Map"
                  [LMonoTy.ftvar "k",
                    LMonoTy.tcons "arrow"
                      [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]])))
            (app ()
              (app ()
                (app ()
                  (op () { name := "update", metadata := () }
                    (some
                      (LMonoTy.tcons "Map"
                        [LMonoTy.ftvar "k",
                          LMonoTy.tcons "arrow"
                            [LMonoTy.ftvar "v",
                              LMonoTy.tcons "arrow"
                                [LMonoTy.ftvar "k",
                                  LMonoTy.tcons "arrow"
                                    [LMonoTy.ftvar "v",
                                      LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]])))
                  (bvar () 2))
                (bvar () 1))
              (bvar () 0)))
          (bvar () 1))
        (bvar () 0)))) : LExpr { Metadata := Unit, IDMeta := Unit }.mono
-/
#guard_msgs in
#check
  esM[∀ (Map %k %v):
            (∀ (%k):
               (∀ (%v):
                  (((~select : Map %k %v → %k → %v)
                     ((((~update : Map %k %v → %k → %v → Map %k %v) %2) %1) %0)) %1) == %0))]

-- Tests for poly syntax (es[...])

open LExpr.Syntax

/--
info: const () (LConst.intConst (Int.ofNat 5)) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[#5]

/--
info: app () (absUntyped () (bvar () 0))
  (const () (LConst.intConst (Int.ofNat 5))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[((λ %0) #5)]

/--
info: app () (abs () "" (some (LTy.forAll [] (LMonoTy.tcons "bool" []))) (bvar () 0))
  (boolConst () true) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[((λ (bool): %0) #true)]

/--
info: allUntyped ()
  (eq () (bvar () 0)
    (const ()
      (LConst.intConst (Int.ofNat 5)))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∀ %0 == #5)]

/--
info: existUntyped ()
  (eq () (bvar () 0)
    (const ()
      (LConst.intConst (Int.ofNat 5)))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∃ %0 == #5)]

/--
info: exist () "" (some (LTy.forAll [] (LMonoTy.tcons "int" [])))
  (eq () (bvar () 0)
    (const ()
      (LConst.intConst (Int.ofNat 5)))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∃ (int): %0 == #5)]

/--
info: fvar () { name := "x", metadata := () }
  (some
    (LTy.forAll [] (LMonoTy.tcons "bool" []))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check es[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all () "" (some (LTy.forAll [] (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"])))
  (all () "" (some (LTy.forAll [] (LMonoTy.ftvar "k")))
    (all () "" (some (LTy.forAll [] (LMonoTy.ftvar "v")))
      (eq ()
        (app ()
          (app ()
            (op () { name := "select", metadata := () }
              (some
                (LTy.forAll []
                  (LMonoTy.tcons "Map"
                    [LMonoTy.ftvar "k",
                      LMonoTy.tcons "arrow"
                        [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]))))
            (app ()
              (app ()
                (app ()
                  (op () { name := "update", metadata := () }
                    (some
                      (LTy.forAll []
                        (LMonoTy.tcons "Map"
                          [LMonoTy.ftvar "k",
                            LMonoTy.tcons "arrow"
                              [LMonoTy.ftvar "v",
                                LMonoTy.tcons "arrow"
                                  [LMonoTy.ftvar "k",
                                    LMonoTy.tcons "arrow"
                                      [LMonoTy.ftvar "v",
                                        LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]]))))
                  (bvar () 2))
                (bvar () 1))
              (bvar () 0)))
          (bvar () 1))
        (bvar () 0)))) : LExpr { base := { Metadata := Unit, IDMeta := Unit }, TypeType := LTy }
-/
#guard_msgs in
#check
  es[∀ (Map %k %v):
            (∀ (%k):
               (∀ (%v):
                  (((~select : Map %k %v → %k → %v)
                     ((((~update : Map %k %v → %k → %v → Map %k %v) %2) %1) %0)) %1) == %0))]

-- `mkHave` desugars `have x = value in body` to `app (abs x. body) value`,
-- introducing no new AST node. The body refers to the bound value positionally
-- via `%0`. Untyped binder: `have x = #5 in (x == #1)`.
#guard LExpr.mkHave () "x" none esM[#5] esM[%0 == #1] ==
       LExpr.app () (LExpr.abs () "x" none esM[%0 == #1]) esM[#5]

-- Typed binder: `have x : int = #5 in (x == #5)` desugars to a typed `abs`.
#guard LExpr.mkHave () "x" (some mty[int]) esM[#5] esM[%0 == #5] ==
       LExpr.app () (LExpr.abs () "x" (some mty[int]) esM[%0 == #5]) esM[#5]

-- Nested bindings: `have x = #1 in have y = #2 in (x == y)`. The inner body
-- references the inner binding as `%0` and the outer binding as `%1`, so the
-- desugaring must nest the abstractions with the de Bruijn indices preserved.
#guard LExpr.mkHave () "x" none esM[#1]
         (LExpr.mkHave () "y" none esM[#2] esM[%1 == %0]) ==
       LExpr.app () (LExpr.abs () "x" none
         (LExpr.app () (LExpr.abs () "y" none esM[%1 == %0]) esM[#2])) esM[#1]

end Lambda.LExpr.SyntaxTests
