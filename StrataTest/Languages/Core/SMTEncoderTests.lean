/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.SMTEncoder

/-! ## Tests for SMTEncoder -/

namespace Core
open Lambda
open Strata.SMT

/-- info: "(define-fun t0 () Bool (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all (.some .int) (LExpr.noTrigger ())
   (.quant () .exist (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

/--
info: "; x\n(declare-const f0 Int)\n(define-fun t0 () Bool (exists (($__bv0 Int)) (= $__bv0 f0)))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-fun f0 (Int) Int)\n; x\n(declare-const f1 Int)\n(define-fun t0 () Bool (exists (($__bv0 Int)) (! (= $__bv0 f1) :pattern ((f0 $__bv0)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant ()  .exist (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))


/--
info: "; f\n(declare-fun f0 (Int) Int)\n; x\n(declare-const f1 Int)\n(define-fun t0 () Bool (exists (($__bv0 Int)) (! (= (f0 $__bv0) f1) :pattern ((f0 $__bv0)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/-- info: "Cannot encode expression (f %0)" -/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist (.some .int) (.app () (.fvar () "f" (.none)) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-const f0 (arrow Int Int))\n; f\n(declare-fun f1 (Int) Int)\n; x\n(declare-const f2 Int)\n(define-fun t0 () Bool (exists (($__bv0 Int)) (! (= (f1 $__bv0) f2) :pattern (f0))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist (.some .int)
   (mkTriggerExpr [[.fvar () "f" (.some (.arrow .int .int))]])
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))
   (ctx := SMT.Context.default)
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

/--
info: "; f\n(declare-fun f0 (Int Int) Int)\n; x\n(declare-const f1 Int)\n(define-fun t0 () Bool (forall (($__bv0 Int) ($__bv1 Int)) (! (= (f0 $__bv1 $__bv0) f1) :pattern ((f0 $__bv1 $__bv0)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .all (.some .int) (.bvar () 0) (.quant () .all (.some .int) (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1))
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] False [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none []
      }
   }})


/--
info: "; f\n(declare-fun f0 (Int Int) Int)\n; x\n(declare-const f1 Int)\n(define-fun t0 () Bool (forall (($__bv0 Int) ($__bv1 Int)) (= (f0 $__bv1 $__bv0) f1)))\n"
-/
#guard_msgs in -- No valid trigger
#eval toSMTTermString
   (.quant () .all (.some .int) (.bvar () 0) (.quant () .all (.some .int) (.bvar () 0)
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] False [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none []
      }
   }})

/-! ## Tests for multi-argument fvar application -/

-- Two-argument fvar: g(a, b) where g : int → int → bool
-- The fix ensures all argument types are collected via destructArrow,
-- not just the first arrow layer.
/--
info: "; a\n(declare-const f0 Int)\n(define-fun t0 () Int f0)\n; b\n(declare-const f1 Int)\n(define-fun t1 () Int f1)\n; g\n(declare-fun f2 (Int Int) Bool)\n(define-fun t2 () Bool (f2 t0 t1))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.app () (.app () (.fvar () "g" (.some (.arrow .int (.arrow .int .bool)))) (.fvar () "a" (.some .int))) (.fvar () "b" (.some .int)))

-- Three-argument fvar: h(a, b, c) where h : int → int → int → int
/--
info: "; a\n(declare-const f0 Int)\n(define-fun t0 () Int f0)\n; b\n(declare-const f1 Int)\n(define-fun t1 () Int f1)\n; c\n(declare-const f2 Int)\n(define-fun t2 () Int f2)\n; h\n(declare-fun f3 (Int Int Int) Int)\n(define-fun t3 () Int (f3 t0 t1 t2))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.app () (.app () (.app () (.fvar () "h" (.some (.arrow .int (.arrow .int (.arrow .int .int))))) (.fvar () "a" (.some .int))) (.fvar () "b" (.some .int))) (.fvar () "c" (.some .int)))

/-! ## Tests for Map type SMT encoding -/

-- Map int bool should encode as (Array Int Bool)
/--
info: "; m\n(declare-const f0 (Array Int Bool))\n(define-fun t0 () (Array Int Bool) f0)\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.fvar () "m" (.some (.tcons "Map" [.int, .bool])))

-- Nested Map: Map int (Map int bool) → (Array Int (Array Int Bool))
/--
info: "; m\n(declare-const f0 (Array Int (Array Int Bool)))\n(define-fun t0 () (Array Int (Array Int Bool)) f0)\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.fvar () "m" (.some (.tcons "Map" [.int, .tcons "Map" [.int, .bool]])))

end Core
