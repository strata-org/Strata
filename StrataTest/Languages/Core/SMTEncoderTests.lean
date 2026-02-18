/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier

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

/-! ## Tests for Array Theory Support -/

section ArrayTheory

-- Test map select with Array theory enabled
/--
info: "; m\n(declare-const f0 (Array Int Int))\n(define-fun t0 () (Array Int Int) f0)\n; i\n(declare-const f1 Int)\n(define-fun t1 () Int f1)\n(define-fun t2 () Int (select t0 t1))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app () (.app () (.op () "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.fvar () "m" (.some (mapTy .int .int))))
    (.fvar () "i" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test map update with Array theory enabled
/--
info: "; m\n(declare-const f0 (Array Int Int))\n(define-fun t0 () (Array Int Int) f0)\n; i\n(declare-const f1 Int)\n(define-fun t1 () Int f1)\n; v\n(declare-const f2 Int)\n(define-fun t2 () Int f2)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app () (.app () (.app () (.op () "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
    (.fvar () "m" (.some (mapTy .int .int))))
    (.fvar () "i" (.some .int)))
    (.fvar () "v" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test nested map operations with Array theory
/--
info: "; m\n(declare-const f0 (Array Int Int))\n(define-fun t0 () (Array Int Int) f0)\n; i\n(declare-const f1 Int)\n(define-fun t1 () Int f1)\n; v\n(declare-const f2 Int)\n(define-fun t2 () Int f2)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n; j\n(declare-const f3 Int)\n(define-fun t4 () Int f3)\n(define-fun t5 () Int (select t3 t4))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app () (.app () (.op () "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.app () (.app () (.app () (.op () "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
      (.fvar () "m" (.some (mapTy .int .int))))
      (.fvar () "i" (.some .int)))
      (.fvar () "v" (.some .int))))
    (.fvar () "j" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

end ArrayTheory

end Core

/-! ## End-to-End Test with Complete Program -/

namespace Strata

-- Simple program that uses maps
def simpleMapProgram :=
#strata
program Core;

var m : Map int int;

procedure UpdateAndRead(k : int, v : int) returns (result : int)
spec {
    modifies m;
    ensures result == v;
}
{
    m := m[k := v];
    result := m[k];
};
#end

-- Test verification with axiomatized maps (default)
/--
info:
Obligation: UpdateAndRead_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify simpleMapProgram (options := {Options.quiet with useArrayTheory := false})

-- Test verification with Array theory
/--
info:
Obligation: UpdateAndRead_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify simpleMapProgram (options := {Options.quiet with useArrayTheory := true})

end Strata
