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

/-- info: "(define-fun t0 () Bool (forall ((n Int)) (exists ((m Int)) (= n m))))\n" -/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .all "n" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.quant Strata.SourceRange.none .exist "m" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 1) (.bvar Strata.SourceRange.none 0))))

/--
info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (= i x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .exist "i" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 0) (.fvar Strata.SourceRange.none "x" (.some .int))))

/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= i x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none  .exist "i" (.some .int) (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))) (.bvar Strata.SourceRange.none 0))
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 0) (.fvar Strata.SourceRange.none "x" (.some .int))))


/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f i) x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .exist "i" (.some .int) (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))) (.bvar Strata.SourceRange.none 0))
   (.eq Strata.SourceRange.none (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))) (.bvar Strata.SourceRange.none 0)) (.fvar Strata.SourceRange.none "x" (.some .int))))

/-- info: "Cannot encode expression (f %0)" -/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .exist "i" (.some .int) (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.none)) (.bvar Strata.SourceRange.none 0))
   (.eq Strata.SourceRange.none (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))) (.bvar Strata.SourceRange.none 0)) (.fvar Strata.SourceRange.none "x" (.some .int))))

/--
info: "; f\n(declare-const f (arrow Int Int))\n; f\n(declare-fun f@1 (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f@1 i) x) :pattern (f))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .exist "i" (.some .int)
   (mkTriggerExpr [[.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))]])
   (.eq Strata.SourceRange.none (.app Strata.SourceRange.none (.fvar Strata.SourceRange.none "f" (.some (.arrow .int .int))) (.bvar Strata.SourceRange.none 0)) (.fvar Strata.SourceRange.none "x" (.some .int))))
   (ctx := SMT.Context.default)
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((m Int) (n Int)) (! (= (f n m) x) :pattern ((f n m)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant Strata.SourceRange.none .all "m" (.some .int) (.bvar Strata.SourceRange.none 0) (.quant Strata.SourceRange.none .all "n" (.some .int) (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar Strata.SourceRange.none 0)) (.bvar Strata.SourceRange.none 1))
   (.eq Strata.SourceRange.none (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar Strata.SourceRange.none 0)) (.bvar Strata.SourceRange.none 1)) (.fvar Strata.SourceRange.none "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] False [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
      }
   }})


/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((m Int) (n Int)) (= (f n m) x)))\n"
-/
#guard_msgs in -- No valid trigger
#eval toSMTTermString
(.quant Strata.SourceRange.none .all "m" (.some .int) (.bvar Strata.SourceRange.none 0) (.quant Strata.SourceRange.none .all "n" (.some .int) (.bvar Strata.SourceRange.none 0)
   (.eq Strata.SourceRange.none (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar Strata.SourceRange.none 0)) (.bvar Strata.SourceRange.none 1)) (.fvar Strata.SourceRange.none "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] False [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
      }
   }})

/-! ## Tests for Array Theory Support -/

section ArrayTheory

-- Test map select with Array theory enabled
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun t1 () Int i)\n(define-fun t2 () Int (select t0 t1))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.fvar Strata.SourceRange.none "m" (.some (mapTy .int .int))))
    (.fvar Strata.SourceRange.none "i" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test map update with Array theory enabled
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun t1 () Int i)\n; v\n(declare-const v Int)\n(define-fun t2 () Int v)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
    (.fvar Strata.SourceRange.none "m" (.some (mapTy .int .int))))
    (.fvar Strata.SourceRange.none "i" (.some .int)))
    (.fvar Strata.SourceRange.none "v" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test nested map operations with Array theory
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun t1 () Int i)\n; v\n(declare-const v Int)\n(define-fun t2 () Int v)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n; j\n(declare-const j Int)\n(define-fun t4 () Int j)\n(define-fun t5 () Int (select t3 t4))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
      (.fvar Strata.SourceRange.none "m" (.some (mapTy .int .int))))
      (.fvar Strata.SourceRange.none "i" (.some .int)))
      (.fvar Strata.SourceRange.none "v" (.some .int))))
    (.fvar Strata.SourceRange.none "j" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test empty string falls back to generated names
/-- info: "(define-fun t0 () Bool (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant Strata.SourceRange.none .all "" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.quant Strata.SourceRange.none .exist "" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 1) (.bvar Strata.SourceRange.none 0))))

-- Test name clash between two nested quantifiers with same name
-- Expected: Inner x should be disambiguated to x@1
/-- info: "(define-fun t0 () Bool (forall ((x Int)) (exists ((x@1 Int)) (= x x@1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant Strata.SourceRange.none .all "x" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.quant Strata.SourceRange.none .exist "x" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 1) (.bvar Strata.SourceRange.none 0))))

-- Test x, x, x@1 scenario: nested quantifiers both named "x", then bvar named "x@1"
-- Expected: outer x stays x, inner x becomes x@1, bvar "x@1" becomes x@2
/-- info: "(define-fun t0 () Bool (forall ((x Int) (x@1 Int) (x@2 Int)) (= x@2 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant Strata.SourceRange.none .all "x" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.quant Strata.SourceRange.none .all "x" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
    (.quant Strata.SourceRange.none .all "x@1" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
     (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 0) (.bvar Strata.SourceRange.none 2)))))


/-- info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((x@1 Int)) (= x@1 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant Strata.SourceRange.none .all "x" (.some .int) (LExpr.noTrigger Strata.SourceRange.none)
   (.eq Strata.SourceRange.none (.bvar Strata.SourceRange.none 0) (.fvar Strata.SourceRange.none "x" (.some .int))))

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
#eval! verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := false})

-- Test verification with Array theory
/--
info:
Obligation: UpdateAndRead_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval! verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := true})

end Strata
