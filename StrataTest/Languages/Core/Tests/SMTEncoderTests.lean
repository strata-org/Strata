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

private abbrev sr := Strata.SourceRange.none

/-- info: "(define-fun t0 () Bool (forall ((n Int)) (exists ((m Int)) (= n m))))\n" -/
#guard_msgs in
#eval toSMTTermString
(.quant sr .all "n" (.some .int) (LExpr.noTrigger sr)
   (.quant sr .exist "m" (.some .int) (LExpr.noTrigger sr)
   (.eq sr (.bvar sr 1) (.bvar sr 0))))

/--
info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (= i x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant sr .exist "i" (.some .int) (LExpr.noTrigger sr)
   (.eq sr (.bvar sr 0) (.fvar sr "x" (.some .int))))

/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= i x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant sr  .exist "i" (.some .int) (.app sr (.fvar sr "f" (.some (.arrow .int .int))) (.bvar sr 0))
   (.eq sr (.bvar sr 0) (.fvar sr "x" (.some .int))))


/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f i) x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant sr .exist "i" (.some .int) (.app sr (.fvar sr "f" (.some (.arrow .int .int))) (.bvar sr 0))
   (.eq sr (.app sr (.fvar sr "f" (.some (.arrow .int .int))) (.bvar sr 0)) (.fvar sr "x" (.some .int))))

/-- info: "Cannot encode expression (f %0)" -/
#guard_msgs in
#eval toSMTTermString
(.quant sr .exist "i" (.some .int) (.app sr (.fvar sr "f" (.none)) (.bvar sr 0))
   (.eq sr (.app sr (.fvar sr "f" (.some (.arrow .int .int))) (.bvar sr 0)) (.fvar sr "x" (.some .int))))

/--
info: "; f\n(declare-const f (arrow Int Int))\n; f\n(declare-fun f@1 (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f@1 i) x) :pattern (f))))\n"
-/
#guard_msgs in
#eval toSMTTermString
(.quant sr .exist "i" (.some .int)
   (mkTriggerExpr [[.fvar sr "f" (.some (.arrow .int .int))]])
   (.eq sr (.app sr (.fvar sr "f" (.some (.arrow .int .int))) (.bvar sr 0)) (.fvar sr "x" (.some .int))))
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
(.quant sr .all "m" (.some .int) (.bvar sr 0) (.quant sr .all "n" (.some .int) (.app sr (.app sr (.op sr "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar sr 0)) (.bvar sr 1))
   (.eq sr (.app sr (.app sr (.op sr "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar sr 0)) (.bvar sr 1)) (.fvar sr "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
      }
   }})


/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((m Int) (n Int)) (= (f n m) x)))\n"
-/
#guard_msgs in -- No valid trigger
#eval toSMTTermString
(.quant sr .all "m" (.some .int) (.bvar sr 0) (.quant sr .all "n" (.some .int) (.bvar sr 0)
   (.eq sr (.app sr (.app sr (.op sr "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar sr 0)) (.bvar sr 1)) (.fvar sr "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [])
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.push $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
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
  (.app sr (.app sr (.op sr "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.fvar sr "m" (.some (mapTy .int .int))))
    (.fvar sr "i" (.some .int)))
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
  (.app sr (.app sr (.app sr (.op sr "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
    (.fvar sr "m" (.some (mapTy .int .int))))
    (.fvar sr "i" (.some .int)))
    (.fvar sr "v" (.some .int)))
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
  (.app sr (.app sr (.op sr "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.app sr (.app sr (.app sr (.op sr "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
      (.fvar sr "m" (.some (mapTy .int .int))))
      (.fvar sr "i" (.some .int)))
      (.fvar sr "v" (.some .int))))
    (.fvar sr "j" (.some .int)))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory := Core.Factory
      }
   }})

-- Test that UF input types use Array when useArrayTheory=true (regression for Map/Array mismatch)
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; getFirst\n(declare-fun getFirst ((Array Int Int)) Int)\n(define-fun t1 () Int (getFirst t0))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app sr (.op sr (⟨"getFirst", ()⟩) (.some (.arrow (mapTy .int .int) .int)))
           (.fvar sr (⟨"m", ()⟩) (.some (mapTy .int .int))))
  (useArrayTheory := true)
  (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Core.Factory.push $
          LFunc.mk (⟨"getFirst", ()⟩) [] false false
            [(⟨"m", ()⟩, mapTy .int .int)] .int .none #[] .none [] []
      }
   }})

-- Test empty string falls back to generated names
/-- info: "(define-fun t0 () Bool (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant sr .all "" (.some .int) (LExpr.noTrigger sr)
   (.quant sr .exist "" (.some .int) (LExpr.noTrigger sr)
   (.eq sr (.bvar sr 1) (.bvar sr 0))))

-- Test name clash between two nested quantifiers with same name
-- Expected: Inner x should be disambiguated to x@1
/-- info: "(define-fun t0 () Bool (forall ((x Int)) (exists ((x@1 Int)) (= x x@1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant sr .all "x" (.some .int) (LExpr.noTrigger sr)
   (.quant sr .exist "x" (.some .int) (LExpr.noTrigger sr)
   (.eq sr (.bvar sr 1) (.bvar sr 0))))

-- Test x, x, x@1 scenario: nested quantifiers both named "x", then bvar named "x@1"
-- Expected: outer x stays x, inner x becomes x@1, bvar "x@1" becomes x@2
/-- info: "(define-fun t0 () Bool (forall ((x Int) (x@1 Int) (x@2 Int)) (= x@2 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant sr .all "x" (.some .int) (LExpr.noTrigger sr)
   (.quant sr .all "x" (.some .int) (LExpr.noTrigger sr)
    (.quant sr .all "x@1" (.some .int) (LExpr.noTrigger sr)
     (.eq sr (.bvar sr 0) (.bvar sr 2)))))


/-- info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((x@1 Int)) (= x@1 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant sr .all "x" (.some .int) (LExpr.noTrigger sr)
   (.eq sr (.bvar sr 0) (.fvar sr "x" (.some .int))))

-- Test string literal containing double quotes is properly escaped for SMT-LIB 2.7
-- In SMT-LIB 2.7, double quotes inside strings are escaped by doubling: "a""b" represents a"b
/--
info: "; x\n(declare-const x String)\n(define-fun t0 () String x)\n(define-fun t1 () Bool (= t0 \"{\"\"key\"\":\"\"val\"\"}\"))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.eq sr (.fvar sr "x" (.some .string)) (.strConst sr "{\"key\":\"val\"}"))

-- Test that negative integer constants are lowered to (- N) form
/-- info: Except.ok "(- 1)" -/
#guard_msgs in
#eval Strata.SMTDDM.termToString (.prim (.int (-1)))

-- Test that Real.Div encodes to `/` (real division) not `div` (integer division).
/--
info: "; x\n(declare-const x Real)\n(define-fun t0 () Real x)\n; y\n(declare-const y Real)\n(define-fun t1 () Real y)\n(define-fun t2 () Real (|/| t0 t1))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app ()
    (.app ()
      (.op () "Real.Div" (.some (.arrow .real (.arrow .real .real))))
      (.fvar () "x" (.some .real)))
    (.fvar () "y" (.some .real)))
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

-- Test that string literals with embedded double quotes are correctly encoded for SMT
def quotedStringProgram :=
#strata
program Core;

var x: string;

procedure Test() returns ()
spec { ensures true; }
{
  assume x == "{\"key\":\"val\"}";
  assert x == "{\"key\":\"val\"}";
};
#end

/--
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval! verify quotedStringProgram (options := Core.VerifyOptions.quiet)

end Strata
