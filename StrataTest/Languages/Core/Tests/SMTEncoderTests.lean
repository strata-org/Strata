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
  (.quant () .all "n" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "m" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

/--
info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (= i x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist "i" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= i x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant ()  .exist "i" (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))


/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f i) x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist "i" (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/-- info: "Cannot encode expression f(bvar!0)\n-- Errors: Unsupported construct in lexprToExpr: bvar index out of bounds: 0\nContext: Global scope:\n  freeVars: [f]" -/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist "i" (.some .int) (.app () (.fvar () "f" (.none)) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-const f (arrow Int Int))\n; f\n(declare-fun f@1 (Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (exists ((i Int)) (! (= (f@1 i) x) :pattern (f))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist "i" (.some .int)
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
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((m Int) (n Int)) (! (= (f n m) x) :pattern ((f n m)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1))
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
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
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.bvar () 0)
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
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
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun t1 () Int i)\n; v\n(declare-const v Int)\n(define-fun t2 () Int v)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n"
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
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun t1 () Int i)\n; v\n(declare-const v Int)\n(define-fun t2 () Int v)\n(define-fun t3 () (Array Int Int) (store t0 t1 t2))\n; j\n(declare-const j Int)\n(define-fun t4 () Int j)\n(define-fun t5 () Int (select t3 t4))\n"
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

-- Test that UF input types use Array when useArrayTheory=true (regression for Map/Array mismatch)
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun t0 () (Array Int Int) m)\n; getFirst\n(declare-fun getFirst ((Array Int Int)) Int)\n(define-fun t1 () Int (getFirst t0))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app () (.op () (⟨"getFirst", ()⟩) (.some (.arrow (mapTy .int .int) .int)))
           (.fvar () (⟨"m", ()⟩) (.some (mapTy .int .int))))
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
  (.quant () .all "" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test name clash between two nested quantifiers with same name
-- Expected: Inner x should be disambiguated to x@1
/-- info: "(define-fun t0 () Bool (forall ((x Int)) (exists ((x@1 Int)) (= x x@1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test x, x, x@1 scenario: nested quantifiers both named "x", then bvar named "x@1"
-- Expected: outer x stays x, inner x becomes x@1, bvar "x@1" becomes x@2
/-- info: "(define-fun t0 () Bool (forall ((x Int) (x@1 Int) (x@2 Int)) (= x@2 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
    (.quant () .all "x@1" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 0) (.bvar () 2)))))


/-- info: "; x\n(declare-const x Int)\n(define-fun t0 () Bool (forall ((x@1 Int)) (= x@1 x)))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

-- Test string literal containing double quotes is properly escaped for SMT-LIB 2.7
-- In SMT-LIB 2.7, double quotes inside strings are escaped by doubling: "a""b" represents a"b
/--
info: "; x\n(declare-const x String)\n(define-fun t0 () String x)\n(define-fun t1 () Bool (= t0 \"{\"\"key\"\":\"\"val\"\"}\"))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.eq () (.fvar () "x" (.some .string)) (.strConst () "{\"key\":\"val\"}"))

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
