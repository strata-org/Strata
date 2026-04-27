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

/--
info: "(define-fun $__t.0 () Bool (forall ((n Int)) (exists ((m Int)) (= n m))))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "n" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "m" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

/--
info: "; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (exists ((i Int)) (= i x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .exist "i" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (exists ((i Int)) (! (= i x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant ()  .exist "i" (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))


/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (exists ((i Int)) (! (= (f i) x) :pattern ((f i)))))\n"
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
info: "; f\n(declare-const f (arrow Int Int))\n; f\n(declare-fun f@1 (Int) Int)\n; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (exists ((i Int)) (! (= (f@1 i) x) :pattern (f))))\n"
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
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (forall ((m Int) (n Int)) (! (= (f n m) x) :pattern ((f n m)))))\n"
-/
#guard_msgs in
#eval toSMTTermString
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1))
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [] 0 false)
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.pushIfNew $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
      }
   }})


/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (forall ((m Int) (n Int)) (= (f n m) x)))\n"
-/
#guard_msgs in -- No valid trigger
#eval toSMTTermString
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.bvar () 0)
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := SMT.Context.mk #[] #[UF.mk "f" ((TermVar.mk "m" TermType.int) ::(TermVar.mk "n" TermType.int) :: []) TermType.int] #[] #[] [] #[] {} [] 0 false)
   (E := {Env.init with exprEnv := {
    Env.init.exprEnv with
      config := { Env.init.exprEnv.config with
        factory :=
          Env.init.exprEnv.config.factory.pushIfNew $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] []
      }
   }})

/-! ## Tests for Array Theory Support -/

section ArrayTheory

-- Test map select with Array theory enabled
/--
info: "; m\n(declare-const m (Array Int Int))\n(define-fun $__t.0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun $__t.1 () Int i)\n(define-fun $__t.2 () Int (select $__t.0 $__t.1))\n"
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
info: "; m\n(declare-const m (Array Int Int))\n(define-fun $__t.0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun $__t.1 () Int i)\n; v\n(declare-const v Int)\n(define-fun $__t.2 () Int v)\n(define-fun $__t.3 () (Array Int Int) (store $__t.0 $__t.1 $__t.2))\n"
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
info: "; m\n(declare-const m (Array Int Int))\n(define-fun $__t.0 () (Array Int Int) m)\n; i\n(declare-const i Int)\n(define-fun $__t.1 () Int i)\n; v\n(declare-const v Int)\n(define-fun $__t.2 () Int v)\n(define-fun $__t.3 () (Array Int Int) (store $__t.0 $__t.1 $__t.2))\n; j\n(declare-const j Int)\n(define-fun $__t.4 () Int j)\n(define-fun $__t.5 () Int (select $__t.3 $__t.4))\n"
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
info: "; m\n(declare-const m (Array Int Int))\n(define-fun $__t.0 () (Array Int Int) m)\n; getFirst\n(declare-fun getFirst ((Array Int Int)) Int)\n(define-fun $__t.1 () Int (getFirst $__t.0))\n"
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
          Core.Factory.pushIfNew $
          LFunc.mk (⟨"getFirst", ()⟩) [] false false
            [(⟨"m", ()⟩, mapTy .int .int)] .int .none #[] .none [] []
      }
   }})

-- Test that all bound variables get globally unique generated names
/-- info: "(define-fun $__t.0 () Bool (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test nested quantifiers with same user name get disambiguated human-readable names
/--
info: "(define-fun $__t.0 () Bool (forall ((x Int)) (exists ((x@1 Int)) (= x x@1))))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test triply nested quantifiers all get distinct disambiguated human-readable names
/--
info: "(define-fun $__t.0 () Bool (forall ((x Int) (x@1 Int) (x@2 Int)) (= x@2 x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
    (.quant () .all "x@1" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 0) (.bvar () 2)))))


/--
info: "; x\n(declare-const x Int)\n(define-fun $__t.0 () Bool (forall ((x@1 Int)) (= x@1 x)))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

-- Test that bound variable names are globally unique across multiple terms.
-- Two independent forall terms with empty names encoded via toSMTTerms should get distinct $__bv names.
#guard
  match toSMTTerms Env.init [
    -- Term 1: ∀ x:Int. x = x
    (.quant () .all "" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 0) (.bvar () 0))),
    -- Term 2: ∀ y:Bool. y
    (.quant () .all "" (.some .bool) (LExpr.noTrigger ())
     (.bvar () 0))
  ] SMT.Context.default with
  | .ok ([t1, t2], _) =>
    match Strata.SMTDDM.termToString t1, Strata.SMTDDM.termToString t2 with
    | .ok s1, .ok s2 =>
      s1 == "(forall (($__bv0 Int)) true)" &&
      s2 == "(forall (($__bv1 Bool)) $__bv1)"
    | _, _ => false
  | _ => false

-- Test string literal containing double quotes is properly escaped for SMT-LIB 2.7
-- In SMT-LIB 2.7, double quotes inside strings are escaped by doubling: "a""b" represents a"b
/--
info: "; x\n(declare-const x String)\n(define-fun $__t.0 () String x)\n(define-fun $__t.1 () Bool (= $__t.0 \"{\"\"key\"\":\"\"val\"\"}\"))\n"
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
info: "; x\n(declare-const x Real)\n(define-fun $__t.0 () Real x)\n; y\n(declare-const y Real)\n(define-fun $__t.1 () Real y)\n(define-fun $__t.2 () Real (|/| $__t.0 $__t.1))\n"
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

/-! ## Test that built-in types do not produce declare-sort -/

-- Callers of addType (i.e. LMonoTy.toSMTType) should not call addType for
-- built-in Core types (int, bool, etc.). Array should also not produce a
-- declare-sort because it is a built-in SMT-LIB sort.
/-- info: (#[{ name := "Foo", arity := 2 }], true) -/
#guard_msgs in
#eval do
  let ctx := SMT.Context.default
  -- toSMTType for a user-defined type "Foo" should register the sort
  let (.ok (_, ctx)) := LMonoTy.toSMTType Env.init (.tcons "Foo" [.tcons "int" [], .tcons "bool" []]) ctx
    | unreachable!
  -- Map with useArrayTheory converts to Array; should NOT register a sort
  let (.ok (_, ctx)) := LMonoTy.toSMTType Env.init (.tcons "Map" [.tcons "int" [], .tcons "int" []]) ctx (useArrayTheory := true)
    | unreachable!
  return (ctx.sorts, ctx.sorts.all (fun s => s.name ∉ ["int", "bool", "Array"]))

/-! ## Test that get-value ids exclude non-nullary UFs -/

-- encodeCore should only include nullary UFs (constants) in the ids passed to
-- get-value. Non-nullary UFs like `f(x : Int) : Int` cannot be queried via
-- get-value in some SMT solvers.
/-- info: (["c"], true) -/
#guard_msgs in
#eval show IO _ from do
  -- Non-nullary UF: f(x : Int) : Int — should be excluded from ids
  let uf_f := UF.mk "f" [TermVar.mk "x" TermType.int] TermType.int
  -- Nullary UF: c : Int — should be included in ids
  let uf_c := UF.mk "c" [] TermType.int
  let ctx : SMT.Context := { SMT.Context.default with ufs := #[uf_f, uf_c] }
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression := #[]
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let ((ids, _estate), _) ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "test"))
  -- ids should contain "c" but not "f"
  let hasF := ids.any (· == "f")
  return (ids, !hasF)

/-! ## Test that final-message falls back to label when metadata has no message -/

/--
info: (set-logic ALL)
; Validity
(assert false)
(check-sat)
(set-info :final-message "assert_bounds_check")
-/
#guard_msgs in
#eval show IO _ from do
  let ctx : SMT.Context := SMT.Context.default
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression := #[]
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let _ ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "assert_bounds_check"))
  let contents ← b.get
  let smt :=
    if h : contents.data.IsValidUTF8
    then String.fromUTF8 contents.data h
    else ""
  IO.print smt

/-! ## Test that final-message uses propertySummary when present -/

/--
info: (set-logic ALL)
; Validity
(assert false)
(check-sat)
(set-info :final-message "Division by zero is impossible")
-/
#guard_msgs in
#eval show IO _ from do
  let ctx : SMT.Context := SMT.Context.default
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression :=
    Imperative.MetaData.empty.withPropertySummary "Division by zero is impossible"
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let _ ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "assert_bounds_check"))
  let contents ← b.get
  let smt :=
    if h : contents.data.IsValidUTF8
    then String.fromUTF8 contents.data h
    else ""
  IO.print smt

end Core

/-! ## End-to-End Test with Complete Program -/

namespace Strata

-- Simple program that uses maps
def simpleMapProgram :=
#strata
program Core;

procedure UpdateAndRead(inout m : Map int int, k : int, v : int, out result : int)
spec {
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
Obligation: UpdateAndRead_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval! verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := false})

-- Test verification with Array theory
/--
info:
Obligation: UpdateAndRead_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval! verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := true})

-- Test that string literals with embedded double quotes are correctly encoded for SMT
def quotedStringProgram :=
#strata
program Core;

procedure Test(x: string)
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
