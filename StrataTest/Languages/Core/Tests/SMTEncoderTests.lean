/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.SMTEncoder
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.Transform.BetaReduce
import Strata.Languages.Core.ObligationExtraction

meta section

/-! ## Tests for SMTEncoder -/

namespace Core
open Lambda
open Strata.SMT

/--
info: "(assert (forall ((n Int)) (exists ((m Int)) (= n m))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "n" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "m" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

/--
info: "; x\n(declare-const x Int)\n(assert (exists ((i Int)) (= i x)))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant () .exist "i" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(assert (exists ((i Int)) (! (= i x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant ()  .exist "i" (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))


/--
info: "; f\n(declare-fun f (Int) Int)\n; x\n(declare-const x Int)\n(assert (exists ((i Int)) (! (= (f i) x) :pattern ((f i)))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant () .exist "i" (.some .int) (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/-- info: "Cannot encode .app expression f(bvar!0)\n-- Errors: Unsupported construct in lexprToExpr: bvar index out of bounds: 0\nContext: Global scope:\n  freeVars: [f]" -/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant () .exist "i" (.some .int) (.app () (.fvar () "f" (.none)) (.bvar () 0))
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))

/--
info: "; f\n(declare-const f (arrow Int Int))\n; f\n(declare-fun f@1 (Int) Int)\n; x\n(declare-const x Int)\n(assert (exists ((i Int)) (! (= (f@1 i) x) :pattern (f))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant () .exist "i" (.some .int)
   (mkTriggerExpr [[.fvar () "f" (.some (.arrow .int .int))]])
   (.eq () (.app () (.fvar () "f" (.some (.arrow .int .int))) (.bvar () 0)) (.fvar () "x" (.some .int))))
   (ctx := SMT.Context.default)
   (factory := Core.Factory)

/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(assert (forall ((m Int) (n Int)) (! (= (f n m) x) :pattern ((f n m)))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1))
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := { ufs := .ofArray #[UF.mk "f" (TermType.int :: TermType.int :: []) TermType.int] })
   (factory := Core.Factory.pushIfNew $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] [])


/--
info: "; f\n(declare-fun f (Int Int) Int)\n; x\n(declare-const x Int)\n(assert (forall ((m Int) (n Int)) (= (f n m) x)))\n"
-/
#guard_msgs in -- No valid trigger
#eval toSMTCommandsWithAssert
   (.quant () .all "m" (.some .int) (.bvar () 0) (.quant () .all "n" (.some .int) (.bvar () 0)
   (.eq () (.app () (.app () (.op () "f" (.some (.arrow .int (.arrow .int .int)))) (.bvar () 0)) (.bvar () 1)) (.fvar () "x" (.some .int)))))
   (ctx := { ufs := .ofArray #[UF.mk "f" (TermType.int :: TermType.int :: []) TermType.int] })
   (factory := Core.Factory.pushIfNew $
          LFunc.mk "f" [] false false [("m", LMonoTy.int), ("n", LMonoTy.int)] LMonoTy.int .none #[] .none [] [])

/-! ## Tests for Array Theory Support -/

section ArrayTheory

-- Test map select with Array theory enabled
/--
info: "; m\n(declare-const m (Array Int Int))\n; i\n(declare-const i Int)\n(assert (select m i))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.app () (.op () "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.fvar () "m" (.some (mapTy .int .int))))
    (.fvar () "i" (.some .int)))
  (ctx := { SMT.Context.default with useArrayTheory := true })
  (factory := Core.Factory)

-- Test map update with Array theory enabled
/--
info: "; m\n(declare-const m (Array Int Int))\n; i\n(declare-const i Int)\n; v\n(declare-const v Int)\n(assert (store m i v))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.app () (.app () (.op () "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
    (.fvar () "m" (.some (mapTy .int .int))))
    (.fvar () "i" (.some .int)))
    (.fvar () "v" (.some .int)))
  (ctx := { SMT.Context.default with useArrayTheory := true })
  (factory := Core.Factory)

-- Test nested map operations with Array theory
/--
info: "; m\n(declare-const m (Array Int Int))\n; i\n(declare-const i Int)\n; v\n(declare-const v Int)\n; j\n(declare-const j Int)\n(assert (select (store m i v) j))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.app () (.op () "select" (.some (.arrow (mapTy .int .int) (.arrow .int .int))))
    (.app () (.app () (.app () (.op () "update" (.some (.arrow (mapTy .int .int) (.arrow .int (.arrow .int (mapTy .int .int))))))
      (.fvar () "m" (.some (mapTy .int .int))))
      (.fvar () "i" (.some .int)))
      (.fvar () "v" (.some .int))))
    (.fvar () "j" (.some .int)))
  (ctx := { SMT.Context.default with useArrayTheory := true })
  (factory := Core.Factory)

-- Test that UF input types use Array when useArrayTheory=true (regression for Map/Array mismatch)
/--
info: "; m\n(declare-const m (Array Int Int))\n; getFirst\n(declare-fun getFirst ((Array Int Int)) Int)\n(assert (getFirst m))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.op () (⟨"getFirst", ()⟩) (.some (.arrow (mapTy .int .int) .int)))
           (.fvar () (⟨"m", ()⟩) (.some (mapTy .int .int))))
  (ctx := { SMT.Context.default with useArrayTheory := true })
  (factory := Core.Factory.pushIfNew $
          LFunc.mk (⟨"getFirst", ()⟩) [] false false
            [(⟨"m", ()⟩, mapTy .int .int)] .int .none #[] .none [] [])

-- Nested empty-named binders get distinct generated names by de Bruijn depth: outer at depth 0
-- (`$__bv0`), inner at depth 1 (`$__bv1`).
/-- info: "(assert (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test nested quantifiers with same user name get disambiguated human-readable names
/--
info: "(assert (forall ((x Int)) (exists ((x@1 Int)) (= x x@1))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .exist "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 1) (.bvar () 0))))

-- Test triply nested quantifiers all get distinct disambiguated human-readable names
/--
info: "(assert (forall ((x Int) (x@1 Int) (x@2 Int)) (= x@2 x)))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
    (.quant () .all "x@1" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 0) (.bvar () 2)))))

-- Test mixed named/unnamed nesting: de Bruijn depth (`bvs.length`) counts user-named binders too, so
-- the inner unnamed binder gets `$__bv2` (its stack depth), not `$__bv1`. (The two adjacent `forall`s
-- coalesce into one binder group; the inner `exists` stays separate but still sees depth 2.)
/--
info: "(assert (forall (($__bv0 Int) (x Int)) (exists (($__bv2 Int)) (= $__bv0 $__bv2))))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "" (.some .int) (LExpr.noTrigger ())
   (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
    (.quant () .exist "" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 2) (.bvar () 0)))))


/--
info: "; x\n(declare-const x Int)\n(assert (forall ((x@1 Int)) (= x@1 x)))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.quant () .all "x" (.some .int) (LExpr.noTrigger ())
   (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))

-- Empty-named quantifier binders are named by de Bruijn depth (`$__bv{depth}`). Each term encoded
-- via toSMTTerms starts from an empty binder stack, so two independent top-level foralls each get
-- depth 0 → both `$__bv0`. This is sound because the two binders are never simultaneously in scope
-- (distinct depths only arise for nested binders within one term).
#guard
  match toSMTTerms Lambda.Factory.default [
    -- Term 1: ∀ x:Int. x = x
    (.quant () .all "" (.some .int) (LExpr.noTrigger ())
     (.eq () (.bvar () 0) (.bvar () 0))),
    -- Term 2: ∀ y:Bool. y
    (.quant () .all "" (.some .bool) (LExpr.noTrigger ())
     (.bvar () 0))
  ] SMT.Context.default {} with
  | .ok ([t1, t2], _, _) =>
    match Strata.SMTDDM.termToString t1, Strata.SMTDDM.termToString t2 with
    | .ok s1, .ok s2 =>
      s1 == "(forall (($__bv0 Int)) true)" &&
      s2 == "(forall (($__bv0 Bool)) $__bv0)"
    | _, _ => false
  | _ => false

-- Test string literal containing double quotes is properly escaped for SMT-LIB 2.7
-- In SMT-LIB 2.7, double quotes inside strings are escaped by doubling: "a""b" represents a"b
/--
info: "; x\n(declare-const x String)\n(assert (= x \"{\"\"key\"\":\"\"val\"\"}\"))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.eq () (.fvar () "x" (.some .string)) (.strConst () "{\"key\":\"val\"}"))

-- Test that negative integer constants are lowered to (- N) form
/-- info: Except.ok "(- 1)" -/
#guard_msgs in
#eval Strata.SMTDDM.termToString (.prim (.int (-1)))

-- Test that Real.Div encodes to `/` (real division) not `div` (integer division).
/--
info: "; x\n(declare-const x Real)\n; y\n(declare-const y Real)\n(assert (|/| x y))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app ()
    (.app ()
      (.op () "Real.Div" (.some (.arrow .real (.arrow .real .real))))
      (.fvar () "x" (.some .real)))
    (.fvar () "y" (.some .real)))
  (factory := Core.Factory)

-- A `realConst` whose value has no terminating decimal expansion (e.g. `1/3`,
-- the value of the surface literal `frac{1, 3}`) cannot be emitted as a single
-- SMT-LIB decimal literal, so it is encoded as the exact real division
-- `(/ num den)` rather than erroring.
/-- info: "(assert (|/| 1.0 3.0))\n" -/
#guard_msgs in
#eval toSMTCommandsWithAssert (.realConst () (1 / 3 : Rat))

-- The sign of a negative non-terminating value (e.g. `-2/3`, the value of
-- `-frac{2, 3}`) rides on the numerator, which the serializer wraps in unary
-- minus; the denominator stays positive.
/-- info: "(assert (|/| (- 2.0) 3.0))\n" -/
#guard_msgs in
#eval toSMTCommandsWithAssert (.realConst () (-2 / 3 : Rat))

-- Conversely, a *terminating* value (e.g. `1/4`) keeps routing through the
-- `Decimal.fromRat = some` branch and emits a single SMT-LIB decimal literal,
-- not the `(/ num den)` division. Pins the branch boundary so a change to
-- `fromRat`'s terminating-detection fails here instead of silently reshaping
-- emitted SMT.
/-- info: "(assert 0.25)\n" -/
#guard_msgs in
#eval toSMTCommandsWithAssert (.realConst () (1 / 4 : Rat))

end ArrayTheory

/-! ## `smtTermToLExpr`: unary `-` decodes by operand type

The model parser represents a unary `-` in a counterexample as a UF
application whose return type is an untyped placeholder, so `smtTermToLExpr`
decides `int.neg` vs `real.neg` from the operand, which is expected to be a
numeric constant: a real constant ⇒ `real.neg`, otherwise `int.neg`. -/

/-- Build the untyped `(- arg)` UF application that a parsed model yields for
    unary minus. -/
private def negUF (arg : Strata.SMT.Term) : Strata.SMT.Term :=
  .app (.core (.uf { id := "-", args := [], out := .constr "_placeholder" [] }))
    [arg] (.constr "_placeholder" [])

-- Integer constant operand ⇒ `Int.Neg`.
#guard smtTermToLExpr (negUF (.prim (.int 1)))
  == .app () (.op () "Int.Neg" none) (.intConst () 1)

-- Real constant operand ⇒ `Real.Neg` (the untyped placeholder return type is ignored).
#guard smtTermToLExpr (negUF (.prim (.real (StrataDDM.Decimal.mk 628 (-2)))))
  == .app () (.op () "Real.Neg" none) (.realConst () (StrataDDM.Decimal.mk 628 (-2)).toRat)

-- A non-constant operand (here a variable) is not a real literal ⇒ defaults to `Int.Neg`.
#guard smtTermToLExpr (negUF (.var { id := "x", ty := .constr "_placeholder" [] }))
  == .app () (.op () "Int.Neg" none) (.fvar () "x" none)

/-- Build a binary `(- a b)` UF application (two operands). -/
private def binMinusUF (a b : Strata.SMT.Term) : Strata.SMT.Term :=
  .app (.core (.uf { id := "-", args := [], out := .constr "_placeholder" [] }))
    [a, b] (.constr "_placeholder" [])

-- Binary `-` (two args) is NOT rewritten to Int.Neg; it falls through to a plain UF.
#guard smtTermToLExpr (binMinusUF (.prim (.int 3)) (.prim (.int 1)))
  == .app () (.app () (.fvar () "-" none) (.intConst () 3)) (.intConst () 1)

-- Nested negation `-(-(1))` decodes recursively to `int.neg(int.neg(1))`.
#guard smtTermToLExpr (negUF (negUF (.prim (.int 1))))
  == .app () (.op () "Int.Neg" none)
       (.app () (.op () "Int.Neg" none) (.intConst () 1))

-- Nested real negation: `smtTermIsReal` inspects only the immediate operand, so
-- the outer `-` sees an `.app` (not a real literal) and defaults to `Int.Neg`,
-- while the inner `-` over the real literal is `Real.Neg`.
#guard smtTermToLExpr (negUF (negUF (.prim (.real (StrataDDM.Decimal.mk 100 0)))))
  == .app () (.op () "Int.Neg" none)
       (.app () (.op () "Real.Neg" none) (.realConst () (StrataDDM.Decimal.mk 100 0).toRat))

/-! ## Test that built-in types do not produce declare-sort -/

-- Callers of addType (i.e. LMonoTy.toSMTType) should not call addType for
-- built-in Core types (int, bool, etc.). Array should also not produce a
-- declare-sort because it is a built-in SMT-LIB sort.
/-- info: (#[{ name := "Foo", arity := 2 }], true) -/
#guard_msgs in
#eval do
  let ctx := SMT.Context.default
  -- toSMTType for a user-defined type "Foo" should register the sort
  let (.ok (_, ctx)) := LMonoTy.toSMTType (.tcons "Foo" [.tcons "int" [], .tcons "bool" []]) ctx
    | unreachable!
  -- Map with useArrayTheory converts to Array; should NOT register a sort
  let ctx := { ctx with useArrayTheory := true }
  let (.ok (_, ctx)) := LMonoTy.toSMTType (.tcons "Map" [.tcons "int" [], .tcons "int" []]) ctx
    | unreachable!
  return (ctx.sorts.toArray, ctx.sorts.toArray.all (fun s => s.name ∉ ["int", "bool", "Array"]))

/-! ## Test that get-value ids exclude non-nullary UFs -/

-- encodeCore should only include nullary UFs (constants) in the ids passed to
-- get-value. Non-nullary UFs like `f(x : Int) : Int` cannot be queried via
-- get-value in some SMT solvers.
/-- info: (["c"], true) -/
#guard_msgs in
#eval show IO _ from do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet) (profilePipeline := false)
  -- Non-nullary UF: f(x : Int) : Int — should be excluded from ids
  let uf_f := UF.mk "f" [TermType.int] TermType.int
  -- Nullary UF: c : Int — should be included in ids
  let uf_c := UF.mk "c" [] TermType.int
  let ctx : SMT.Context := { SMT.Context.default with ufs := .ofArray #[uf_f, uf_c] }
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression := #[]
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let ((ids, _estate), _) ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "test")
        (pctx := pctx))
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
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet) (profilePipeline := false)
  let ctx : SMT.Context := SMT.Context.default
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression := #[]
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let _ ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "assert_bounds_check")
        (pctx := pctx))
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
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet) (profilePipeline := false)
  let ctx : SMT.Context := SMT.Context.default
  let obligationTerm := Term.prim (.bool true)
  let md : Imperative.MetaData Core.Expression :=
    Imperative.MetaData.empty.withPropertySummary "Division by zero is impossible"
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let _ ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := false) (validityCheck := true) (label := "assert_bounds_check")
        (pctx := pctx))
  let contents ← b.get
  let smt :=
    if h : contents.data.IsValidUTF8
    then String.fromUTF8 contents.data h
    else ""
  IO.print smt

/-! ## Regression: `:final-message` / `:sat-message` / `:unsat-message`
    must escape embedded double quotes by doubling them (`""`) per
    SMT-LIB 2.6+, not with C-style `\"` escaping.

    Before the fix, a property summary containing `"` would render as
    `(set-info :final-message "... \"FOO\" ...")` which SMT-LIB parsers
    reject: the backslash is a literal character in string contexts, and
    the following `"` closes the string, leaving `FOO\"...` outside as
    unexpected tokens. See
    https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf
    §3.1.2. -/

/-- Run `encodeCore` on a trivial `true` obligation with the given metadata
    and check flags, and return the resulting SMT-LIB text. -/
private def captureEncodeCore (md : Imperative.MetaData Core.Expression)
    (satCheck validityCheck : Bool) (label : String := "test") : IO String := do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet) (profilePipeline := false)
  let ctx : SMT.Context := SMT.Context.default
  let obligationTerm := Term.prim (.bool true)
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Strata.SMT.Solver.bufferWriter b
  let _ ←
    Strata.SMT.SolverM.run solver
      (Strata.SMT.Encoder.encodeCore ctx (pure ()) [] obligationTerm md
        (satisfiabilityCheck := satCheck) (validityCheck := validityCheck) (label := label)
        (pctx := pctx))
  let contents ← b.get
  return if h : contents.data.IsValidUTF8
         then String.fromUTF8 contents.data h
         else ""

/-- Metadata carrying only a property summary (no file range). -/
private def summaryMd (summary : String) : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.empty.withPropertySummary summary

/-- Metadata carrying only a file range (no property summary); used to
    exercise `addLocationInfo`. -/
private def fileRangeMd (file : String) : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofProvenance (Strata.Provenance.ofSourceRange (.file file) StrataDDM.SourceRange.none)

/-! Embedded double quotes in the property summary must be doubled (`""`). -/
/--
info: (set-logic ALL)
; Validity
(assert false)
(check-sat)
(set-info :final-message "Expected len(kwargs[""JobName""]) >= 1, got stringLen(kwargs[JobName])")
-/
#guard_msgs in
#eval show IO _ from do
  let smt ← captureEncodeCore
    (summaryMd "Expected len(kwargs[\"JobName\"]) >= 1, got stringLen(kwargs[JobName])")
    false true
  IO.print smt

/-! A backslash in the property summary is a *literal* character in SMT-LIB
    2.6+ strings (no special meaning), so no escape is needed. -/
/--
info: (set-info :final-message "path/with\backslash")
-/
#guard_msgs in
#eval show IO _ from do
  let smt ← captureEncodeCore (summaryMd "path/with\\backslash") false true
  for line in smt.splitOn "\n" do
    if line.startsWith "(set-info :final-message" then
      IO.println line

/-! In full-check mode (both satisfiability and validity), `addLocationInfo`
    emits `:sat-message` and `:unsat-message`. These values must not carry
    pre-wrapping literal quote characters — before the fix, the
    `bothChecks` branch passed `"\"Property can be satisfied\""` which, once
    `setInfoString` re-quoted it, rendered as `"""Property..."""` (a
    well-formed SMT-LIB string whose content has literal leading and
    trailing `"`). -/
/--
info: (set-info :sat-message "Property can be satisfied")
(set-info :unsat-message "Property is always true")
-/
#guard_msgs in
#eval show IO _ from do
  let smt ← captureEncodeCore (fileRangeMd "test.st") true true
  for line in smt.splitOn "\n" do
    if line.startsWith "(set-info :sat-message"
        ∨ line.startsWith "(set-info :unsat-message" then
      IO.println line

/-! ## SMT encoding of str.prefixof / str.suffixof -/

/--
info: "; s1\n(declare-const s1 String)\n; s2\n(declare-const s2 String)\n(assert (str.prefixof s1 s2))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.app () strPrefixOfOp (.fvar () "s1" (.some .string)))
    (.fvar () "s2" (.some .string)))

/--
info: "; s1\n(declare-const s1 String)\n; s2\n(declare-const s2 String)\n(assert (str.suffixof s1 s2))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app () (.app () strSuffixOfOp (.fvar () "s1" (.some .string)))
    (.fvar () "s2" (.some .string)))

/-! ## Obligation encoding preserves the input datatype factory

`SMT.Context.datatypes` is seeded by the caller from the env's datatype
TypeFactory and is never modified during encoding (encoding a datatype marks it
`seen` and registers its function maps, but never extends `datatypes`). These
checks pin that invariant: the output context's datatype factory equals the
datatype factory the caller seeded it with. -/

private def intListDatatypeRT : Lambda.LDatatype Unit :=
  { name := "IntList", typeArgs := [],
    constrs := [
      { name := "Nil", args := [], testerName := "isNil" },
      { name := "Cons", args := [("hd", .int), ("tl", .tcons "IntList" [])],
        testerName := "isCons" }
    ], constrs_ne := rfl }

/-- A minimal assertion obligation for `obligation`. -/
private def assertOb (obligation : LExpr CoreLParams.mono) :
    Imperative.ProofObligation Expression :=
  { label := "test", property := .assert, assumptions := [],
    obligation := obligation, metadata := {} }

/-- Build an env from the given datatype blocks, encode `ob` with its
    `datatypes` seeded from the env's datatypes, and return whether the output
    context's datatype factory still equals that input datatype factory. -/
private def typeFactoryPreserved (blocks : List (List (Lambda.LDatatype Unit)))
    (ob : Imperative.ProofObligation Expression) : Except Std.Format Bool := do
  let env ← (Env.init.addDatatypes blocks).mapError (f!"{·}")
  let ctx := { SMT.Context.default with datatypes := .ofFactory env.datatypes }
  let encState : SMTEncodeState := .init { ctx := ctx }
  let (res, _) ← encodeObligationToSMT env.factory encState ob
  let ctx' := res.ctx
  .ok (ctx'.datatypes.factory == env.datatypes)

-- Obligation referencing the `IntList` datatype (via its `Nil` constructor).
/-- info: ok: true -/
#guard_msgs in
#eval show Except Std.Format Bool from
  let nil : LExpr CoreLParams.mono := .op () ⟨"Nil", ()⟩ (.some (.tcons "IntList" []))
  typeFactoryPreserved [[intListDatatypeRT]] (assertOb (.eq () nil nil))

-- Obligation that does not reference the datatype at all: unused datatypes are
-- still retained in `typeFactory`.
/-- info: ok: true -/
#guard_msgs in
#eval typeFactoryPreserved [[intListDatatypeRT]]
  (assertOb (.eq () (.intConst () 0) (.intConst () 0)))

-- Empty datatype factory: trivially preserved.
/-- info: ok: true -/
#guard_msgs in
#eval typeFactoryPreserved [] (assertOb (.boolConst () true))

/-! ## Regression: a directly-applied lambda redex in an obligation term encodes
    (rather than hitting `appToSMTTerm`'s "Cannot encode .app expression").

    A front-end argument-value precondition can lower to a constant-lambda
    redex `(fun _ : string => true)(v)` that is injected into the proof
    obligation as an ASSUMPTION. Unlike a Core-surface function body it is not
    partial-evaluated first. The `betaReduce` pipeline phase contracts such
    redexes in every program expression before obligation extraction, so the
    SMT encoder (a pure Core-to-SMT mapping) never sees them; these tests pin
    the phase's coverage of each obligation-feeding position. -/

/-- `(fun _ : string => true)("v1")` — a constant-lambda redex, the shape
    an argument-value constraint lowers to. -/
private def constLambdaRedex : LExpr CoreLParams.mono :=
  .app ()
    (.abs () "ignored" (.some (.tcons "string" [])) (.boolConst () true))
    (.strConst () "v1")

/-- A second constant-lambda redex reducing to `false`, for the distinctness test. -/
private def constLambdaRedexFalse : LExpr CoreLParams.mono :=
  .app ()
    (.abs () "ignored" (.some (.tcons "string" [])) (.boolConst () false))
    (.strConst () "x")

/-- A program carrying `constLambdaRedex` in each obligation-feeding position:
    an `assume` (the argument-precondition shape), a variable definition
    (`init`), an `assert` goal, and a `distinct` declaration. -/
private def redexTestPgm : Program :=
  { decls := [
      .distinct ⟨"d", ()⟩ [constLambdaRedex, constLambdaRedexFalse] #[],
      .proc
        { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            Statement.assume "arg_precondition" constLambdaRedex #[],
            Statement.init ⟨"v", ()⟩ (.forAll [] (.tcons "bool" [])) (.det constLambdaRedex) #[],
            Statement.assert "goal" constLambdaRedex #[]] } #[]] }

-- The `betaReduce` phase contracts the redex in all four positions: the
-- assumption, the variable definition's RHS, the goal, and both distinctness
-- operands. Each position's concrete reduced expression is pinned on its own
-- output line, so a failure names the position that broke.
/--
info: distinct operands: [true, false]
assume: true
init rhs: true
assert goal: true
-/
#guard_msgs in
#eval show IO Unit from
  match (Core.BetaReduce.betaReduceProgram redexTestPgm).decls with
  | [.distinct _ es _, .proc p _] => do
    IO.println s!"distinct operands: {es.map (f!"{·}".pretty)}"
    match p.body with
    | .structured [
        Statement.assume _ a _,
        Statement.init _ _ (.det rhs) _,
        Statement.assert _ g _] => do
      IO.println s!"assume: {f!"{a}".pretty}"
      IO.println s!"init rhs: {f!"{rhs}".pretty}"
      IO.println s!"assert goal: {f!"{g}".pretty}"
    | _ => IO.println "UNEXPECTED body shape"
  | _ => IO.println "UNEXPECTED decl shape"

/-- Render each obligation of `pgm` for `#guard_msgs`: obligation count, then
    per obligation its label and either the encoded shape (assumption terms
    rendered through SMTDDM, definition/declaration counts, the goal term) or
    the encoder's error text. Pins the concrete encoder output, not just
    `.ok`/`.error`. -/
private def printRedexObligations (pgm : Program) : IO Unit := do
  match Core.ObligationExtraction.extractObligations pgm with
  | .error e => IO.println s!"extract error: {e}"
  | .ok obs =>
    IO.println s!"{obs.toList.length} obligation(s)"
    for ob in obs.toList do
      match (Env.init.addDatatypes []).mapError (f!"{·}") >>= fun env =>
            encodeObligationToSMT env.factory (.init { ctx := SMT.Context.default }) ob with
      | .ok (res, _) =>
        let render (t : Term) : String :=
          match Strata.SMTDDM.termToString t with
          | .ok s => s
          | .error e => s!"<render error: {e}>"
        IO.println s!"{ob.label}: assumptions [{", ".intercalate (res.assumptions.map render)}], \
          {res.varDefs.length} def(s), {res.varDecls.length} decl(s), goal {render res.goal}"
      | .error e => IO.println s!"{ob.label}: ERROR: {e.pretty}"

-- Composed seam test: obligations extracted from the reduced program encode
-- cleanly through `encodeObligationToSMT`, and the encoded terms are the
-- reduced constants — pinning that the phase leaves nothing the encoder
-- rejects and what the encoder actually produces.
/--
info: 1 obligation(s)
goal: assumptions [(distinct true false), true], 1 def(s), 0 decl(s), goal true
-/
#guard_msgs in
#eval printRedexObligations (Core.BetaReduce.betaReduceProgram redexTestPgm)

-- Un-reduced control: the same program WITHOUT the phase fails to encode —
-- the redex reaches `appToSMTTerm`'s catch-all, pinned by the concrete
-- "Cannot encode .app expression" error on the named obligation. This shows
-- the phase is load-bearing (if the encoder ever learns to reduce, this
-- expectation should be revisited together with the phase).
/--
info: 1 obligation(s)
goal: ERROR: Cannot encode .app expression (fun ignored : string => true)("v1")
-/
#guard_msgs in
#eval printRedexObligations redexTestPgm

/-! ## emission-time pruning defers entry encoding errors

The fold step (`encodePathConditionEntry`) encodes each `PathConditionEntry`
into a *deferred* result; `snapshotObligation` forces only the entries whose
labels survive the `prunedLabels` filter. So an entry pruned at emission time (e.g. an
irrelevant axiom) must not fail an obligation the base flow would have
passed — and conversely, keeping the entry must still surface its error. Both
label-prunable entry kinds are covered: `.assumption` and `.distinct`. -/

/-- An obligation whose single assumption `bad_ax` is an unencodable redex,
    with a trivially encodable goal. -/
private def badAxOb : Imperative.ProofObligation Expression :=
  { label := "q", property := .assert,
    assumptions := [[.assumption "bad_ax"
      (.app () (.abs () "x" none (.bvar () 0)) (.intConst () 0))]],
    obligation := .boolConst () true, metadata := {} }

-- Pruning `bad_ax` at emission time: its deferred encoding error is never
-- forced, and the obligation encodes to just the goal — no assumption (or
-- definition/declaration) from `bad_ax` leaks into the output.
/-- info: Except.ok ([], 0, 0, Strata.SMT.Term.prim (Strata.SMT.TermPrim.bool true)) -/
#guard_msgs in
#eval (encodeObligationToSMT Core.Factory (.init { ctx := SMT.Context.default })
    badAxOb ["bad_ax"]).mapError toString |>.map
    fun (res, _) =>
      (res.assumptions, res.varDefs.length, res.varDecls.length, res.goal)

-- Not pruning `bad_ax` surfaces the kept entry's deferred encoding error.
/-- info: Except.error "Cannot encode .app expression (fun x : ($__unknown_type) => x)(0)" -/
#guard_msgs in
#eval (encodeObligationToSMT Core.Factory (.init { ctx := SMT.Context.default })
    badAxOb []).mapError toString |>.map
    fun (res, _) =>
      (res.assumptions, res.varDefs.length, res.varDecls.length, res.goal)

/-- An obligation whose single frame interleaves both label-prunable entry
    kinds in program order: an encodable distinct, an encodable assumption, an
    unencodable distinct, an unencodable assumption, and a second encodable
    assumption. -/
private def mixedOb : Imperative.ProofObligation Expression :=
  { label := "q", property := .assert,
    assumptions := [[
      .distinct "good_d" [.intConst () 0, .intConst () 1],
      .assumption "good_ax_1" (.boolConst () true),
      .distinct "bad_d"
        [.app () (.abs () "y" none (.bvar () 0)) (.intConst () 7), .intConst () 2],
      .assumption "bad_ax"
        (.app () (.abs () "x" none (.bvar () 0)) (.intConst () 0)),
      .assumption "good_ax_2" (.boolConst () false)]],
    obligation := .boolConst () true, metadata := {} }

/-- Render encoding `ob` under `pruned`: the kept asserted terms,
    definition/declaration counts and goal, or the encoder's error. -/
private def prunedSummary (ob : Imperative.ProofObligation Expression)
    (pruned : List String) : String :=
  let render (t : Term) : String :=
    match Strata.SMTDDM.termToString t with
    | .ok s => s
    | .error e => s!"<render error: {e}>"
  match encodeObligationToSMT Core.Factory (.init { ctx := SMT.Context.default }) ob pruned with
  | .error e => s!"ERROR: {e.pretty}"
  | .ok (res, _) =>
    s!"asserted [{", ".intercalate (res.assumptions.map render)}], \
      {res.varDefs.length} def(s), {res.varDecls.length} decl(s), goal {render res.goal}"

-- Partial pruning of both kinds at once: the two unencodable entries are
-- pruned, so neither deferred error is forced, and every kept entry is still
-- emitted — distincts first, then assumptions, each in program order.
/-- info: "asserted [(distinct 0 1), true, false], 0 def(s), 0 decl(s), goal true" -/
#guard_msgs in
#eval prunedSummary mixedOb ["bad_d", "bad_ax"]

-- Pruning only the bad distinct leaves the bad assumption kept, so the
-- *assumption* path's deferred error surfaces.
/-- info: "ERROR: Cannot encode .app expression (fun x : ($__unknown_type) => x)(0)" -/
#guard_msgs in
#eval prunedSummary mixedOb ["bad_d"]

-- Mirror image: pruning only the bad assumption leaves the bad distinct kept,
-- so the *distinct* path's deferred error surfaces (the `y`/`7` redex). Pruning
-- is by label, not "drop whatever fails".
/-- info: "ERROR: Cannot encode .app expression (fun y : ($__unknown_type) => y)(7)" -/
#guard_msgs in
#eval prunedSummary mixedOb ["bad_ax"]

-- Pruning a kept-encodable entry of each kind alongside the unencodable ones:
-- only `good_ax_2` survives, pinning that both filters drop exactly the named
-- labels rather than a prefix or suffix of the frame, and that an emptied
-- distinct list contributes nothing.
/-- info: "asserted [false], 0 def(s), 0 decl(s), goal true" -/
#guard_msgs in
#eval prunedSummary mixedOb ["good_d", "good_ax_1", "bad_d", "bad_ax"]

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
#eval! Core.verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := false})

-- Test verification with Array theory
/--
info:
Obligation: UpdateAndRead_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval! Core.verify simpleMapProgram (options := {Core.VerifyOptions.quiet with useArrayTheory := true})

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
#eval! Core.verify quotedStringProgram (options := Core.VerifyOptions.quiet)

-- A `frac{n, d}` literal whose value has no terminating decimal expansion is
-- encoded to SMT as exact real division, so it verifies precisely rather than
-- hitting the old `Non-decimal real value` encoding error. `1/3 + 1/3 + 1/3`
-- is exactly `1.0` (holds), while `-2/3 == 2/3` is false (fails).
def nonDecimalFracProgram :=
#strata
program Core;

procedure P()
{
  assert [three_thirds]: real.add(real.add(frac{1, 3}, frac{1, 3}), frac{1, 3}) == 1.0;
  assert [neg_neq_pos]: real.neg(frac{2, 3}) == frac{2, 3};
};
#end

/--
info:
Obligation: three_thirds
Property: assert
Result: ✅ pass

Obligation: neg_neq_pos
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify nonDecimalFracProgram (options := Core.VerifyOptions.quiet)

end Strata

end
