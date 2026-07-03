/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda
meta import Strata.DL.Lambda.LExpr
meta import Strata.DL.Lambda.LState
meta import Strata.DL.Lambda.LTy
meta import Strata.DL.SMT.Term
meta import Strata.DL.SMT.Encoder
meta import Strata.Languages.Core.Env
meta import Strata.Languages.Core.Factory
meta import Strata.Languages.Core.Identifiers
meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core.SMTEncoder
meta import Strata.Languages.Core.Verifier

meta section

/-!
Unit tests for SMT encoding of factory functions that carry axioms which
reference *other* functions — including functions whose axioms (or bodies) call
each other cyclically, and a polymorphic function instantiated at two types.

Each test runs `runTest es funcs`, which calls `toSMTTerms` on `es` (the
"obligation" expressions) in an environment whose factory holds `funcs`, then
resolves the deferred function definitions, and prints the result captured by
`#guard_msgs`. The printed report has four parts to read and check:

* `Terms:`  — the obligation expressions `es`, encoded to SMT terms. Confirms
  the goal itself is encoded as expected.
* `UFs:`    — uninterpreted functions (`declare-fun`), one `id : (arg : ty, ...)
  -> out` line each. Check that every referenced function is declared, and that
  a *polymorphic* function appears once per distinct instantiation (e.g. both
  `(Int) -> Int` and `(Real) -> Real` — two entries that share the source name
  but are distinct `UF`s; they are given distinct SMT-LIB names at emission).
* `IFs:`    — interpreted functions (`define-fun`), printed as `signature :=
  body`. Check the body, and that an IF referenced by another IF's body appears
  *before* that caller (see the ordering note below).
* `Axioms:` — the asserted axiom terms. Check each function contributes its
  axiom at the right type instantiation, and that the cycle terminates (no
  duplicate or missing axioms).
-/

namespace Core

open Lambda
open Std
open Strata.SMT

section FuncWithAxiomsTests

/- A little `SMT.Context` printer, via SMTDDM -/

/-- Render a `UF` as a function signature `id : (argTy, ...) -> out`. -/
def ppUF (uf : UF) : Except String String := do
  let args ← uf.args.mapM fun ty => do
    return s!"{← Strata.SMTDDM.termTypeToString ty}"
  let outTy ← Strata.SMTDDM.termTypeToString uf.out
  return s!"{uf.id} : ({", ".intercalate args}) -> {outTy}"

/-- Render an `IF` as a function signature with param names. -/
def ppIF (f : IF) : Except String String := do
  let args ← f.args.mapM fun v => do
    return s!"{v.id} : {← Strata.SMTDDM.termTypeToString v.ty}"
  let outTy ← Strata.SMTDDM.termTypeToString f.out
  return s!"{f.id} : ({", ".intercalate args}) -> {outTy}"

/-- Pretty-print `SMT.Context` -/
def ppContext (ctx : SMT.Context) : Except String String := do
  let ufs ← ctx.ufs.toList.mapM ppUF
  let ifs ← ctx.ifs.toList.mapM fun f => do
    return s!"{← ppIF f} := {← Strata.SMTDDM.termToString f.body}"
  let axms ← ctx.axms.toList.mapM Strata.SMTDDM.termToString
  let sect (title : String) (lines : List String) : String :=
    if lines.isEmpty then s!"{title}: (none)\n"
    else s!"{title}:\n" ++ String.join (lines.map (s!"  {·}\n"))
  return sect "UFs" ufs ++ sect "IFs" ifs ++ sect "Axioms" axms

/-- A simplified version of ProofObligation.toSMTTerms.
    Encode a list of `LExpr`, `es` in an environment whose factory has been
    extended with `funcs`. -/
def encodeFuncsToSMT (es : List (LExpr CoreLParams.mono))
    (funcs : List (Lambda.LFunc CoreLParams)):
    Except Format String := do
  -- 1. Build an environment with all functions registered in the factory.
  let env ← (funcs.foldlM (fun (env : Env) f => env.addFactoryFunc f) Env.init).mapError
    (fun msg => f!"Error adding functions: {msg}")
  let factory := env.factory
  -- Seed the encoding context's `typeFactory` from the env's datatypes.
  let ctx := { SMT.Context.default with typeFactory := env.datatypes }

  -- 2. Encode the terms, then resolve/commit the deferred function definitions.
  let (terms, ctx, pending) ← toSMTTerms factory es ctx []
  let ctx ← processPendingFnDefs factory ctx pending

  -- 3/ Render terms and context through SMTDDM, lifting render errors into `Format`.
  let termStrs ← (terms.mapM Strata.SMTDDM.termToString).mapError (f!"{·}")
  let ctxStr ← (ppContext ctx).mapError (f!"{·}")
  let termLines := String.join (termStrs.map (s!"  {·}\n"))
  .ok s!"Terms:\n{termLines}{ctxStr}"

/-- Run `encodeFuncsToSMT` and print the result, for `#guard_msgs`. -/
def runTest (es : List (LExpr CoreLParams.mono))
    (funcs : List (Lambda.LFunc CoreLParams)) : IO Unit :=
  match encodeFuncsToSMT es funcs with
  | .ok s => IO.println s
  | .error e => IO.println s!"ERROR: {e.pretty}"

/-! ## Builders -/

private def intToInt : LMonoTy := .arrow .int .int

/- `name(arg)` where `name : Int → Int`. -/
private def appI (name : String) (arg : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  .app () (.op () ⟨name, ()⟩ (.some intToInt)) arg

/- `∀ (x : Int). lhs(x) == rhs(x)` -/
private def eqAxiomI (lhs rhs : String) : LExpr CoreLParams.mono :=
  .quant () .all "x" (.some .int) (LExpr.noTrigger ())
    (.eq () (appI lhs (.bvar () 0)) (appI rhs (.bvar () 0)))

/- A monomorphic `Int → Int` function `name` with a single axiom `∀ x. name(x) == callee(x)`. -/
private def monoFuncWithAxiom (name callee : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    inputs := [(⟨"v", ()⟩, .int)],
    output := .int,
    axioms := [eqAxiomI name callee] }

/- A monomorphic `Int → Int` function `name` with an axiom `∀ x. name(x) == x`. -/
private def monoFuncWithAxiomId (name : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    inputs := [(⟨"v", ()⟩, .int)],
    output := .int,
    axioms := [.quant () .all "x" (.some .int) (LExpr.noTrigger ())
                 (.eq () (appI name (.bvar () 0)) (.bvar () 0))] }

/-- An `Int → Int` function `name` whose function body is `callee(v)`. -/
private def monoDefFunc (name callee : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    inputs := [(⟨"v", ()⟩, .int)],
    output := .int,
    body := some (appI callee (.fvar () ⟨"v", ()⟩ (.some .int))) }

/-- An `Int → Int` function `name` with function body `body` and the axiom
    `∀ x. name(x) == axiomCallee(x)`. -/
private def monoDefFuncWithAxiom (name : String) (body : LExpr CoreLParams.mono)
    (axiomCallee : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    inputs := [(⟨"v", ()⟩, .int)],
    output := .int,
    body := some body,
    axioms := [eqAxiomI name axiomCallee] }

/-! ## Test 1: two monomorphic functions, one references the other -/

-- `f` has axiom `∀ x. f(x) == g(x)`; encoding `f(0) == 0` must pull in `g`,
-- which is declared before `f` (callee-before-caller). `g`'s axiom is
-- `∀ x. g(x) == x`.
/--
info: Terms:
  (= (f 0) 0)
UFs:
  g : (Int) -> Int
  f : (Int) -> Int
IFs: (none)
Axioms:
  (forall ((x Int)) (= (g x) x))
  (forall ((x Int)) (= (f x) (g x)))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appI "f" (.intConst () 0)) (.intConst () 0))]
  [monoFuncWithAxiom "f" "g", monoFuncWithAxiomId "g"]

/-! ## Test 2: three monomorphic functions whose axioms call each other cyclically -/

-- f → g → h → f.  Encoding a term that references `f` must resolve the whole
-- cycle (breaking it via the `seen` set) and declare callees before callers.
/--
info: Terms:
  (= (f 0) 0)
UFs:
  h : (Int) -> Int
  g : (Int) -> Int
  f : (Int) -> Int
IFs: (none)
Axioms:
  (forall ((x Int)) (= (h x) (f x)))
  (forall ((x Int)) (= (g x) (h x)))
  (forall ((x Int)) (= (f x) (g x)))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appI "f" (.intConst () 0)) (.intConst () 0))]
  [monoFuncWithAxiom "f" "g", monoFuncWithAxiom "g" "h", monoFuncWithAxiom "h" "f"]

/-! ## Test 3: three polymorphic functions whose axioms call each other -/

-- pf, qf, rf : ∀a. a → Int, with axioms pf(x)==qf(x), qf(x)==rf(x), rf(x)==pf(x).
private def polyTy : LMonoTy := .arrow (.ftvar "a") .int

private def appP (name : String) (arg : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  .app () (.op () ⟨name, ()⟩ (.some polyTy)) arg

private def eqAxiomP (lhs rhs : String) : LExpr CoreLParams.mono :=
  .quant () .all "x" (.some (.ftvar "a")) (LExpr.noTrigger ())
    (.eq () (appP lhs (.bvar () 0)) (appP rhs (.bvar () 0)))

private def polyFunc (name callee : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    typeArgs := ["a"],
    inputs := [(⟨"v", ()⟩, .ftvar "a")],
    output := .int,
    axioms := [eqAxiomP name callee] }

/--
info: Terms:
  (= (pf 0) 0)
UFs:
  rf : (Int) -> Int
  qf : (Int) -> Int
  pf : (Int) -> Int
IFs: (none)
Axioms:
  (forall ((x Int)) (= (rf x) (pf x)))
  (forall ((x Int)) (= (qf x) (rf x)))
  (forall ((x Int)) (= (pf x) (qf x)))
-/
#guard_msgs in
#eval runTest
  [(.eq () (.app () (.op () ⟨"pf", ()⟩ (.some intToInt)) (.intConst () 0)) (.intConst () 0))]
  [polyFunc "pf" "qf", polyFunc "qf" "rf", polyFunc "rf" "pf"]

/-! ## Test 4: an interpreted function whose body calls an axiomatized function -/

-- `d` is a `define-fun` with body `g(v)`; `g` is an uninterpreted function with
-- axiom `∀ x. g(x) == x`. Encoding `d(0) == 0` registers `g` (callee) before the
-- interpreted `d`, exercising the `IF` section.
/--
info: Terms:
  (= (d 0) 0)
UFs:
  g : (Int) -> Int
IFs:
  d : (v : Int) -> Int := (g v)
Axioms:
  (forall ((x Int)) (= (g x) x))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appI "d" (.intConst () 0)) (.intConst () 0))]
  [monoDefFunc "d" "g", monoFuncWithAxiomId "g"]

/-! ## Test 5: three interpreted functions with bodies and axioms calling each other -/

private def vInt : LExpr CoreLParams.mono := .fvar () ⟨"v", ()⟩ (.some .int)

/-- An interpreted identity `Int → Int` `name` (body `v`) with axiom `∀ x. name(x) == x` -/
private def monoDefFuncWithAxiomId (name : String) : Lambda.LFunc CoreLParams :=
  { name := ⟨name, ()⟩,
    inputs := [(⟨"v", ()⟩, .int)],
    output := .int,
    body := some vInt,
    axioms := [.quant () .all "x" (.some .int) (LExpr.noTrigger ())
                 (.eq () (appI name (.bvar () 0)) (.bvar () 0))] }

/--
info: Terms:
  (= (da 0) 0)
UFs: (none)
IFs:
  dc : (v : Int) -> Int := v
  db : (v : Int) -> Int := (dc v)
  da : (v : Int) -> Int := (db v)
Axioms:
  (forall ((x Int)) (= (dc x) x))
  (forall ((x Int)) (= (db x) (dc x)))
  (forall ((x Int)) (= (da x) (db x)))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appI "da" (.intConst () 0)) (.intConst () 0))]
  [monoDefFuncWithAxiom "da" (appI "db" vInt) "db",
   monoDefFuncWithAxiom "db" (appI "dc" vInt) "dc",
   monoDefFuncWithAxiomId "dc"]

/-! ## Test 6: one polymorphic function instantiated at two different types -/

-- `idp : ∀a. a → a` with axiom `∀ (x : a). idp(x) == x`, applied at both `Int`
-- and `Real`. The single source function yields two *distinct* UFs that share
-- the source name `idp` but differ in signature (`Int -> Int` vs `Real ->
-- Real`); each carries its axiom at its own instantiation. The shared name is
-- expected: dedup keys on the whole `UF` (name + arg/out types), and the two
-- are given distinct SMT-LIB names (e.g. `idp`, `idp@1`) at emission time.

/-- `idp(arg)` at instantiation where `idp : ty → ty`. -/
private def appIdp (ty : LMonoTy) (arg : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  .app () (.op () ⟨"idp", ()⟩ (.some (.arrow ty ty))) arg

private def idpFunc : Lambda.LFunc CoreLParams :=
  { name := ⟨"idp", ()⟩,
    typeArgs := ["a"],
    inputs := [(⟨"v", ()⟩, .ftvar "a")],
    output := .ftvar "a",
    axioms := [.quant () .all "x" (.some (.ftvar "a")) (LExpr.noTrigger ())
                 (.eq () (appIdp (.ftvar "a") (.bvar () 0)) (.bvar () 0))] }

/--
info: Terms:
  (= (idp 0) 0)
  (= (idp 0.0) 0.0)
UFs:
  idp : (Int) -> Int
  idp : (Real) -> Real
IFs: (none)
Axioms:
  (forall ((x Int)) (= (idp x) x))
  (forall ((x Real)) (= (idp x) x))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appIdp .int (.intConst () 0)) (.intConst () 0)),
   (.eq () (appIdp .real (.realConst () 0)) (.realConst () 0))]
  [idpFunc]

/-! ## Test 7: one polymorphic function referenced twice at the *same* type -/

-- Two references to `idp` both at `Int → Int` (`idp(0)` and `idp(1)`) produce
-- the *same* `UF`, so they dedup to a single declaration and a single axiom.
-- This is the converse of Test 6: distinct instantiations stay separate, but
-- repeated identical instantiations collapse. (Dedup keys on the whole `UF`,
-- i.e. name + monomorphic arg/out types, not on the source identifier.)
/--
info: Terms:
  (= (idp 0) 0)
  (= (idp 1) 1)
UFs:
  idp : (Int) -> Int
IFs: (none)
Axioms:
  (forall ((x Int)) (= (idp x) x))
-/
#guard_msgs in
#eval runTest
  [(.eq () (appIdp .int (.intConst () 0)) (.intConst () 0)),
   (.eq () (appIdp .int (.intConst () 1)) (.intConst () 1))]
  [idpFunc]

/-! ## Test 8: encodeUF then encodeFunctionDef on the same UF errors -/

-- Reference `g` first (emits `declare-fun g`), then try to define it:
--   encodeUF g; encodeFunctionDef g body
-- expect the IO.userError: "declared as uninterpreted before its definition".
/--
info: encodeFunctionDef: function 'g' was already declared as uninterpreted before its definition was encoded.
-/
#guard_msgs in
#eval show IO Unit from do
  let g : UF := { id := "g", args := [.int], out := .int }
  let gIF : IF := { id := "g", args := [⟨"v", .int⟩], out := .int, body := .var ⟨"v", .int⟩ }
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  try
    let _ ← (do
      let _ ← Encoder.encodeUF g
      let _ ← Encoder.encodeFunctionDef gIF
      : EncoderM Unit).run EncoderState.init |>.run solver
    IO.println "ERROR: expected an error but succeeded"
  catch e =>
    IO.println s!"{e}"

/-! ## Test 9: processPendingFnDefs commits all scheduled functions -/

-- After `processPendingFnDefs` succeeds, every UF from the pending queue must
-- satisfy `ctx'.committedFn`. This pins the "queue fully drained" invariant.
private def testAllCommitted : Except Format String := do
  let funcs := [monoFuncWithAxiom "f" "g", monoFuncWithAxiom "g" "h", monoFuncWithAxiom "h" "f"]
  let env ← (funcs.foldlM (fun (env : Env) f => env.addFactoryFunc f) Env.init).mapError
    (fun msg => f!"Error adding functions: {msg}")
  let factory := env.factory
  let ctx := { SMT.Context.default with typeFactory := env.datatypes }
  let (_, ctx, pending) ← toSMTTerms factory
    [(.eq () (appI "f" (.intConst () 0)) (.intConst () 0))] ctx []
  let ctx' ← processPendingFnDefs factory ctx pending
  let allCommitted := pending.all (fun p => SMT.Context.committedFn ctx' p.uf)
  return s!"{allCommitted}"

/-- info: true -/
#guard_msgs in
#eval do
  match testAllCommitted with
  | .ok s => IO.println s
  | .error e => IO.println s!"ERROR: {e.pretty}"

end FuncWithAxiomsTests

end Core
