/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.Counterexample.ModelToValuation
meta import Strata.Languages.Core.Counterexample.ValuationToRun
meta import Strata.Languages.Core.Counterexample.ModelAnonymous
meta import StrataTest.DL.SMT.ModelTestHarness
meta import StrataTest.Util.TimeBound
import StrataDDM.Integration.Lean.HashCommands

/-! # Solver models read back as Core values

A counterexample is confirmed only when the solver's model, read back as Core values,
fails the obligation it was found for. Here two model shapes are read back, from the
solver's answer to the VC check (`runVCCheck`) and to the input store and oracle of replay
(`valuationToEnv`), whose bound input values the tests pin:

- cvc5 binds a constructor with `let` and applies the bound name:
  `(let ((_let_1 (as Cons (List Int)))) (_let_1 1 (_let_1 7 (as Nil (List Int)))))`.
- z3 names the first element of both `S int` and `S bool` `S!val!0`.

Each answer read back for a program is a real solver output (z3 4.12.6, cvc5 1.3.4) to its query, in
which the verifier names the input `x` as `x@1`; no solver runs at test time except in the
`Core.verify` checks. Each pipeline stage is the verifier's: `solverResult` (parsing), the lift
(`smtTermToLExpr`, `smtTermIsValue`), the type gate (`checkedModel`), the anonymous values
(`extendAnon`), the VC check, and the input store (`modelValuation`, `valuationToEnv`).
-/

meta section
open StrataDDM (Program)

namespace Strata.CounterexampleSolverModelTest

open _root_.Lambda _root_.Imperative _root_.Core Strata.SMT.ModelTestHarness

/-! ## The pipeline -/

/-- The factory and the obligations of `p`, after type checking and symbolic evaluation. -/
private def obligationsOf (p : StrataDDM.Program) :
    IO (@Lambda.Factory CoreLParams × List (ProofObligation Expression)) := do
  let (prog, errs) := TransM.run Inhabited.default (translateProgram p)
  unless errs.isEmpty do throw (IO.userError "translation failed")
  match typeCheckAndEval VerifyOptions.quiet prog with
  | .ok ([E], _) => return (E.exprEnv.config.factory, E.deferred.toList)
  | .ok _ => throw (IO.userError "expected one environment")
  | .error e => throw (IO.userError (toString e))

/-- The answer `stdout` to the validity check of `p`'s only obligation read back: the VC
    check's verdict, and the input store and oracle replay reconstructs from the model
    (`valuationToEnv`), whose inputs are the variables the obligation reads: the value each
    input is bound to, and the oracle's choices. -/
private def readBack (p : StrataDDM.Program) (stdout : String) : IO String := do
  let (F, obs) ← obligationsOf p
  let [o] := obs | return s!"{obs.length} obligations"
  let vars := (obligationReadVars o).eraseDups
  let typed : List Expression.TypedIdent := vars.map fun (n, ty) => (n, .forAll [] ty)
  let .ok (_, .sat m) ← readAnswer typed stdout | return "no model"
  let ctors : Std.HashSet String :=
    .ofList ((F.toArray.filter (·.isConstr)).toList.map (·.name.name))
  let lm := checkedModel F o
    (m.map fun (k, t) => (k, smtTermToLExpr t ctors, smtTermIsValue t ctors))
  let F := extendAnon F (lm.map (·.2.1))
  let verdict := (runVCCheck F 20000 lm o true).describe
  let unit : PassiveUnit := { inputs := vars, statements := [] }
  let link : ObligationExtraction.ExtractBackLink :=
    { entryStatements := [], targetLabel := o.label, events := [] }
  let fmt (e : Expression.Expr) : String := toString (Std.format e)
  let store := match valuationToEnv F unit o link (modelValuation (valuationDefaults F o) lm) with
    | .ok (env, oracle) =>
      let bound := vars.map fun (nt : Expression.Ident × _) =>
        s!"\n  {nt.1.name} ↦ {match env.store.get nt.1 with | some v => fmt v | none => "unbound"}"
      s!"input store:{String.join bound}\noracle: {oracle.map fmt}"
    | .error e => s!"input store rejected: {repr e}"
  return s!"{vars.map (·.1.name)}: {verdict}\n{store}"

/-! ## A map value the reader cannot lift (z3)

z3 may print an array as `(_ as-array k!0)`, which the model reader drops, so the valuation
leaves `a@1` unbound although the solver assigned it. A map type has no default value
(`defaultValueIn`), so `a@1` stays unbound: the VC check cannot evaluate the goal and reports
`can't-validate`, not a verdict about a value the solver did not choose. -/

/-- A failure that depends on a nested map value. -/
def nested : StrataDDM.Program :=
#strata
program Core;
procedure nested(a : Map int (Map int int)) {
  assert [nestedBad]: a[1][2] != 7;
};
#end

/-- The VC check's verdict on the answer `stdout` to `nested`'s validity check. -/
private def nestedVerdict (stdout : String) : IO String := do
  let (F, obs) ← obligationsOf nested
  let [o] := obs | return s!"{obs.length} obligations"
  let typed : List Expression.TypedIdent :=
    (obligationReadVars o).eraseDups.map fun (n, ty) => (n, .forAll [] ty)
  let .ok (_, .sat m) ← readAnswer typed stdout | return "no model"
  let lm := checkedModel F o (m.map fun (k, t) => (k, smtTermToLExpr t {}, smtTermIsValue t {}))
  return (runVCCheck F 20000 lm o true).describe

/-- info: "can't-validate: goal did not reduce to a boolean" -/
#guard_msgs in
#eval nestedVerdict "sat\n((a@1 ((_ as-array k!0))))\n"

/-! ## A constructor bound with `let` (cvc5)

`second` fails only at `xs = Cons(1, Cons(7, Nil()))`. cvc5 binds `Cons` to `_let_1` and
applies `_let_1`; z3, the control, prints the constructor itself. Both read back as the
same value, which fails the assertion. -/

/-- A failure reached only when the generic list `xs` is `[1, 7]`. -/
def second : StrataDDM.Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure second(xs : List int) {
  assert [secondBad]: xs != Cons(1, Cons(7, Nil()));
};
#end

/--
info: [xs@1]: genuine
input store:
  xs@1 ↦ Cons(1, Cons(7, Nil))
oracle: []
[xs@1]: genuine
input store:
  xs@1 ↦ Cons(1, Cons(7, Nil))
oracle: []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← readBack second
    ("sat\n((xs@1 (let ((_let_1 (as Cons (List Int)))) " ++
      "(_let_1 1 (_let_1 7 (as Nil (List Int)))))))\n"))
  IO.println (← readBack second "sat\n((xs@1 (Cons 1 (Cons 7 Nil))))\n")

/-- The lifted value of `x` in the answer `stdout`. -/
private def liftedValue (stdout : String) : IO String := do
  let .ok (_, .sat [(_, t)]) ← readAnswer [(⟨"x", ()⟩, .forAll [] .int)] stdout
    | return "no model"
  return toString (Std.format (smtTermToLExpr t))

/-! The `let` substitution on its own: a bound name in head position takes the
arguments of its use after those of its bound term, a nullary use becomes the bound
term, and the bindings are parallel: in the last answer `h` is bound to the outer `p`,
which is unbound. -/

/--
info: Cons(1, Cons(7, Nil))
f(1, 2, 3)
g(Cons(5, Nil), Nil)
f(1, p(2))
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← liftedValue
    "sat\n((x (let ((_let_1 (as Cons (List Int)))) (_let_1 1 (_let_1 7 (as Nil (List Int)))))))\n")
  IO.println (← liftedValue "sat\n((x (let ((p (f 1))) (p 2 3))))\n")
  IO.println (← liftedValue
    "sat\n((x (let ((c Cons) (n Nil)) (g (c 5 n) n))))\n")
  IO.println (← liftedValue "sat\n((x (let ((p f) (h p)) (p 1 (h 2)))))\n")

/-! ## Anonymous values of two instances of one sort (z3)

`twoSorts` fails at `u1 = u2` and `v1 = v2`, of sorts `S int` and `S bool`. z3 names the
elements of both sorts `S!val!0`; cvc5 names them `@(S Int)_0` and `@(S Bool)_0`. The
control `oneSort` has the single sort `S int`. -/

/-- A failure whose model has elements of two instances of one sort constructor. -/
def twoSorts : StrataDDM.Program :=
#strata
program Core;
type S (a : Type);
procedure p(u1 : S int, u2 : S int, v1 : S bool, v2 : S bool) {
  assert [bad]: u1 != u2 || v1 != v2;
};
#end

/-- The same failure with the single instance `S int`. -/
def oneSort : StrataDDM.Program :=
#strata
program Core;
type S (a : Type);
procedure p(u1 : S int, u2 : S int) {
  assert [bad]: u1 != u2;
};
#end

/-- The sort `S ty`. -/
private def sortS (ty : LMonoTy) : LMonoTy := .tcons "S" [ty]

/--
info: [u1@1, u2@1, v1@1, v2@1]: genuine
input store:
  u1@1 ↦ |S!val!0 : (S int)|
  u2@1 ↦ |S!val!0 : (S int)|
  v1@1 ↦ |S!val!0 : (S bool)|
  v2@1 ↦ |S!val!0 : (S bool)|
oracle: []
[u1@1, u2@1, v1@1, v2@1]: genuine
input store:
  u1@1 ↦ |@(S Int)_0 : (S int)|
  u2@1 ↦ |@(S Int)_0 : (S int)|
  v1@1 ↦ |@(S Bool)_0 : (S bool)|
  v2@1 ↦ |@(S Bool)_0 : (S bool)|
oracle: []
[u1@1, u2@1]: genuine
input store:
  u1@1 ↦ |S!val!0 : (S int)|
  u2@1 ↦ |S!val!0 : (S int)|
oracle: []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← readBack twoSorts
    "sat\n((u1@1 S!val!0)\n (u2@1 S!val!0)\n (v1@1 S!val!0)\n (v2@1 S!val!0))\n")
  IO.println (← readBack twoSorts
    "sat\n((u1@1 (as |@(S Int)_0| (S Int))) (u2@1 (as |@(S Int)_0| (S Int))) \
     (v1@1 (as |@(S Bool)_0| (S Bool))) (v2@1 (as |@(S Bool)_0| (S Bool))))\n")
  IO.println (← readBack oneSort "sat\n((u1@1 S!val!0)\n (u2@1 S!val!0))\n")

/-! An anonymous value is named by the solver's name and the sort: one solver name at two
sorts gives two names, each still a solver element name. -/

#guard anonName "S!val!0" (sortS .int) != anonName "S!val!0" (sortS .bool)
#guard isSolverElementName (anonName "S!val!0" (sortS .int))
#guard isSolverElementName (anonName "@(S Int)_0" (sortS .int))

/-! ## Arrays (z3, array theory)

With the array theory, z3 gives a map an array term: `((as const (Array K V)) d)` and
`(store a k v)` read back as the map literals they denote. -/

/-- A failure reached only when `a[1] == 5`, `b[2]` is false and `b[3]` is true. -/
def mapAt : StrataDDM.Program :=
#strata
program Core;
procedure mapAt(a : Map int int, b : Map int bool) {
  assert [mapBad]: a[1] != 5 || b[2] || !(b[3]);
};
#end

/--
info: [a@1, b@1]: genuine
input store:
  a@1 ↦ mapConst<int>(5)
  b@1 ↦ (mapConst<int>(true))[2:=false]
oracle: []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← readBack mapAt
    ("sat\n((a@1 ((as const (Array Int Int)) 5))\n" ++
      " (b@1 (store ((as const (Array Int Bool)) true) 2 false)))\n"))

/-! ## End to end

The model the verifier reports for `second` is the list itself, under cvc5 as under z3. -/

/--
info:
Obligation: secondBad
Property: assert
Result: ❌ fail
Model:
(xs@1, Cons(1, Cons(7, Nil)))
-/
#guard_msgs in
#eval Core.verify second (options := { VerifyOptions.models with solver := "cvc5" })

/--
info:
Obligation: secondBad
Property: assert
Result: ❌ fail
Model:
(xs@1, Cons(1, Cons(7, Nil)))
-/
#guard_msgs in
#eval Core.verify second (options := { VerifyOptions.models with solver := "z3" })

/-! ## Completing a valuation over many reads -/

/-- The `int` variable `y{k}`. -/
private def yv (k : Nat) : Expression.Expr := .fvar default ⟨s!"y{k}", ()⟩ (some .int)

/-- The obligation with the `n` assumptions `y_k == y_k` and the goal `y0 == 1`. -/
private def manyReads (n : Nat) : ProofObligation Expression :=
  { label := "t", property := .assert,
    assumptions := [(List.range n).map fun k => .assumption "a" (.eq default (yv k) (yv k))],
    obligation := .eq default (yv 0) (.intConst default 1), metadata := {} }

/-- The evaluation fuel of the VC check below, ample for the 3200 assumptions. -/
private def manyReadsFuel : Nat := 20000

-- A model binding none of the 3200 variables the obligation reads: the VC check completes
-- each with its default and finds a counterexample, within 10 s.
/-- info: some "genuine" -/
#guard_msgs in
#eval StrataTest.TimeBound.withinMs 10000 fun _ =>
  (runVCCheck Core.Factory manyReadsFuel [] (manyReads 3200) true).describe

end Strata.CounterexampleSolverModelTest

end
