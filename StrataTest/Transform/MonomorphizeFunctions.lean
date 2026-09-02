/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.MonomorphizeFunctions
meta import Strata.Transform.MonomorphizeProcedures
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.TerminationCheck
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init

meta section

open Strata

/-! ## `MonomorphizeFunctions` tests

`MonomorphizeFunctions` duplicates each polymorphic top-level function once per
distinct ground type-instantiation it is used at (`$__mono#…` copies), rewrites
references, and drops the polymorphic originals (an unused one vanishes).

It runs just after `typeCheckPhase`, because a function call site only reveals
its instantiation through the type annotation the type checker attaches to the
`.op` node.  The tests therefore feed the pass a translated, type-checked
program.
-/

section MonomorphizeFunctionsTests

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

/-- Translate `t`, type-check, then run `MonomorphizeFunctions`.  Returns the
    transformed program AND the final `Factory` (extracted from the
    `CoreTransformState`). -/
private def monoFns (t : StrataDDM.Program) :
    Except Message (Core.Program × Lambda.Factory Core.CoreLParams) := do
  let prog := translate t
  let tc ← Core.typeCheck quietOpts prog
  let seedState : Core.Transform.CoreTransformState :=
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  let (res, finalState) :=
    Core.Transform.runWith tc Core.MonomorphizeFunctions.run seedState
  match res with
  | .ok p => return (p, finalState.factory)
  | .error msg => throw msg

/-- Fuller-pipeline runner: `precondElim` + `termCheck` +
    `monomorphizeProcedures` + `typeCheck` + `MonomorphizeFunctions`,
    matching the order in `corePipelinePhases`.  Each upstream pass can
    change the set of reachable polymorphic-function callsites:
    `precondElim` inlines `requires` clauses as fresh `assert`s (and
    emits a `$$wf` procedure), `termCheck` emits `$$term` procedures +
    `D..adtRank` axioms for every recursive-function block, and
    `monomorphizeProcedures` substitutes a polymorphic procedure's type
    variables with fresh opaque types before type-checking. -/
private def monoFnsFullPipeline (t : StrataDDM.Program) :
    Except Message (Core.Program × Lambda.Factory Core.CoreLParams) := do
  let initState : Core.Transform.CoreTransformState :=
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  let (r1, s1) :=
    Core.Transform.runWith (translate t) Core.PrecondElim.precondElim initState
  let (_, p1) ← r1
  let (r2, s2) := Core.Transform.runWith p1 Core.TermCheck.termCheck s1
  let (_, p2) ← r2
  let (r3, s3) := Core.Transform.runWith p2 Core.monomorphizeProcedures s2
  let (_, p3) ← r3
  let tc ← Core.typeCheck quietOpts p3
  let (r4, sFinal) := Core.Transform.runWith tc Core.MonomorphizeFunctions.run s3
  let p4 ← r4
  return (p4, sFinal.factory)

/-- Format the monomorphized program as surface syntax. -/
private def fmtMonoFns (t : StrataDDM.Program) : IO Std.Format :=
  match monoFns t with
  | .error msg => throw (IO.userError s!"{msg}")
  | .ok (p, _fac) => return (Std.format p.stripMetaData)

/-- Format the monomorphized program produced by the full pipeline
    (`precondElim` + `termCheck` + `monomorphizeProcedures` + `typeCheck` +
    `MonomorphizeFunctions`) as surface syntax. -/
private def fmtMonoFnsFullPipeline (t : StrataDDM.Program) : IO Std.Format :=
  match monoFnsFullPipeline t with
  | .error msg => throw (IO.userError s!"{msg}")
  | .ok (p, _fac) => return (Std.format p.stripMetaData)

/-- No top-level function declaration retains type parameters after the pass.
    Returns `false` if the transformation itself failed; every example pairs its
    property guards with a `fmtMonoFns`/`monoSucceeds` guard that reports a
    transform failure loudly and distinctly from a genuine non-mono result. -/
private def allFuncsMonomorphic
    (r : Except Message (Core.Program × Lambda.Factory Core.CoreLParams)) : Bool :=
  match r with
  | .error _ => false
  | .ok (p, _) =>
    p.decls.all fun
      | .func f _ => f.typeArgs.isEmpty
      | .recFuncBlock fs _ => fs.all (·.typeArgs.isEmpty)
      | _ => true

/-- No Factory entry retains type parameters after the pass, except for known
    SMT-trigger meta-operators (`TriggerGroup.addTrigger`, …) which the CST
    converter matches by name and are intentionally left polymorphic.  Returns
    `false` if the transformation failed (see `allFuncsMonomorphic`). -/
private def factoryIsMonomorphic
    (r : Except Message (Core.Program × Lambda.Factory Core.CoreLParams)) : Bool :=
  match r with
  | .error _ => false
  | .ok (_, f) =>
    f.toArray.all fun lfunc =>
      lfunc.typeArgs.isEmpty || isTriggerMetaOp lfunc.name.name
where
  isTriggerMetaOp : String → Bool
    | "TriggerGroup.addTrigger" => true
    | "TriggerGroup.empty" => true
    | "Triggers.addGroup" => true
    | "Triggers.empty" => true
    | _ => false

/-- Count the top-level function declarations (single + block members).
    Returns `0` if the transformation failed; a `monoSucceeds`/`fmtMonoFns`
    guard on the same program keeps that sentinel from being read as a count. -/
private def funcCount
    (r : Except Message (Core.Program × Lambda.Factory Core.CoreLParams)) : Nat :=
  match r with
  | .error _ => 0
  | .ok (p, _) =>
    p.decls.foldl (init := 0) fun n d =>
      match d with
      | .func _ _ => n + 1
      | .recFuncBlock fs _ => n + fs.length
      | _ => n

/-- The monomorphized program type-checks against the *transformed* factory
    (the factory `MonomorphizeFunctions` produced, which drops the polymorphic
    Factory originals and adds the specialized copies).  Returns `false` if the
    transformation failed (see `allFuncsMonomorphic`). -/
private def typeChecks (t : StrataDDM.Program) : Bool :=
  match monoFns t with
  | .error _ => false
  | .ok (p, fac) =>
    match Core.typeCheck quietOpts p (factory := fac) with
    | .ok _ => true
    | .error _ => false

private def monoSucceeds (t : StrataDDM.Program) : Bool := (monoFns t).isOk

/-- Full-pipeline analogue of `monoSucceeds`. -/
private def monoFullSucceeds (t : StrataDDM.Program) : Bool := (monoFnsFullPipeline t).isOk

---------------------------------------------------------------------
/-! ### Example 1: a polymorphic function used at a single concrete type -/

private def idPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(out r : int)
spec {
  ensures r == 5;
}
{
  r := id(5);
};
#end

/--
info: program Core;

function |$__mono#id#int| (x : int) : int {
  x
}
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: r == 5;
  } {
  r := |$__mono#id#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns idPgm

#guard allFuncsMonomorphic (monoFns idPgm)
#guard factoryIsMonomorphic (monoFns idPgm)
#guard typeChecks idPgm

---------------------------------------------------------------------
/-! ### Example 2: used at two distinct types → two specialized copies -/

private def idTwoPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(out r : int, out b : bool)
spec {
  ensures r == 5;
}
{
  r := id(5);
  b := id(true);
};
#end

/--
info: program Core;

function |$__mono#id#int| (x : int) : int {
  x
}
function |$__mono#id#bool| (x : bool) : bool {
  x
}
procedure P (out r : int, out b : bool)
spec {
  ensures [P_ensures_0]: r == 5;
  } {
  r := |$__mono#id#int|(5);
  b := |$__mono#id#bool|(true);
};
-/
#guard_msgs in
#eval fmtMonoFns idTwoPgm

#guard allFuncsMonomorphic (monoFns idTwoPgm)
#guard factoryIsMonomorphic (monoFns idTwoPgm)
#guard typeChecks idTwoPgm

---------------------------------------------------------------------
/-! ### Example 3: an unused polymorphic function is removed -/

private def unusedPgm :=
#strata
program Core;
function unused<a>(x : a) : a { x }
procedure P(out r : int)
spec {
  ensures r == 5;
}
{
  r := 5;
};
#end

/--
info: program Core;

procedure P (out r : int)
spec {
  ensures [P_ensures_0]: r == 5;
  } {
  r := 5;
};
-/
#guard_msgs in
#eval fmtMonoFns unusedPgm

#guard allFuncsMonomorphic (monoFns unusedPgm)
#guard factoryIsMonomorphic (monoFns unusedPgm)
#guard funcCount (monoFns unusedPgm) == 0
#guard typeChecks unusedPgm

---------------------------------------------------------------------
/-! ### Example 3b: a program with no polymorphic functions is a no-op

The pass has nothing to specialize, so it passes every declaration through
unchanged (the monomorphic `inc` keeps its name and body, `funcCount` is
stable, and its call site is untouched). -/

private def monoOnlyPgm :=
#strata
program Core;
function inc(x : int) : int { int.add(x, 1) }
procedure P(out r : int)
spec {
  ensures r == 6;
}
{
  r := inc(5);
};
#end

/--
info: program Core;

function inc (x : int) : int {
  int.add(x, 1)
}
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: r == 6;
  } {
  r := inc(5);
};
-/
#guard_msgs in
#eval fmtMonoFns monoOnlyPgm

#guard allFuncsMonomorphic (monoFns monoOnlyPgm)
#guard factoryIsMonomorphic (monoFns monoOnlyPgm)
#guard funcCount (monoFns monoOnlyPgm) == 1
#guard typeChecks monoOnlyPgm

---------------------------------------------------------------------
/-! ### Example 4: transitive specialization across functions -/

private def transitivePgm :=
#strata
program Core;
function g<a>(x : a) : a { x }
function f<a>(x : a) : a { g(x) }
procedure P(out r : int)
spec {
  ensures r == 5;
}
{
  r := f(5);
};
#end

/--
info: program Core;

function |$__mono#g#int| (x : int) : int {
  x
}
function |$__mono#f#int| (x : int) : int {
  |$__mono#g#int|(x)
}
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: r == 5;
  } {
  r := |$__mono#f#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns transitivePgm

#guard allFuncsMonomorphic (monoFns transitivePgm)
#guard factoryIsMonomorphic (monoFns transitivePgm)
#guard typeChecks transitivePgm

---------------------------------------------------------------------
/-! ### Example 5: end-to-end verification via `Core.verify` -/

private def verifyPgm : StrataDDM.Program :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(out r : int)
spec {
  ensures r == 5;
}
{
  r := id(5);
};
#end

private def verifyMono (t : StrataDDM.Program)
    (options : Core.VerifyOptions := .default) : IO Core.VCResults :=
  EIO.toIO (fun s => IO.userError s) (Core.verifyProgram (translate t) options)

/--
info:
Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono verifyPgm quietOpts

---------------------------------------------------------------------
/-! ### Example 6: a used recursive polymorphic function is monomorphized

A recursive polymorphic function used at a ground type is specialized into a
monomorphic recursive block that the SMT encoder accepts. -/

private def recUsedPgm :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
rec function len<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, len(MyList..tl(xs)))
};
procedure P(out r : int)
spec {
  ensures true;
}
{
  var xs : MyList int;
  xs := Cons(1, Nil());
  r := len(xs);
};
#end

/--
info: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
rec function |$__mono#len#int| (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, |$__mono#len#int|(MyList..tl(xs)))
};
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: true;
  } {
  var xs : (MyList int);
  xs := Cons(1, Nil);
  r := |$__mono#len#int|(xs);
};
-/
#guard_msgs in
#eval fmtMonoFns recUsedPgm

#guard allFuncsMonomorphic (monoFns recUsedPgm)
#guard factoryIsMonomorphic (monoFns recUsedPgm)
#guard typeChecks recUsedPgm

---------------------------------------------------------------------
/-! ### Example 7: transitive polymorphic calls at distinct type args

`P` calls `f` at two types, and `f<T>` in turn calls `g` at two different type
argument tuples that depend on `T`.  This produces every cross-product of
instantiations: `g<int, int>`, `g<string, int>`, `g<int, bool>`, `g<string, bool>`,
plus `f<int>` and `f<bool>`. -/

private def transitiveMultiInstPgm :=
#strata
program Core;
function g<a, b>(x : a, y : b) : b { y }
function f<a>(x : a) : a { g(1, g("s", x)) }
procedure P(out r : int, out b : bool)
spec {
  ensures true;
}
{
  r := f(5);
  b := f(true);
};
#end

/--
info: program Core;

function |$__mono#g#int#int| (x : int, y : int) : int {
  y
}
function |$__mono#g#string#int| (x : string, y : int) : int {
  y
}
function |$__mono#g#int#bool| (x : int, y : bool) : bool {
  y
}
function |$__mono#g#string#bool| (x : string, y : bool) : bool {
  y
}
function |$__mono#f#int| (x : int) : int {
  |$__mono#g#int#int|(1, |$__mono#g#string#int|("s", x))
}
function |$__mono#f#bool| (x : bool) : bool {
  |$__mono#g#int#bool|(1, |$__mono#g#string#bool|("s", x))
}
procedure P (out r : int, out b : bool)
spec {
  ensures [P_ensures_0]: true;
  } {
  r := |$__mono#f#int|(5);
  b := |$__mono#f#bool|(true);
};
-/
#guard_msgs in
#eval fmtMonoFns transitiveMultiInstPgm

#guard allFuncsMonomorphic (monoFns transitiveMultiInstPgm)
#guard factoryIsMonomorphic (monoFns transitiveMultiInstPgm)
#guard typeChecks transitiveMultiInstPgm

---------------------------------------------------------------------
/-! ### Example 8: a used mutually recursive polymorphic block

`even`/`odd` are mutually recursive and share type parameters, so the pass
handles them as a unit: both members get specialized once for each ground
instantiation reached from a live context (here, `int`). -/

private def mutualRecUsedPgm :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
rec function evenLen<a>(@[cases] xs : MyList a) : bool
{
  if MyList..isNil(xs) then true else oddLen(MyList..tl(xs))
}
function oddLen<a>(@[cases] xs : MyList a) : bool
{
  if MyList..isNil(xs) then false else evenLen(MyList..tl(xs))
};
procedure P(out r : bool)
spec {
  ensures true;
}
{
  var xs : MyList int;
  xs := Cons(1, Nil());
  r := evenLen(xs);
};
#end

/--
info: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
rec function |$__mono#evenLen#int| (@[cases] xs : MyList int) : bool
{
  if MyList..isNil(xs) then true else |$__mono#oddLen#int|(MyList..tl(xs))
}
function |$__mono#oddLen#int| (@[cases] xs : MyList int) : bool
{
  if MyList..isNil(xs) then false else |$__mono#evenLen#int|(MyList..tl(xs))
};
procedure P (out r : bool)
spec {
  ensures [P_ensures_0]: true;
  } {
  var xs : (MyList int);
  xs := Cons(1, Nil);
  r := |$__mono#evenLen#int|(xs);
};
-/
#guard_msgs in
#eval fmtMonoFns mutualRecUsedPgm

#guard allFuncsMonomorphic (monoFns mutualRecUsedPgm)
#guard factoryIsMonomorphic (monoFns mutualRecUsedPgm)
#guard typeChecks mutualRecUsedPgm

---------------------------------------------------------------------
/-! ### Example 9: mutually recursive functions whose callees use fixed types

`f<a>` always calls `g` at a fixed argument type (forcing `g<int>`), and `g<a>`
always calls `f` at a fixed argument type (forcing `f<string>`).  Both members
declare `<a>`, but each is bound independently — the pass treats them as
individual polymorphic functions and specializes each only at the
instantiations reached by its own call sites: `f<int>` (from `P`), `g<int>`
(from `f<int>`'s body), `f<string>` (from `g<int>`'s body).  Plus three
`ignore` specializations discovered along the way. -/

private def unrelatedTypeArgsPgm :=
#strata
program Core;
function ignore<a, b>(x : a, y : b) : b { y }
rec function f<a>(x : a) : a
{
  ignore(g(0), x)
}
function g<a>(y : a) : a
{
  ignore(f(""), y)
};
procedure P(out r : int)
spec {
  ensures true;
}
{
  r := f(5);
};
#end

/--
info: program Core;

function |$__mono#ignore#int#int| (x : int, y : int) : int {
  y
}
function |$__mono#ignore#string#int| (x : string, y : int) : int {
  y
}
function |$__mono#ignore#int#string| (x : int, y : string) : string {
  y
}
rec function |$__mono#f#int| (x : int) : int
{
  |$__mono#ignore#int#int|(|$__mono#g#int|(0), x)
}
function |$__mono#f#string| (x : string) : string
{
  |$__mono#ignore#int#string|(|$__mono#g#int|(0), x)
}
function |$__mono#g#int| (y : int) : int
{
  |$__mono#ignore#string#int|(|$__mono#f#string|(""), y)
};
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: true;
  } {
  r := |$__mono#f#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns unrelatedTypeArgsPgm

#guard allFuncsMonomorphic (monoFns unrelatedTypeArgsPgm)
#guard factoryIsMonomorphic (monoFns unrelatedTypeArgsPgm)
#guard typeChecks unrelatedTypeArgsPgm

---------------------------------------------------------------------
/-! ### Example 10: mutual `recFuncBlock` whose members have different `typeArgs`

`f` and `g` are mutually recursive but declare separate type parameters (`<a>`
and `<b>`).  `f<a>` always calls `g` at `int` (via the `0` argument) and `g<b>`
always calls `f` at `string` (via the `""` argument), so the specialization
graph reached from `f<int>` is exactly `f<int>`, `g<int>` (from `f<int>`),
`f<string>` (from `g<int>`).  Each member of the block is specialized only at
the instantiations reached by its own call sites — even members that share
`typeArgs` names have independently-bound type parameters — and my pass emits
all specialized copies in one `.recFuncBlock`. -/

private def mutualDiffTypeArgsPgm :=
#strata
program Core;
function ignore<a, b>(x : a, y : b) : b { y }
rec function f<a>(x : a) : a
{
  ignore(g(0), x)
}
function g<b>(y : b) : b
{
  ignore(f(""), y)
};
procedure P(out r : int)
spec {
  ensures true;
}
{
  r := f(5);
};
#end

/--
info: program Core;

function |$__mono#ignore#int#int| (x : int, y : int) : int {
  y
}
function |$__mono#ignore#string#int| (x : string, y : int) : int {
  y
}
function |$__mono#ignore#int#string| (x : int, y : string) : string {
  y
}
rec function |$__mono#f#int| (x : int) : int
{
  |$__mono#ignore#int#int|(|$__mono#g#int|(0), x)
}
function |$__mono#f#string| (x : string) : string
{
  |$__mono#ignore#int#string|(|$__mono#g#int|(0), x)
}
function |$__mono#g#int| (y : int) : int
{
  |$__mono#ignore#string#int|(|$__mono#f#string|(""), y)
};
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: true;
  } {
  r := |$__mono#f#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns mutualDiffTypeArgsPgm

#guard allFuncsMonomorphic (monoFns mutualDiffTypeArgsPgm)
#guard factoryIsMonomorphic (monoFns mutualDiffTypeArgsPgm)
#guard typeChecks mutualDiffTypeArgsPgm

---------------------------------------------------------------------
/-! ### Example 11: mutual block with different arities of type parameters

`f<a>` takes one type parameter; `g<b, c>` takes two.  The pass specializes each
member at exactly the instantiations it is called at, and emits both in one
`.recFuncBlock`. -/

private def mutualDiffAritiesPgm :=
#strata
program Core;
function fst<a, b>(x : a, y : b) : a { x }
rec function f<a>(x : a) : a
{
  fst(x, g(0, true))
}
function g<b, c>(u : b, v : c) : b
{
  fst(u, f(""))
};
procedure P(out r : int)
spec {
  ensures true;
}
{
  r := f(5);
};
#end

/--
info: program Core;

function |$__mono#fst#int#int| (x : int, y : int) : int {
  x
}
function |$__mono#fst#int#string| (x : int, y : string) : int {
  x
}
function |$__mono#fst#string#int| (x : string, y : int) : string {
  x
}
rec function |$__mono#f#int| (x : int) : int
{
  |$__mono#fst#int#int|(x, |$__mono#g#int#bool|(0, true))
}
function |$__mono#f#string| (x : string) : string
{
  |$__mono#fst#string#int|(x, |$__mono#g#int#bool|(0, true))
}
function |$__mono#g#int#bool| (u : int, v : bool) : int
{
  |$__mono#fst#int#string|(u, |$__mono#f#string|(""))
};
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: true;
  } {
  r := |$__mono#f#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns mutualDiffAritiesPgm

#guard allFuncsMonomorphic (monoFns mutualDiffAritiesPgm)
#guard factoryIsMonomorphic (monoFns mutualDiffAritiesPgm)
#guard typeChecks mutualDiffAritiesPgm

---------------------------------------------------------------------
/-! ### Example 12: iteration cap on non-uniform polymorphic recursion

Non-uniform polymorphic recursion produces an unbounded family of ground
type instantiations — here `f<a>` calls itself at `MyList a`, generating
`f<int>`, `f<MyList int>`, `f<MyList (MyList int)>`, …  The worklist would
never drain, so the pass caps the number of specializations it will
process and aborts with a documented error.

Runs with a tiny cap (`10`) so the test triggers the cap quickly instead
of the production default. -/

private def unboundedRecPgm :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
rec function f<a>(x : a) : int { f(Cons(x, Nil())) };
procedure P(out r : int)
spec {
  ensures true;
}
{
  r := f(5);
};
#end

/-- Type-check `t`, then run `MonomorphizeFunctions` with a small cap.
    Returns the transform's `Except`-shaped error/success message. -/
private def monoFnsCappedMsg (t : StrataDDM.Program) (cap : Nat) : String :=
  let prog := translate t
  match Core.typeCheck quietOpts prog with
  | .error e => toString e.message
  | .ok tc =>
    match Core.Transform.run tc (fun p => Core.MonomorphizeFunctions.run p cap) with
    | .ok _ => "OK"
    | .error m => toString m

/--
info: "MonomorphizeFunctions: too many specializations (non-uniform polymorphic recursion is not supported)"
-/
#guard_msgs in
#eval monoFnsCappedMsg unboundedRecPgm 10

-- Cap boundary: a program that drains in *exactly* `cap` specializations still
-- succeeds (pins the `0`-fuel `pending.isEmpty` off-by-one fix in `Worklist`).
-- `idPgm` specializes `id` at exactly one ground type (`int`).
/--
info: "OK"
-/
#guard_msgs in
#eval monoFnsCappedMsg idPgm 1

---------------------------------------------------------------------
/-! ### Example 13: `MonomorphizeFunctions` after `PrecondElim` / `TermCheck`

`PrecondElim` inlines each call's `requires` clause as a fresh `assert`
(and emits a WF procedure), and `TermCheck` emits `$$term` procedures +
`D..adtRank` axioms for every recursive-function block.  Both can
introduce new call-sites that reference polymorphic functions or add
polymorphic axioms.  This example exercises `MonomorphizeFunctions` on
the output of that full transform chain to catch surprises those passes
might introduce.

The program has a poly recursive function `len<a>` used at `int` — which
`TermCheck` will decorate with `MyList..adtRank<a>` axioms and a `len$$term`
termination procedure — so `len`, the derived `MyList..adtRank`, and the
termination check are all specialized at `int` and discharged end-to-end.
-/

private def fullPipelinePgm :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
rec function len<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, len(MyList..tl(xs)))
};
procedure P(out r : int)
spec {
  ensures true;
}
{
  var xs : MyList int;
  xs := Cons(1, Nil());
  r := len(xs);
};
#end

#guard allFuncsMonomorphic (monoFnsFullPipeline fullPipelinePgm)
#guard factoryIsMonomorphic (monoFnsFullPipeline fullPipelinePgm)
#guard monoFullSucceeds fullPipelinePgm

-- End-to-end through the real pipeline: the specialized `len` verifies, its
-- body well-formedness holds, and the termination check (`len_terminates_0`,
-- specialized from the polymorphic `len<a>` at a fresh opaque type) is
-- discharged.
/--
info:
Obligation: len_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: len_terminates_0
Property: assert
Result: ✅ pass

Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono fullPipelinePgm quietOpts

---------------------------------------------------------------------
/-! ### Example 14: polymorphic function with a datatype precondition

A polymorphic function `head<a>(xs : MyList a) : a` guards its body with a
precondition `requires MyList..isCons(xs)`.  `PrecondElim` inlines this
precondition as an `assert` at every call site AND emits a `head$$wf`
well-formedness procedure for the function's body.  `MonomorphizeFunctions`
then specialises `head<a>` and its precondition at `int` (the ground
instantiation reached from `P`).

Exercises the interaction between:
* `PrecondElim` (introduces new call-sites at ground types),
* the datatype selector `MyList..hd` (polymorphic in Factory, must be
  specialised),
* and `MonomorphizeFunctions` (must specialise `head`, `MyList..hd`, and
  any preconditions transitively).
-/

private def polyPrecondPgm :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
function head<a>(xs : MyList a) : a
  requires MyList..isCons(xs);
{
  MyList..hd(xs)
}
procedure P(out r : int)
spec {
  ensures true;
}
{
  var xs : MyList int;
  xs := Cons(7, Nil());
  r := head(xs);
};
#end

#guard allFuncsMonomorphic (monoFnsFullPipeline polyPrecondPgm)
#guard factoryIsMonomorphic (monoFnsFullPipeline polyPrecondPgm)

/--
info: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
type $__opaque_head$$wf_a_0;
procedure head$$wf (xs : MyList $__opaque_head$$wf_a_0)
{
  assume [precond_head_0]: MyList..isCons(xs);
  assert [head_body_calls_MyList..hd_0]: MyList..isCons(xs);
};
function |$__mono#head#int| (xs : MyList int) : int {
  MyList..hd(xs)
}
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: true;
  } {
  var xs : (MyList int);
  xs := Cons(7, Nil);
  assert [set_r_calls_head_0]: MyList..isCons(xs);
  r := |$__mono#head#int|(xs);
};
-/
#guard_msgs in
#eval fmtMonoFnsFullPipeline polyPrecondPgm

---------------------------------------------------------------------
/-! ### Example 15: a polymorphic Factory op (`Map` `select`) end-to-end

`get0<v>(m : Map int v)` reads `m[0]`, i.e. the polymorphic Factory operator
`select`.  Instantiated at `v := int` it forces `select` to be specialised to a
ground `Map int int → int → int`, exercising the SMTEncoder's demangle dispatch
for a used Factory function. -/

private def mapGetPgm : StrataDDM.Program :=
#strata
program Core;
function get0<v>(m : Map int v) : v { m[0] }
procedure P(m : Map int int, out r : int)
spec {
  requires m[0] == 42;
  ensures r == 42;
}
{
  r := get0(m);
};
#end

#guard allFuncsMonomorphic (monoFns mapGetPgm)
#guard factoryIsMonomorphic (monoFns mapGetPgm)

/--
info: program Core;

function |$__mono#get0#int| (m : Map int int) : int {
  m[0]
}
procedure P (m : Map int int, out r : int)
spec {
  requires [P_requires_0]: m[0] == 42;
  ensures [P_ensures_1]: r == 42;
  } {
  r := |$__mono#get0#int|(m);
};
-/
#guard_msgs in
#eval fmtMonoFns mapGetPgm

#guard typeChecks mapGetPgm
#guard monoSucceeds mapGetPgm

/--
info:
Obligation: P_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono mapGetPgm quietOpts

---------------------------------------------------------------------
/-! ### Example 16: a Factory op whose surface syntax carries a mandatory type
    annotation (`mapConst`)

`mapConst<K>(v)` builds a constant map; its key type `K` cannot be inferred from
the single value argument, so the surface syntax carries it explicitly.  After
monomorphization the reference is the specialized `$__mono#mapConst#int#bool`, and
the CST printer must still recover `K` and emit `mapConst<int>(false)` — a bare
`mapConst(false)` would not re-parse.  Unlike sugar-rendered Factory ops (`m[k]`,
which look identical before and after specialization), this callsite makes the
Factory-op rewrite observable in the golden. -/

private def mapConstPgm :=
#strata
program Core;
procedure P(out r : bool)
spec {
  ensures true;
}
{
  var m : Map int bool;
  m := mapConst<int>(false);
  r := m[9];
};
#end

/--
info: program Core;

procedure P (out r : bool)
spec {
  ensures [P_ensures_0]: true;
  } {
  var m : (Map int bool);
  m := mapConst<int>(false);
  r := m[9];
};
-/
#guard_msgs in
#eval fmtMonoFns mapConstPgm

#guard allFuncsMonomorphic (monoFns mapConstPgm)
#guard factoryIsMonomorphic (monoFns mapConstPgm)
#guard typeChecks mapConstPgm

---------------------------------------------------------------------
/-! ### Full Verification Example 1: Procedure + Function monomorphization, poly pre/post

Combines both monomorphization passes end-to-end: a polymorphic procedure
`keep<T>` (specialised by `MonomorphizeProcedures`) whose `requires`/`ensures`
mention a polymorphic function `idf<a>` (specialised by
`MonomorphizeFunctions`). -/

private def prePostPgm : StrataDDM.Program :=
#strata
program Core;
function idf<a>(x : a) : a { x }
procedure keep<T>(x : T, out r : T)
spec {
  requires idf(x) == x;
  ensures r == idf(x);
}
{
  r := x;
};
procedure P(out r : int)
spec {
  ensures r == 7;
}
{
  call keep(7, out r);
};
#end

/--
info:
Obligation: keep_ensures_1
Property: assert
Result: ✅ pass

Obligation: callElimAssert_keep_requires_0_3
Property: assert
Result: ✅ pass

Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono prePostPgm quietOpts

---------------------------------------------------------------------
/-! ### Full Verification Example 2: polymorphic function used in an axiom

`idf<a>` is referenced from a top-level `axiom` at a ground type (`idf(2)`), so
the axiom is a polymorphic-use site the pass must specialise before SMT.  The
goal `r == 2` is discharged end-to-end. -/

private def axiomPgm : StrataDDM.Program :=
#strata
program Core;
function idf<a>(x : a) : a { x }
axiom [idf_two]: (idf(2) == 2);
procedure P(out r : int)
spec {
  ensures r == 2;
}
{
  r := idf(2);
};
#end

/--
info:
Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono axiomPgm quietOpts

---------------------------------------------------------------------
/-! ### Full Verification Example 3: polymorphic function used in a loop measure and invariant

`idf<a>` is referenced from a loop's `decreases` (measure) and from a loop
`invariant`, both at a ground type — the two remaining polymorphic-use sites.
Every loop-generated obligation (invariant entry, invariant maintenance,
measure lower-bound, measure decrease) plus the postcondition discharges. -/

private def measureInvariantPgm : StrataDDM.Program :=
#strata
program Core;
function idf<a>(x : a) : a { x }
procedure P(n : int, out r : int)
spec {
  requires (int.le(0, n));
  ensures (r == n);
}
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
    decreases int.sub(idf(n), i)
    invariant int.le(idf(0), i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
  r := i;
};
#end

/--
info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ✅ pass

Obligation: P_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono measureInvariantPgm quietOpts

---------------------------------------------------------------------
/-! ### Print-parse roundtrip: a monomorphized program re-parses

Monomorphization renames functions to `$__mono#<f>#<types>`, whose `#`
separators are not legal in a *bare* Strata identifier, so the printer must
pipe-quote every such name — at its declaration and at every reference — for
the printed program to re-parse.

`monoRoundtrips` checks `print (parse (print p)) = print p`.  Comparing
reformatted output (not merely parse success) catches semantic drift such as
wrong variable indices. -/
private def monoRoundtrips (t : StrataDDM.Program) : IO Bool := do
  match monoFns t with
  | .error _ => pure false
  | .ok (p, _) =>
    let printed := (Core.formatProgram p).pretty
    let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Core]
    let body := if printed.startsWith "program Core;\n\n" then
      (printed.drop "program Core;\n\n".length).toString else printed
    let inputCtx := StrataDDM.Parser.stringInputContext ⟨"mono-roundtrip-test"⟩ body
    try
      let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
      let (ast2, errs) := TransM.run Inhabited.default (translateProgram sp)
      pure (errs.isEmpty && (Core.formatProgram ast2).pretty == printed)
    catch _ => pure false

/--
info: done
-/
#guard_msgs in
#eval show IO Unit from do
  let cases : List (String × StrataDDM.Program) :=
    [("id", idPgm), ("idTwo", idTwoPgm), ("transitive", transitivePgm),
     ("transitiveMultiInst", transitiveMultiInstPgm), ("recUsed", recUsedPgm),
     ("mutualRecUsed", mutualRecUsedPgm), ("mutualDiffArities", mutualDiffAritiesPgm),
     ("mapGet", mapGetPgm)]
  for (nm, pgm) in cases do
    if !(← monoRoundtrips pgm) then IO.println s!"FAIL: {nm}"
  IO.println "done"

end MonomorphizeFunctionsTests

end
