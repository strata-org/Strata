/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import StrataDDM.Util.Format
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.CallElim
meta import Strata.Languages.Core.Counterexample.BackLinkCallElimOrigin
meta import Strata.Languages.Core.Counterexample.BackLinkCallElim

/-! # callElim origin extractor: fresh-name agreement with the pass

The extractor `Core.CallElim.callElimOrigin'`, run from the same initial
`CoreTransformState` as the call-elimination pass `Core.CallElim.callElim'`, records
per call site exactly the fresh names the pass generates, in the same order. The tests
compare, on three programs (two calls in one procedure, an `inout` parameter read
through `old` in a postcondition, and calls in both branches of an `if`):

  * `passGeneratedNames p`: the names the pass generates, in generation order;
  * `extractorFreshNames p`: the concatenation of every `CallOrigin.freshNames` the
    extractor records, in traversal order.

The axioms of the extractor are checked in `CounterexampleCallElimOriginAxioms.lean`,
since `#print axioms` cannot appear in a `module` file.
-/

meta section

open Core
open Core.Transform
open Core.CallElim
open Strata

namespace Strata.CallElimOriginTest

/-- Translate a parsed `#strata` program to `Core.Program`. -/
def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- The real forward pass's total fresh-name output, as name strings in
    generation order (oldest first). Runs `callElim'` from the empty initial
    `CoreTransformState` and reads the final generator log. -/
def passGeneratedNames (p : Core.Program) : List String :=
  let (_, finalState) := runWith p callElim' CoreTransformState.emp
  finalState.genState.generated.reverse.map (·.name)

/-- The extractor's recorded fresh names, as name strings in traversal order
    (each site oldest-first). Runs `callElimOrigin'` from the same empty initial
    `CoreTransformState`. An extractor error yields `["<extractor-error>"]`, which
    matches no list of generated names. -/
def extractorFreshNames (p : Core.Program) : List String :=
  match (runWith p callElimOrigin' CoreTransformState.emp).1 with
  | .ok origins => (origins.flatMap (·.freshNames)).map (·.name)
  | .error _ => ["<extractor-error>"]

/-- Number of `.call` sites the extractor records (`0` on an extractor error). -/
def extractorCallCount (p : Core.Program) : Nat :=
  match (runWith p callElimOrigin' CoreTransformState.emp).1 with
  | .ok origins => origins.length
  | .error _ => 0

---------------------------------------------------------------------
/-! ## Representative programs -/

/-- Multiple monomorphic calls in one procedure (two calls to `Double`),
    exercising sequential fresh-name generation across sites. -/
def MultiCallSrc :=
#strata
program Core;

procedure Double(n : int, out result : int)
spec {
  ensures [double_correct]: (result == int.mul(n, 2));
}
{
  result := int.add(n, n);
};

procedure TestProc(x : int, out output : int)
spec {
  ensures [testProc_result]: (output == int.mul(x, 4));
}
{
  call Double(x, out output);
  call Double(output, out output);
};
#end

/-- Inout parameter referenced via `old` in a postcondition, exercising the
    `old_*` fresh-name path in addition to `arg_*`/out temps. -/
def InoutOldSrc :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  call f(i, inout j, k, k, l, out b);
};
#end

/-- Calls nested inside both branches of an `if`, exercising the extractor's traversal
    of nested statements, which follows the pass's `runStmtsRec` order. -/
def CallInIteSrc :=
#strata
program Core;
procedure Double(n : int, out result : int)
spec {
  ensures [double_correct]: (result == int.mul(n, 2));
}
{
  result := int.add(n, n);
};
procedure g(c : bool, x : int, out output : int) {
  if (c) {
    call Double(x, out output);
  } else {
    call Double(x, out output);
  }
};
#end

def MultiCall  : Core.Program := translate MultiCallSrc
def InoutOld   : Core.Program := translate InoutOldSrc
def CallInIte  : Core.Program := translate CallInIteSrc

---------------------------------------------------------------------
/-! ## Fresh-name agreement -/

-- The extractor records one origin per call written in the program.
/-- info: 2 -/
#guard_msgs in #eval extractorCallCount MultiCall
/-- info: 1 -/
#guard_msgs in #eval extractorCallCount InoutOld
/-- info: 2 -/
#guard_msgs in #eval extractorCallCount CallInIte

-- The names the pass generates (non-empty, so the agreement below is not vacuous).
#guard passGeneratedNames MultiCall ==
  ["tmp_arg_0", "tmp_output_1", "$__callElimAssume_double_correct_2", "tmp_arg_3", "tmp_output_4",
   "$__callElimAssume_double_correct_5"]
#guard passGeneratedNames InoutOld ==
  ["tmp_arg_0", "tmp_arg_1", "tmp_arg_2", "tmp_arg_3", "tmp_arg_4", "tmp_j_5", "tmp_b_6",
   "old_j_7", "callElimAssert_f_requires_0_8", "callElimPost_f_ensures_1_9",
   "callElimPost_f_ensures_2_10"]
#guard passGeneratedNames CallInIte ==
  ["tmp_arg_0", "tmp_output_1", "$__callElimAssume_double_correct_2", "tmp_arg_3", "tmp_output_4",
   "$__callElimAssume_double_correct_5"]

-- The extractor's fresh names are the pass's generated names, exactly and in order.
#guard extractorFreshNames MultiCall == passGeneratedNames MultiCall
#guard extractorFreshNames InoutOld == passGeneratedNames InoutOld
#guard extractorFreshNames CallInIte == passGeneratedNames CallInIte

/-- The precondition targets the extractor records: each generated `callElimAssert_*`
    label paired with the label of the callee precondition it checks (`[]` on an
    extractor error). -/
def extractorPreTargets (p : Core.Program) : List (String × String) :=
  match (runWith p callElimOrigin' CoreTransformState.emp).1 with
  | .ok origins => origins.flatMap fun o => o.preconditionTargets.map fun (l, t) => (l, t.label)
  | .error _ => []

-- The generated label is one the pass emitted (`callElimAssert_f_requires_0_8` above).
/-- info: [("callElimAssert_f_requires_0_8", "f_requires_0")] -/
#guard_msgs in #eval extractorPreTargets InoutOld
#guard extractorPreTargets MultiCall == []

/-! ## A CFG body before a structured one

The pass eliminates the call of the CFG body `C` too, so its names come first; the extractor
records no origin for it but advances the fresh counter as the pass does, so the origin of
the call in the structured `S` after it records the pass's names for that call. -/

/-- A CFG-bodied procedure with a call, then a structured one with a call. -/
def CfgThenStructuredSrc :=
#strata
program Core;

procedure Double(n : int, out result : int)
spec {
  ensures [double_correct]: (result == int.mul(n, 2));
}
{
  result := int.add(n, n);
};

procedure C(x : int, out y : int)
cfg c0 {
  c0: {
    call Double(x, out y);
    return;
  }
};

procedure S(x : int, out y : int)
{
  call Double(x, out y);
};
#end

def CfgThenStructured : Core.Program := translate CfgThenStructuredSrc

/-- info: 1 -/
#guard_msgs in #eval extractorCallCount CfgThenStructured
#guard passGeneratedNames CfgThenStructured ==
  ["tmp_arg_0", "tmp_y_1", "$__callElimAssume_double_correct_2", "tmp_arg_3", "tmp_y_4",
   "$__callElimAssume_double_correct_5"]
#guard extractorFreshNames CfgThenStructured == (passGeneratedNames CfgThenStructured).drop 3

/-! ## A program variable named like a temporary

The pass draws its temporaries with `CoreGenState.genAvoiding`, which skips a name of the
program: here the parameter `tmp_arg_0`, so the argument's temporary is `tmp_arg_1`. The
generator still logs the skipped draw (`passGeneratedNames`); the extractor records only the
names the pass used, so the call-elimination back-link keeps `tmp_arg_0` in a lifted store
(`RStore.dropVars`). -/

/-- A procedure whose parameter is named like the pass's first argument temporary. -/
def ClashSrc :=
#strata
program Core;

procedure Inc(n : int, out r : int)
spec {
  ensures [inc_post]: (r == int.add(n, 1));
}
{
  r := int.add(n, 1);
};

procedure P(tmp_arg_0 : int, out y : int) {
  call Inc(tmp_arg_0, out y);
  assert [a]: (tmp_arg_0 != 5);
};
#end

def Clash : Core.Program := translate ClashSrc

#guard passGeneratedNames Clash ==
  ["tmp_arg_0", "tmp_arg_1", "tmp_y_2", "$__callElimAssume_inc_post_3"]
#guard extractorFreshNames Clash == ["tmp_arg_1", "tmp_y_2", "$__callElimAssume_inc_post_3"]

/-- Whether a store binding `tmp_arg_0` and `tmp_arg_1` keeps each of them once the fresh
    variables the extractor records for `Clash` are dropped (`RStore.dropVars`). -/
def clashStoreKept : Bool × Bool :=
  match (runWith Clash callElimOrigin' CoreTransformState.emp).1 with
  | .ok origins =>
    let σ : Imperative.RStore Expression := fun (x : Expression.Ident) =>
      if x.name == "tmp_arg_0" || x.name == "tmp_arg_1" then some Imperative.HasBool.tt else none
    let σ' := Imperative.RStore.dropVars (callElimFreshVars origins) σ
    ((σ' ⟨"tmp_arg_0", ()⟩).isSome, (σ' ⟨"tmp_arg_1", ()⟩).isSome)
  | .error _ => (false, true)

-- The program's `tmp_arg_0` survives; the pass's temporary `tmp_arg_1` is dropped.
#guard clashStoreKept == (true, false)

/-! ## Per-site expansions

Call sites of different shapes (callees, arities and output targets differ) in both branches
of an `if` and in two procedures. Each recorded expansion is the pass's output at its own
site: reading every expansion of the pass's output body back as its call
(`uncallElimStmts`) gives the source body, procedure by procedure. -/

/-- Calls of different shapes in both branches of an `if`, then in a second procedure. -/
def ShapesSrc :=
#strata
program Core;

procedure Double(n : int, out result : int)
spec {
  ensures [double_correct]: (result == int.mul(n, 2));
}
{
  result := int.add(n, n);
};

procedure Split(n : int, out lo : int, out hi : int)
spec {
  ensures [split_sum]: (int.add(lo, hi) == n);
}
{
  lo := 0;
  hi := n;
};

procedure g(c : bool, x : int, out a : int, out b : int) {
  if (c) {
    call Double(x, out a);
  } else {
    call Split(x, out a, out b);
  }
};

procedure k(x : int, out y : int, out z : int) {
  call Split(x, out z, out y);
  call Double(z, out y);
};
#end

def Shapes : Core.Program := translate ShapesSrc

/-- The structured body of the procedure named `n` of `p`, `[]` if there is none. -/
def bodyOfProc (p : Core.Program) (n : String) : List Statement :=
  p.decls.findSome? (fun
    | .proc q _ => if q.header.name.name == n then
        match q.body with | .structured ss _ => some ss | _ => none
      else none
    | _ => none) |>.getD []

/-- Whether, for the procedure named `n`, the pass rewrites the body and reading its output
    body back through the extractor's origins gives the source body. -/
def roundTrips (p : Core.Program) (n : String) : Bool :=
  match (runWith p callElimOrigin' CoreTransformState.emp).1,
      (runWith p callElim' CoreTransformState.emp).1 with
  | .ok origins, .ok (_, p') =>
    !(bodyOfProc p n).isEmpty && bodyOfProc p' n != bodyOfProc p n &&
      uncallElimStmts origins 0 (bodyOfProc p' n) == bodyOfProc p n
  | _, _ => false

/-- info: 4 -/
#guard_msgs in #eval extractorCallCount Shapes
#guard roundTrips Shapes "g"
#guard roundTrips Shapes "k"
#guard extractorFreshNames Shapes == passGeneratedNames Shapes

end Strata.CallElimOriginTest
