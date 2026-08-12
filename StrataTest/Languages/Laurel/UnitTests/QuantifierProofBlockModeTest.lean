/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that `TransparencyPass` emits the quantifier proof block only in the
verification modes.

A quantifier whose body carries assert/assume steps is preceded by a proof block:

  var $proof_0: bool;
  if $proof_0 then { var $havoc_0: int; <body[x := $havoc_0]>; assume false };
  forall(x: int) => <goal>

That scaffolding is verification-only. The nondet `$proof_0` guard is an
uninitialized bool — meaningful to a symbolic verifier, but not to the concrete
interpreter — and the `assume false` seal has nothing to seal under execution. So
`AnalysisMode.Execute` keeps the plain `stripAssertAssume` behavior instead.

This is checked at the pass level rather than end-to-end because the interpreter
cannot evaluate a quantified `assert` at all ("condition did not reduce to bool"),
with or without a proof body, so an Execute-mode e2e test would fail for that
unrelated pre-existing reason.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.TransparencyPass
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Prepend the Laurel prelude, as `runLaurelPasses` does before resolving.

    It declares the built-in operator wrappers (`$mul`, `$ge`, …) that `*` and `>=`
    parse into, so resolution can bind them. Without it, re-resolution reports
    `'$ge' is not defined` for the operators in these test programs. -/
private def withPrelude (program : Program) : Program :=
  { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types }

/-- Run `TransparencyPass` in the given mode and print the resulting core
    procedures, so the presence or absence of proof scaffolding is visible. -/
private def printTransparency (mode : AnalysisMode) (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let resolved := resolve laurelProgram
  let uc := createFunctionsForTransparentBodies resolved.program { analysisMode := mode }
  for proc in uc.coreProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Run `TransparencyPass` in Verify mode and then re-resolve, mirroring what the
    pipeline does because `transparencyPass.needsResolves` is set. Reports whether
    the havoc variable's declaration and the quantifier's binder ended up with
    *distinct* `uniqueId`s, and whether re-resolution was clean. -/
private def printHavocVsBinderIds (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  -- The prelude is needed here (unlike in `printTransparency`, which never
  -- re-resolves): the re-resolve below has to bind the operator wrappers.
  let resolved := resolve (withPrelude laurelProgram)
  let uc := createFunctionsForTransparentBodies resolved.program { analysisMode := .Verify }
  let compositeTypes := resolved.program.types.filter
    (fun t => match t with | .Composite _ => true | _ => false)
  let (uc', _, errors) := resolveUnorderedCore uc (some resolved.model) compositeTypes
  IO.println s!"re-resolution errors: {errors.size}"
  -- Collect the binder ids of every quantifier, and the ids of every declaration.
  let mut binderIds : List Nat := []
  let mut declIds : List Nat := []
  for proc in uc'.coreProcedures do
    match proc.body with
    | .Opaque _ (some impl) _ =>
      binderIds := (foldStmtExpr (fun e acc =>
        match e.val with
        | .Quantifier _ p _ _ => match p.name.uniqueId with
          | some uid => uid :: acc
          | none => acc
        | _ => acc) [] impl)
      declIds := (foldStmtExpr (fun e acc =>
        match e.val with
        | .Var (.Declare p) => match p.name.uniqueId with
          | some uid => uid :: acc
          | none => acc
        | _ => acc) [] impl)
    | _ => pure ()
  let overlap := declIds.filter (binderIds.contains ·)
  IO.println s!"quantifier binders: {binderIds.length}, declarations: {declIds.length}"
  IO.println s!"ids shared between a declaration and a binder: {overlap.length}"

/-! ## Verify mode emits the proof block

    This is the pre-lift shape: the block still sits in the `assert`'s expression
    position, and the later lifting pass hoists its statements out (see
    `LiftExpressionAssignmentsTest.lean`). Note the block's value is the stripped
    quantifier, and no `assume forall(...)` is emitted — the proof block adds the
    body's obligations without establishing the quantifier. -/

/--
info: procedure proofProcedure()
  opaque
{
  assert {
    var $proof_0: bool;
    if $proof_0
      then {
        var $havoc_0: int;
        {
          assume $havoc_0 * $havoc_0 >= 0;
          $havoc_0 * $havoc_0 >= 0
        };
        assume false
      };
    forall(x: int) => x * x >= 0
  }
};
-/
#guard_msgs in
#eval printTransparency .Verify
#strata
program Laurel;
procedure proofProcedure()
  opaque
{
  assert forall(x: int) => { assume x * x >= 0; x * x >= 0 }
};
#end

/-! ## A body with no proof steps gets no proof block, even in Verify mode

    The rewrite is guarded on the body actually containing an `assert`/`assume`.
    A plain goal has no obligations to discharge, so scaffolding it would only add
    a nondet guard and a dead branch. -/

/--
info: procedure plainQuantifier()
  opaque
{
  assert forall(x: int) => x * x >= 0
};
-/
#guard_msgs in
#eval printTransparency .Verify
#strata
program Laurel;
procedure plainQuantifier()
  opaque
{
  assert forall(x: int) => x * x >= 0
};
#end

/-! ## Execute mode does not: the body is simply stripped -/

/--
info: procedure proofProcedure()
  opaque
{
  assert forall(x: int) => x * x >= 0
};
-/
#guard_msgs in
#eval printTransparency .Execute
#strata
program Laurel;
procedure proofProcedure()
  opaque
{
  assert forall(x: int) => { assume x * x >= 0; x * x >= 0 }
};
#end

/-! ## Nested proof blocks get distinct guard names

    A shared `$proof` would fail Core type checking with "Variable $proof of type
    bool already in context". The counter is handed out as each quantifier is
    *entered*, so the outer block takes `_0` and the one nested in its proof body
    takes `_1`. -/

/--
info: procedure nested()
  opaque
{
  assert {
    var $proof_0: bool;
    if $proof_0
      then {
        var $havoc_0: int;
        {
          assume {
            var $proof_1: bool;
            if $proof_1
              then {
                var $havoc_1: int;
                {
                  assume $havoc_0 + $havoc_1 >= $havoc_0;
                  $havoc_0 + $havoc_1 >= $havoc_0
                };
                assume false
              };
            forall(y: int) => $havoc_0 + y >= $havoc_0
          };
          $havoc_0 * $havoc_0 >= 0
        };
        assume false
      };
    forall(x: int) => x * x >= 0
  }
};
-/
#guard_msgs in
#eval printTransparency .Verify
#strata
program Laurel;
procedure nested()
  opaque
{
  assert forall(x: int) => {
    assume forall(y: int) => { assume x + y >= x; x + y >= x };
    x * x >= 0
  }
};
#end

/-! ## The havoc variable is a declaration distinct from the quantifier's binder

    The havoc `var $havoc_N: T` is a separate declaration with its own `uniqueId`,
    never an alias of the binder. Reusing the binder's `Parameter` verbatim would
    leave one id denoting two declarations — `defineName` preserves an already-set
    `uniqueId`, so re-resolution would not repair it — and passes that key on
    `uniqueId` then confuse the two; the lifting pass's read tracking
    (`liftedVarRefs`) is the concrete victim.

    The fresh `$havoc_N` name (rather than the binder's own) is what keeps the
    block lowerable: a same-named declaration would shadow an in-scope local, and
    shadowing does not survive lowering to Core. `binderShadowsLocal` in
    `Quantifiers.lean` covers that end-to-end; this test pins the id-level
    separation, which has no behavioral signature of its own — with the ids shared
    the whole verification suite still passes, so it is a latent trap for the next
    pass that keys on `uniqueId`. -/

/--
info: re-resolution errors: 0
quantifier binders: 1, declarations: 2
ids shared between a declaration and a binder: 0
-/
#guard_msgs in
#eval printHavocVsBinderIds
#strata
program Laurel;
procedure proofProcedure()
  opaque
{
  assert forall(x: int) => { assume x * x >= 0; x * x >= 0 }
};
#end

end Laurel
