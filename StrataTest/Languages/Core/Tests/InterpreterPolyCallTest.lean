/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.InterpreterEval

/-! # Behavioral tests of a call to a polymorphic procedure

The callee `Id<a>(x : a) returns (y : a)` declares a local `t : a`.  A call runs the callee
instantiated at its type arguments (`Procedure.instantiateTypes`), so the local's declared type is
`int` at `Id<int>` and the `init` accepts the integer it is given.  A call that does not
instantiate the callee (no type arguments, or the wrong number) stops with
`programCallTypeArgsMismatch`. -/

meta section

namespace InterpreterPolyCallTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst default n
private def md : MetaData Expression := #[]
private def tvA : LMonoTy := .ftvar "a"

/-- `Id<a>(x : a) returns (y : a) { var t : a := x; y := t; }`. -/
private def idProc : Procedure :=
  { header := { name := id "Id", typeArgs := ["a"], inputs := [(id "x", tvA)],
                outputs := [(id "y", tvA)] },
    spec := default,
    body := .structured
      [.cmd (.cmd (.init (id "t") (.forAll [] tvA) (.det (.fvar default (id "x") (some tvA))) md)),
       .cmd (.cmd (.set (id "y") (.det (.fvar default (id "t") (some tvA))) md))] false }

private def π : String → Option Procedure := fun n => if n = "Id" then some idProc else none

/-- Caller env with `z` predefined to `0`. -/
private def env0 : Imperative.IEnv Expression :=
  .ofStore (fun n => if n == id "z" then some (int 0) else none) Core.Factory

/-- `call z := Id<tyArgs>(5)`. -/
private def callId (tyArgs : Option (List Expression.Ty)) : Statement :=
  .cmd (CmdExt.call "Id" tyArgs [.inArg (int 5), .outArg (id "z")] md)

/-- The stop reason of a run of `[callId tyArgs]`, if it stops. -/
private def stopOf (tyArgs : Option (List Expression.Ty)) : Option StopReason :=
  match runCoreEval π 100 (.stmts [callId tyArgs] env0) with
  | (.error (.stuck r), _) => some r
  | _ => none

-- The instance at `int` has no type parameters and `int` in place of `a`.
#guard (idProc.instantiateTypes [.forAll [] .int]).map (fun p => (p.header.typeArgs, p.header.inputs,
  p.header.outputs)) == some ([], [(id "x", .int)], [(id "y", .int)])
-- Wrong arity and non-monotype arguments instantiate nothing.
#guard (idProc.instantiateTypes []).isNone
#guard (idProc.instantiateTypes [.forAll [] .int, .forAll [] .bool]).isNone
#guard (idProc.instantiateTypes [.forAll ["b"] (.ftvar "b")]).isNone
/-- `Cap<a>(x : a) returns (y : a) { var f : ∀b. a → b; }`, which declares a variable at a
    quantified type. -/
private def capProc : Procedure :=
  { idProc with
    body := .structured
      [.cmd (.cmd (.init (id "f") (.forAll ["b"] (.arrow tvA (.ftvar "b"))) .nondet md))] false }
-- `Cap` has no instance: substituting under the binder could capture a type variable of the
-- type arguments (here `b`).
#guard !capProc.initTypesMono
#guard (capProc.instantiateTypes [.forAll [] (.ftvar "b")]).isNone
#guard idProc.initTypesMono

-- `Id<int>(5)` runs the instance: `z` becomes `5`.
#guard ((runCoreEvalStore π 100 (.stmts [callId (some [.forAll [] .int])] env0)).bind
  (· (id "z"))) == some (int 5)
#guard stopOf (some [.forAll [] .int]) == none

-- Without type arguments, or with the wrong number of them, the call has no callee to run.
#guard stopOf none == some (.programCallTypeArgsMismatch "Id")
#guard stopOf (some []) == some (.programCallTypeArgsMismatch "Id")

-- At the wrong type the callee runs, and its `init t : bool := x` rejects the integer `5`.
#guard stopOf (some [.forAll [] .bool]) == some .illTypedValue

end InterpreterPolyCallTest

end
