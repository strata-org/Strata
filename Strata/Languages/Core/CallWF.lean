/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Pipeline.Messages
public import Strata.Util.String

/-! # Well-formed calls

Core's call rule matches a call's arguments with its callee's formals by position:
the input arguments (`in` and `inout`) with the input formals, and the result
variables (`inout` and `out`) with the output formals. A call's arguments match its
callee's signature (`WF.ArgsMatchSignature`) when the counts agree and each
argument's mode agrees with its formal's. A call is well-formed (`WF.WFcallProp`,
defined in `WF.lean`) when its callee is a declared procedure, its arguments match
the callee's signature, and its result variables are distinct.

`callError?` decides this for one call and explains the first condition that fails;
`illFormedCalls` does so for every call in a program. Each component that checks a
call does so through `callError?`, so they refuse the same calls with the same message.
`callError?_eq_none_iff` and `illFormedCalls_eq_nil_iff`, in `CallWFProps`, state
their agreement with `WF.WFcallProp`.
-/

namespace Core

open Imperative
open Strata (Message)

public section

namespace WF

/-- Whether `a`, the argument a call passes for its callee's input formal `x`,
    matches it. `outputs` are the callee's output formals and `lhs` the call's
    result variables, in order.

    * If `x` is inout, so that it is also output number `k`, then `a` must be
      `inout v`, and `v` must be result variable number `k`: the call reads `x` from
      the same variable it writes `x` back to.
    * Otherwise `a` must be an `in` argument. -/
@[expose] def inputArgMatches (outputs lhs : List Expression.Ident)
    (x : Expression.Ident) (a : CallArg Expression) : Bool :=
  match outputs.idxOf? x, a with
  | some k, .inoutArg v => lhs[k]? == some v
  | none, .inArg _ => true
  | _, _ => false

/-- Whether `r`, the argument a call passes for its callee's output formal `z`,
    matches it, given the callee's input formals `inputs`: an `inout` argument if
    `z` is inout (also an input formal), and an `out` argument otherwise. -/
@[expose] def outputArgMatches (inputs : List Expression.Ident) (z : Expression.Ident)
    (r : CallArg Expression) : Bool :=
  match r with
  | .inoutArg _ => inputs.contains z
  | .outArg _ => !inputs.contains z
  | .inArg _ => false

/-- A call's arguments match its callee `proc`'s signature: there are as many input
    arguments (`in` and `inout`) as input formals and as many result variables
    (`inout` and `out`) as output formals, and each argument matches the formal it
    lands on by position (`inputArgMatches`, `outputArgMatches`). -/
structure ArgsMatchSignature (proc : Procedure) (callArgs : List (CallArg Expression)) :
    Prop where
  inputCount : (CallArg.getInputExprs callArgs).length = proc.header.inputs.length
  resultCount : (CallArg.getLhs callArgs).length = proc.header.outputs.length
  inputsMatch : ∀ xa ∈ proc.header.inputs.keys.zip (CallArg.inputArgs callArgs),
    inputArgMatches proc.header.outputs.keys (CallArg.getLhs callArgs) xa.1 xa.2 = true
  outputsMatch : ∀ zr ∈ proc.header.outputs.keys.zip (CallArg.resultArgs callArgs),
    outputArgMatches proc.header.inputs.keys zr.1 zr.2 = true

end WF

/-- Why a call to `procName` passes one variable for two or more of its
    `out`/`inout` results, or `none` if the results are distinct. -/
private def aliasedResultsMessage? (procName : String) (args : List (CallArg Expression)) :
    Option String :=
  let lhs := CallArg.getLhs args
  (lhs.find? fun x => (lhs.filter (· == x)).length > 1).map fun x =>
    let what := if (CallArg.getInoutArgs args).contains x then
        s!"the inout argument {x.name} for more than one inout or out parameter; an \
          inout argument must not alias another result of the call"
      else
        s!"the variable {x.name} for more than one out parameter; the results of a \
          call must be distinct variables"
    s!"the call to {procName} passes {what}"

/-- The first input formal of `proc` whose argument doesn't match it
    (`WF.inputArgMatches`), described, or `none` if every one matches. -/
private def inputMismatchMessage? (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) : Option String :=
  let outputs := proc.header.outputs.keys
  let lhs := CallArg.getLhs args
  let pairs := proc.header.inputs.keys.zip (CallArg.inputArgs args)
  (pairs.find? fun xa => !WF.inputArgMatches outputs lhs xa.1 xa.2).map fun (x, a) =>
    let what := match outputs.idxOf? x, a with
      | some k, .inoutArg v =>
        let receiver := match lhs[k]? with
          | some w => s!"{w.name}"
          | none => "no variable"
        s!"inout {v.name} for {x.name}, but the result of {x.name} goes to {receiver}; \
          the inout and out arguments must follow the order of {procName}'s outputs"
      | some _, _ =>
        s!"an input value for {x.name}, which is an inout parameter and must be passed \
          as inout"
      | none, .inoutArg v => s!"inout {v.name} for {x.name}, which is not an inout parameter"
      | none, _ => s!"the wrong kind of argument for {x.name}"
    s!"the call to {procName} passes {what}"

/-- The first output formal of `proc` whose argument doesn't match it
    (`WF.outputArgMatches`), described, or `none` if every one matches. -/
private def outputMismatchMessage? (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) : Option String :=
  let inputs := proc.header.inputs.keys
  let pairs := proc.header.outputs.keys.zip (CallArg.resultArgs args)
  (pairs.find? fun zr => !WF.outputArgMatches inputs zr.1 zr.2).map fun (z, r) =>
    let what := match r with
      | .outArg w =>
        s!"out {w.name} for {z.name}, which is an inout parameter and must be passed as \
          inout"
      | .inoutArg v =>
        s!"inout {v.name} for {z.name}, which is an output-only parameter and must be \
          passed as out"
      | .inArg _ => s!"the wrong kind of argument for {z.name}"
    s!"the call to {procName} passes {what}"

/-- The number of `formals`, followed by their names, as in `2 input parameters (y, d)`. -/
private def formalsOf (formals : List Expression.Ident) (singular plural : String) :
    String :=
  let names := if formals.isEmpty then "" else
    s!" ({", ".intercalate (formals.map (·.name))})"
  s!"{countOf formals.length singular plural}{names}"

/-- Why a call to `proc` (named `procName`) with arguments `args` is not well-formed,
    or `none` if it is. -/
def callArgsError? (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) : Option String :=
  let nIn := (CallArg.getInputExprs args).length
  let nOut := (CallArg.getLhs args).length
  if nIn ≠ proc.header.inputs.length then
    some s!"the call to {procName} passes {countOf nIn "input argument" "input arguments"}, \
      but {procName} has \
      {formalsOf proc.header.inputs.keys "input parameter" "input parameters"}"
  else if nOut ≠ proc.header.outputs.length then
    some s!"the call to {procName} passes {countOf nOut "result variable" "result variables"}, \
      but {procName} has \
      {formalsOf proc.header.outputs.keys "output parameter" "output parameters"}"
  else match inputMismatchMessage? procName proc args with
    | some msg => some msg
    | none => match outputMismatchMessage? procName proc args with
      | some msg => some msg
      | none => aliasedResultsMessage? procName args

/-- Why a call to `procName` is ill-formed when no procedure of that name is
    declared. -/
def undeclaredProcedureMessage (procName : String) : String :=
  s!"no procedure named {procName} is declared"

/-- Why `call procName(args)` in `p` is not well-formed (`WF.WFcallProp`), or `none`
    if it is. A callee that `p` doesn't declare is reported first, since nothing else
    can be checked without it. -/
def callError? (p : Program) (procName : String) (args : List (CallArg Expression)) :
    Option String :=
  match Program.Procedure.find? p procName with
  | none => some (undeclaredProcedureMessage procName)
  | some proc => callArgsError? procName proc args

/-- `msg`, an explanation from `callError?`, as the text of a user error reported
    inside another message. -/
def illFormedCallText (msg : String) : String :=
  s!"Ill-formed call: {msg}"

/-- The error raised by `component`, which requires well-formed calls, on meeting a
    call that isn't, explained by `msg`. It is an internal error: a pipeline checks
    every call before `component` runs. -/
def wellFormedCallsBreach (component : String) (md : MetaData Expression) (msg : String) :
    Message :=
  md.toDiagnostic s!"{component} requires every call to be well-formed: {msg}"
    Strata.MessageKind.strataBug

/-- The ill-formed calls of `p`, each explained by `callError?` and located at the
    call, in the order of `Program.callSites`. -/
def illFormedCalls (p : Program) : List Message :=
  p.callSites.filterMap fun c =>
    (callError? p c.procName c.args).map fun msg => c.md.toDiagnostic s!"❌ {illFormedCallText msg}"

end -- public section

end Core
