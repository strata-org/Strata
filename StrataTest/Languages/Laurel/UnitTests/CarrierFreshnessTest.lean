/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
`usedNames` arm-by-arm: the carrier freshening only works if every way a
procedure can bind a name actually reaches the collision set. The e2e bait
tests (`ThrowsClause.lean`) cover the signature arms (an *output* named
`$result`); each case here binds the colliding name through one of the body
arms instead — a bare declaration, an `.Assign` declare-target, an `.Assign`
local-target, a `.Try` catch binding, a quantifier binder, and a `throwsOn`
case postcondition — so a mutation dropping any single fold arm flips exactly
one line below.

The quantifier arm is the load-bearing one: a `forall($result: int)` authored
in a case postcondition is exactly where the carrier substitution lands, so
missing it means the spliced carrier reference is captured by the quantifier
(see the e2e pin in `ThrowsClause.lean`).

The observable is the chosen carrier name: the procedures are void and
throwing, so after lowering their single output IS the carrier.
-/

meta import Strata.Languages.Laurel.EliminateExceptions

meta section

open Strata
open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := .unknown }

private def emptyModel : SemanticModel :=
  { nextId := 0, compositeCount := 0, refToDef := {} }

/-- A void throwing procedure with the given transparent body and cases. -/
private def throwingProc (body : StmtExpr)
    (throwsOn : List ThrowsOnBlock := []) : Program :=
  { staticProcedures := [
      { name := mkId "p"
        inputs := []
        outputs := []
        preconditions := []
        decreases := none
        throwsType := some (mkTy (.UserDefined (mkId "Err")))
        throwsBinding := some (mkId "e")
        throwsOn := throwsOn
        body := .Transparent ⟨body, .unknown⟩ }
    ]
    staticFields := []
    types := [] }

/-- The carrier name the lowering chose (the void procedure's only output). -/
private def carrierOf (prog : Program) : String :=
  let (lowered, _) := eliminateExceptionsTransform emptyModel prog
  match lowered.staticProcedures with
  | [p] => match p.outputs with
    | [o] => o.name.text
    | os => s!"unexpected output count: {os.length}"
  | ps => s!"unexpected procedure count: {ps.length}"

private def declareOf (name : String) : StmtExpr :=
  .Var (.Declare { name := mkId name, type := some (mkTy .TInt) })

private def block (stmts : List StmtExpr) : StmtExpr :=
  .Block (stmts.map (⟨·, .unknown⟩)) none

/--
info: empty body: $result
bare declaration: $result_1
assign declare-target: $result_1
assign local-target: $result_1
catch binding: $result_1
quantifier binder: $result_1
case postcondition declaration: $result_1
both taken: $result_2
-/
#guard_msgs in
#eval do
  IO.println s!"empty body: {carrierOf (throwingProc (block []))}"
  IO.println s!"bare declaration: {carrierOf (throwingProc (block [declareOf "$result"]))}"
  IO.println s!"assign declare-target: {carrierOf (throwingProc (block [
    .Assign [⟨.Declare { name := mkId "$result", type := some (mkTy .TInt) }, .unknown⟩]
      ⟨.LiteralInt 0, .unknown⟩]))}"
  IO.println s!"assign local-target: {carrierOf (throwingProc (block [
    .Assign [⟨.Local (mkId "$result"), .unknown⟩] ⟨.LiteralInt 0, .unknown⟩]))}"
  IO.println s!"catch binding: {carrierOf (throwingProc (block [
    .Try ⟨block [], .unknown⟩
      [{ binding := mkId "$result", predicate := none, body := ⟨block [], .unknown⟩ }]
      none]))}"
  IO.println s!"quantifier binder: {carrierOf (throwingProc (block [])
    [{ guard := ⟨.LiteralBool false, .unknown⟩
       postconditions := [{ condition := ⟨.Quantifier .Forall
         { name := mkId "$result", type := mkTy .TInt } none
         ⟨.LiteralBool true, .unknown⟩, .unknown⟩ }]
       modifies := [] }])}"
  IO.println s!"case postcondition declaration: {carrierOf (throwingProc (block [])
    [{ guard := ⟨.LiteralBool false, .unknown⟩
       postconditions := [{ condition := ⟨declareOf "$result", .unknown⟩ }]
       modifies := [] }])}"
  IO.println s!"both taken: {carrierOf (throwingProc (block [
    declareOf "$result", declareOf "$result_1"]))}"

end
