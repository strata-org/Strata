/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement
import Strata.Languages.Core.Program

/-!
# Precondition Assert Transformation

For each procedure call, insert `assert` statements for the callee's
preconditions (with formals substituted by actuals) before the call.

This runs **before** type checking so that the inserted assertions get
their type variables instantiated by the type checker, avoiding
polymorphic VCs in the SMT encoding.

The evaluator does not generate precondition proof obligations for calls,
since they are already present as assertions.
-/

namespace Core
namespace PreconditionAssert

open Lambda

/--
Given a procedure's preconditions and the formal→actual substitution,
produce a list of `assert` statements.
-/
private def mkPrecondAsserts
    (proc : Procedure) (args : List Expression.Expr) : List Statement :=
  let subst := proc.header.inputs.keys.zip args
  proc.spec.preconditions.flatMap fun (label, check) =>
    let label' := s!"(Origin_{proc.header.name.name}_Requires){label}"
    match check.attr with
    | .Free =>
      dbg_trace f!"{Std.Format.line}Obligation {label'} is free!{Std.Format.line}"
      []
    | .Default =>
      let expr := LExpr.substFvars check.expr subst
      [Statement.assert label' expr check.md]

mutual

/--
Transform a single statement: if it is a call, prepend precondition asserts.
-/
private def transformStmt (p : Program) (s : Statement) : List Statement :=
  match s with
  | .cmd (.call lhs pname args md) =>
    match Program.Procedure.find? p pname with
    | some proc => mkPrecondAsserts proc args ++ [.cmd (.call lhs pname args md)]
    | none => [s]
  | .block label bss md =>
    [.block label (transformStmts p bss) md]
  | .ite cond tss ess md =>
    [.ite cond (transformStmts p tss) (transformStmts p ess) md]
  | .loop guard measure invariant bss md =>
    [.loop guard measure invariant (transformStmts p bss) md]
  | _ => [s]
  termination_by s.sizeOf

private def transformStmts (p : Program) (ss : List Statement) : List Statement :=
  ss.flatMap (transformStmt p)
  termination_by Imperative.Block.sizeOf ss
  decreasing_by apply Imperative.sizeOf_stmt_in_block; assumption
end

/--
Run the precondition-assert transformation on an entire program.
-/
def run (p : Program) : Program :=
  let decls := p.decls.map fun d =>
    match d with
    | .proc proc md =>
      .proc { proc with body := transformStmts p proc.body } md
    | other => other
  { decls }

end PreconditionAssert
end Core
