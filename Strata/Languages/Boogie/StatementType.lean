/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.CmdType
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.OldExpressions
import Strata.DL.Imperative.CmdType

namespace Boogie
namespace Statement

open Lambda Imperative
open Std (ToFormat Format format)
---------------------------------------------------------------------

/--
Type checker for Boogie commands.

Note that this function needs the entire program to type-check `call`
commands by looking up the corresponding procedure's information.
-/
def typeCheckCmd (T : (TEnv BoogieIdent)) (P : Program) (c : Command) :
  Except Format (Command × (TEnv BoogieIdent)) := do
  match c with
  | .cmd c =>
    let (c, T) ← Imperative.Cmd.typeCheck T c
    .ok (.cmd c, T)
  | .call lhs pname args md =>
     match Program.Procedure.find? P pname with
     | none => .error f!"[{c}]: Procedure {pname} not found!"
     | some proc =>
       if lhs.any (fun l => (T.context.types.find? l).isNone) then
         .error f!"[{c}]: All the return variables {lhs} must exist in the context!"
       else if lhs.length != proc.header.outputs.length then
         .error f!"[{c}]: Arity mismatch in this call's return values!\
                   Here is the expected signature: {proc.header.inputs}"
       else if args.length != proc.header.inputs.length then
         .error f!"[{c}]: Arity mismatch in this call's arguments!\
                   Here is the expected signature: {proc.header.inputs}"
       else do
         -- Get the types of lhs variables and unify with the procedures'
         -- return types.
         let lhsinsts ← Lambda.Identifier.instantiateAndSubsts lhs T
         match lhsinsts with
         | none => .error f!"Implementation error. \
                             Types of {lhs} should have been known."
         | some (lhs_tys, T) =>
           let _ ← T.freeVarChecks args
           let (ret_sig, T) ← LMonoTySignature.instantiate T proc.header.typeArgs proc.header.outputs
           let ret_mtys := LMonoTys.subst T.state.substInfo.subst ret_sig.values
           let ret_lhs_constraints := lhs_tys.zip ret_mtys
           -- Infer the types of the actuals and unify with the types of the
           -- procedure's formals.
           let (argsa, T) ← Lambda.LExprT.fromLExprs T args
           let args_tys := argsa.map LExprT.toLMonoTy
           let args' := argsa.map $ LExprT.toLExpr
           let (inp_sig, T) ← LMonoTySignature.instantiate T proc.header.typeArgs proc.header.inputs
           let inp_mtys := LMonoTys.subst T.state.substInfo.subst inp_sig.values
           let lhs_inp_constraints := (args_tys.zip inp_mtys)
           let S ← Constraints.unify (lhs_inp_constraints ++ ret_lhs_constraints) T.state.substInfo
           let T := T.updateSubst S
           let s' := .call lhs pname args' md
           .ok (s', T)


def typeCheckAux (T : (TEnv BoogieIdent)) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except Format (List Statement × (TEnv BoogieIdent)) :=
  go T ss []
where
  go (T : TEnv BoogieIdent) (ss : List Statement) (acc : List Statement) :
    Except Format (List Statement × (TEnv BoogieIdent)) :=
    match ss with
    | [] => .ok (acc.reverse, T)
    | s :: srest => do
      let (s', T) ←
        match s with
        | .cmd cmd => do
          let (c', T) ← typeCheckCmd T P cmd
          .ok (.cmd c', T)

        | .block label blk md => do
          let T := T.pushEmptyContext
          let (ss', T) ← go T blk.ss []
          let s' := .block label ⟨ss'⟩ md
          .ok (s', T.popContext)

        | .ite cond thenb elseb md => do
          let _ ← T.freeVarCheck cond f!"[{s}]"
          let (conda, T) ← LExprT.fromLExpr T cond
          let condty := conda.toLMonoTy
          match condty with
          | .tcons "bool" [] =>
            let (tb, T) ← go T [(.block "$$_then" thenb #[])] []
            let (eb, T) ← go T [(.block "$$_else" elseb #[])] []
            let s' := .ite conda.toLExpr ⟨tb⟩ ⟨eb⟩ md
            .ok (s', T)
          | _ => .error f!"[{s}]: If's condition {cond} is not of type `bool`!"

        | .loop guard measure invariant body md => do
          let _ ← T.freeVarCheck guard f!"[{s}]"
          let (conda, T) ← LExprT.fromLExpr T guard
          let condty := conda.toLMonoTy
          let (mty, T) ← match measure with
          | .some m => do
            let _ ← T.freeVarCheck m f!"[{s}]"
            let (ma, T) ← LExprT.fromLExpr T m
            .ok ((some ma.toLMonoTy), T)
          | _ => .ok (none, T)
          let (ity, T) ← match invariant with
          | .some i => do
            let _ ← T.freeVarCheck i f!"[{s}]"
            let (ia, T) ← LExprT.fromLExpr T i
            .ok ((some ia.toLMonoTy), T)
          | _ => .ok (none, T)
          match (condty, mty, ity) with
          | (.tcons "bool" [], none, none)
          | (.tcons "bool" [], some (.tcons "int" []), none)
          | (.tcons "bool" [], none, some (.tcons "bool" []))
          | (.tcons "bool" [], some (.tcons "int" []), some (.tcons "bool" [])) =>
            let (tb, T) ← go T [(.block "$$_loop_body" body #[])] []
            let s' := .loop conda.toLExpr measure invariant ⟨tb⟩ md
            .ok (s', T)
          | _ =>
            match condty with
            | .tcons "bool" [] =>
              match mty with
              | none | .some (.tcons "int" []) =>
                match ity with
                | none | .some (.tcons "bool" []) => panic! "Internal error. condty, mty or ity must be unexpected."
                | _ => .error f!"[{s}]: Loop's invariant {invariant} is not of type `bool`!"
              | _ => .error f!"[{s}]: Loop's measure {measure} is not of type `int`!"
            | _ =>  .error f!"[{s}]: Loop's guard {guard} is not of type `bool`!"

        | .goto label _ =>
          match op with
          | .some p =>
            if Stmts.hasLabelInside label p.body then
              .ok (s, T)
            else
              .error f!"Label {label} does not exist in the body of {p.header.name}"
          | .none => .error f!"{s} occurs outside a procedure."

      go T srest (s' :: acc)
    termination_by Stmts.sizeOf ss
    decreasing_by
    all_goals simp_wf <;> omega

/--
Apply type substitution `S` to a command.
-/
def Command.subst (S : Subst) (c : Command) : Command :=
  match c with
  | .cmd c => match c with
    | .init x ty e md =>
      .cmd $ .init x (LTy.subst S ty) (e.applySubst S) md
    | .set x e md =>
      .cmd $ .set x (e.applySubst S) md
    | .havoc _ _ => .cmd $ c
    | .assert label b md =>
      .cmd $ .assert label (b.applySubst S) md
    | .assume label b md =>
      .cmd $ .assume label (b.applySubst S) md
  | .call lhs pname args md =>
    .call lhs pname (args.map (fun a => a.applySubst S)) md

private def substOptionExpr (S : Subst) (oe : Option Expression.Expr) : Option Expression.Expr :=
  match oe with
  | some e => some (LExpr.applySubst e S)
  | none => none

/--
Apply type substitution `S` to a statement.
-/
def Statement.subst (S : Subst) (s : Statement) : Statement :=
  match s with
  | .cmd cmd => .cmd (Command.subst S cmd)
  | .block label b md =>
    .block label ⟨go S b.ss []⟩ md
  | .ite cond thenb elseb md =>
    .ite (cond.applySubst S) ⟨go S thenb.ss []⟩ ⟨go S elseb.ss []⟩ md
  | .loop guard m i body md =>
    .loop (guard.applySubst S) (substOptionExpr S m) (substOptionExpr S i) ⟨go S body.ss []⟩ md
  | .goto _ _ => s
  termination_by (Stmt.sizeOf s)
  decreasing_by
    all_goals simp_wf <;> omega
  where
    go S ss acc : List Statement :=
    match ss with
    | [] => acc.reverse
    | s :: srest => go S srest ((Statement.subst S s) :: acc)
    termination_by (Stmts.sizeOf ss)
    decreasing_by
      all_goals simp_wf <;> omega

/--
Type checker and annotater for Statements.

Note that this function needs the entire program to type-check statements to
check whether `goto` targets exist (or .none for statements that don't occur
inside a procedure).
-/
def typeCheck (T : Expression.TyEnv) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except Format (List Statement × Expression.TyEnv) := do
  let (ss', T) ← typeCheckAux T P op ss
  let context := TContext.subst T.context T.state.substInfo.subst
  let T := { T with context := context }
  let ss' := Statement.subst.go T.state.substInfo.subst ss' []
  .ok (ss', T)

---------------------------------------------------------------------
end Statement
end Boogie
