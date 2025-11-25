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
def typeCheckCmd (C: LContext BoogieLParams) (Env : TEnv Visibility) (P : Program) (c : Command) :
  Except Format (Command × (TEnv Visibility)) := do
  match c with
  | .cmd c =>
    let (c, Env) ← Imperative.Cmd.typeCheck C Env c
    .ok (.cmd c, Env)
  | .call lhs pname args md =>
     match Program.Procedure.find? P pname with
     | none => .error f!"[{c}]: Procedure {pname} not found!"
     | some proc =>
       if lhs.any (fun (l: BoogieIdent) => (Env.context.types.find? l).isNone) then
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
         let lhsinsts ← Lambda.Identifier.instantiateAndSubsts lhs C Env
         match lhsinsts with
         | none => .error f!"Implementation error. \
                             Types of {lhs} should have been known."
         | some (lhs_tys, Env) =>
           let _ ← Env.freeVarChecks args
           let (ret_sig, Env) ← LMonoTySignature.instantiate C Env proc.header.typeArgs proc.header.outputs
           let ret_mtys := LMonoTys.subst Env.stateSubstInfo.subst ret_sig.values
           let ret_lhs_constraints := lhs_tys.zip ret_mtys
           -- Infer the types of the actuals and unify with the types of the
           -- procedure's formals.
           let (argsa, Env) ← Lambda.LExpr.resolves C Env args
           let args_tys := argsa.map LExpr.toLMonoTy
           let args' := argsa.map $ LExpr.unresolved
           let (inp_sig, Env) ← LMonoTySignature.instantiate C Env proc.header.typeArgs proc.header.inputs
           let inp_mtys := LMonoTys.subst Env.stateSubstInfo.subst inp_sig.values
           let lhs_inp_constraints := (args_tys.zip inp_mtys)
           let S ← Constraints.unify (lhs_inp_constraints ++ ret_lhs_constraints) Env.stateSubstInfo
           let Env := Env.updateSubst S
           let s' := .call lhs pname args' md
           .ok (s', Env)


def typeCheckAux (C: LContext BoogieLParams) (Env : TEnv Visibility) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except Format (List Statement × TEnv Visibility) :=
  go Env ss []
where
  go (Env : TEnv Visibility) (ss : List Statement) (acc : List Statement) :
    Except Format (List Statement × TEnv Visibility) :=
    match ss with
    | [] => .ok (acc.reverse, Env)
    | s :: srest => do
      let (s', Env) ←
        match s with
        | .cmd cmd => do
          let (c', Env) ← typeCheckCmd C Env P cmd
          .ok (.cmd c', Env)

        | .block label ⟨ bss ⟩ md => do
          let Env := Env.pushEmptyContext
          let (ss', Env) ← go Env bss []
          let s' := .block label ⟨ss'⟩ md
          .ok (s', Env.popContext)

        | .ite cond ⟨ tss ⟩ ⟨ ess ⟩ md => do
          let _ ← Env.freeVarCheck cond f!"[{s}]"
          let (conda, Env) ← LExpr.resolve C Env cond
          let condty := conda.toLMonoTy
          match condty with
          | .tcons "bool" [] =>
            let (tb, Env) ← go Env [(.block "$$_then" ⟨ tss ⟩  #[])] []
            let (eb, Env) ← go Env [(.block "$$_else" ⟨ ess ⟩  #[])] []
            let s' := .ite conda.unresolved ⟨tb⟩ ⟨eb⟩ md
            .ok (s', Env)
          | _ => .error f!"[{s}]: If's condition {cond} is not of type `bool`!"

        | .loop guard measure invariant ⟨ bss ⟩ md => do
          let _ ← Env.freeVarCheck guard f!"[{s}]"
          let (conda, Env) ← LExpr.resolve C Env guard
          let condty := conda.toLMonoTy
          let (mt, Env) ← match measure with
          | .some m => do
            let _ ← Env.freeVarCheck m f!"[{s}]"
            let (ma, Env) ← LExpr.resolve C Env m
            .ok (some ma, Env)
          | _ => .ok (none, Env)
          let (it, Env) ← match invariant with
          | .some i => do
            let _ ← Env.freeVarCheck i f!"[{s}]"
            let (ia, Env) ← LExpr.resolve C Env i
            .ok (some ia, Env)
          | _ => .ok (none, Env)
          let mty := mt.map LExpr.toLMonoTy
          let ity := it.map LExpr.toLMonoTy
          match (condty, mty, ity) with
          | (.tcons "bool" [], none, none)
          | (.tcons "bool" [], some (.tcons "int" []), none)
          | (.tcons "bool" [], none, some (.tcons "bool" []))
          | (.tcons "bool" [], some (.tcons "int" []), some (.tcons "bool" [])) =>
            let (tb, Env) ← go Env [(.block "$$_loop_body" ⟨bss⟩ #[])] []
            let s' := .loop conda.unresolved (mt.map LExpr.unresolved) (it.map LExpr.unresolved) ⟨tb⟩ md
            .ok (s', Env)
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
              .ok (s, Env)
            else
              .error f!"Label {label} does not exist in the body of {p.header.name}"
          | .none => .error f!"{s} occurs outside a procedure."

      go Env srest (s' :: acc)
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
  | .block label ⟨ bss ⟩ md =>
    .block label ⟨go S bss []⟩ md
  | .ite cond ⟨ tss ⟩ ⟨ ess ⟩ md =>
    .ite (cond.applySubst S) ⟨go S tss []⟩ ⟨go S ess []⟩ md
  | .loop guard m i ⟨ bss ⟩ md =>
    .loop (guard.applySubst S) (substOptionExpr S m) (substOptionExpr S i) ⟨go S bss []⟩ md
  | .goto _ _ => s
  where
    go S ss acc : List Statement :=
    match ss with
    | [] => acc.reverse
    | s :: srest => go S srest ((Statement.subst S s) :: acc)

/--
Type checker and annotater for Statements.

Note that this function needs the entire program to type-check statements to
check whether `goto` targets exist (or .none for statements that don't occur
inside a procedure).
-/
def typeCheck (C: Expression.TyContext) (Env : Expression.TyEnv) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except Format (List Statement × Expression.TyEnv) := do
  let (ss', Env) ← typeCheckAux C Env P op ss
  let context := TContext.subst Env.context Env.stateSubstInfo.subst
  let Env := Env.updateContext context
  let ss' := Statement.subst.go Env.stateSubstInfo.subst ss' []
  .ok (ss', Env)

---------------------------------------------------------------------
end Statement
end Boogie
