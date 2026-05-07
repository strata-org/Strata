/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.CmdType
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.FunctionType
public import Strata.DL.Imperative.CmdType
import Strata.Util.Tactics

public section

namespace Core
namespace Statement

open Lambda Imperative
open Std (ToFormat Format format)
open Strata (DiagnosticModel FileRange)
---------------------------------------------------------------------

-- In a call statement, every inout parameter (which appear in both inputs and outputs of the call) must be
-- matched with a simple variable of the same name
private def areInoutArgsValid (proc : Procedure) (args : List Expression.Expr) : Bool :=
  (proc.header.inputs.toList.zip args).all fun ((paramId, _), arg) =>
    !(ListMap.keys proc.header.outputs).contains paramId ||  -- not inout, or …
    match arg with | .fvar _ id _ => id == paramId | _ => false  -- … is fvar with same name

/--
Type checker for Strata Core commands.

Note that this function needs the entire program to type-check `call`
commands by looking up the corresponding procedure's information.
-/
def typeCheckCmd (C: LContext CoreLParams) (Env : TEnv Unit) (P : Program) (c : Command) :
  Except DiagnosticModel (Command × (TEnv Unit)) := do
  match c with
  | .cmd c =>
    -- Any errors in `Imperative.Cmd.typeCheck` already include source
    -- locations.
    let (c, Env) ← Imperative.Cmd.typeCheck C Env c
    .ok (.cmd c, Env)
  | .call pname callArgs md => try
    let lhs := CallArg.getLhs callArgs
    let args := CallArg.getInputExprs callArgs
    -- `try`: to augment any errors with source location info.
     match Program.Procedure.find? P pname with
     | none => .error <| md.toDiagnosticF f!"[{c}]: Procedure {pname} not found!"
     | some proc =>
       if lhs.any (fun (l: CoreIdent) => (Env.context.types.find? l).isNone) then
         .error <| md.toDiagnosticF f!"[{c}]: All the return variables {lhs} must exist in the context!"
       else if lhs.length != proc.header.outputs.length then
         .error <| md.toDiagnosticF f!"[{c}]: Arity mismatch in this call's return values!\
                   Here is the expected signature: {proc.header.inputs}"
       else if args.length != proc.header.inputs.length then
         .error <| md.toDiagnosticF f!"[{c}]: Arity mismatch in this call's arguments!\
                   Here is the expected signature: {proc.header.inputs}"
       else if !areInoutArgsValid proc args then
         .error <| md.toDiagnosticF f!"[{c}]: In-out arguments (parameters appearing in \
                   both inputs and outputs) must be simple variable references"
       else do
         -- Get the types of lhs variables and unify with the procedures'
         -- return types.
         let lhsinsts ← Lambda.Identifier.instantiateAndSubsts lhs C Env |>.mapError DiagnosticModel.fromFormat
         match lhsinsts with
         | none => .error <| md.toDiagnosticF f!"Implementation error. \
                             Types of {lhs} should have been known."
         | some (lhs_tys, Env) =>
           let _ ← Env.freeVarChecks args |>.mapError DiagnosticModel.fromFormat
           let (ret_sig, Env) ← LMonoTySignature.instantiate C Env proc.header.typeArgs proc.header.outputs |>.mapError DiagnosticModel.fromFormat
           let ret_mtys := LMonoTys.subst Env.stateSubstInfo.subst ret_sig.values
           let ret_lhs_constraints := lhs_tys.zip ret_mtys
           -- Infer the types of the actuals and unify with the types of the
           -- procedure's formals.
           let (argsa, Env) ← Lambda.LExpr.resolves C Env args |>.mapError DiagnosticModel.fromFormat
           let args_tys := argsa.map LExpr.toLMonoTy
           let args' := argsa.map $ LExpr.unresolved
           let (inp_sig, Env) ← LMonoTySignature.instantiate C Env proc.header.typeArgs proc.header.inputs |>.mapError DiagnosticModel.fromFormat
           let inp_mtys := LMonoTys.subst Env.stateSubstInfo.subst inp_sig.values
           let lhs_inp_constraints := (args_tys.zip inp_mtys)
           let S ← Constraints.unify (lhs_inp_constraints ++ ret_lhs_constraints) Env.stateSubstInfo |> .mapError (fun e => DiagnosticModel.fromFormat (format e))
           let Env := Env.updateSubst S
           let newCallArgs := CallArg.replaceInArgs callArgs args'
           let s' := .call pname newCallArgs md
           .ok (s', Env)
      catch e =>
        -- Add source location to error messages if not already present.
        .error <| e.withRangeIfUnknown (getFileRange md |>.getD FileRange.unknown)

def typeCheckAux (C: LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss : List Statement) :
    Except DiagnosticModel
      (List Statement × TEnv Unit × LContext CoreLParams) :=
  go C Env ss [] []
where
  go (C : LContext CoreLParams) (Env : TEnv Unit) (ss : List Statement) (acc : List Statement)
    (labels : List String) :
    Except DiagnosticModel (List Statement × TEnv Unit × LContext CoreLParams) :=
    let errorWithSourceLoc := fun (e : DiagnosticModel) md =>
      e.withRangeIfUnknown (getFileRange md |>.getD FileRange.unknown)
    match ss with
    | [] => .ok (acc.reverse, Env, C)
    | s :: srest => do
      let (s', Env, C) ←
        match s with
        | .cmd cmd => do
          let (c', Env) ← typeCheckCmd C Env P cmd
          .ok (Stmt.cmd c', Env, C)

        | .block label bss md => do
          if labels.contains label then
            throw <| md.toDiagnosticF
              f!"Block label \"{label}\" shadows an enclosing block."
          let (bss', Env, C) ← goBlock C Env bss [] (label :: labels)
          let s' := Stmt.block label bss' md
          .ok (s', Env, C)

        | .ite cond tss ess md => do try
          match cond with
          | .det c =>
            let _ ← Env.freeVarCheck c f!"[{s}]" |>.mapError DiagnosticModel.fromFormat
            let (conda, Env) ← LExpr.resolve C Env c |>.mapError DiagnosticModel.fromFormat
            let condty := conda.toLMonoTy
            match condty with
            | .tcons "bool" [] =>
              let (tss, Env, C) ← goBlock C Env tss [] labels
              let (ess, Env, C) ← goBlock C Env ess [] labels
              let s' := Stmt.ite (.det conda.unresolved) tss ess md
              .ok (s', Env, C)
            | _ => .error <| md.toDiagnosticF f!"[{s}]: If's condition {c} is not of type `bool`!"
          | .nondet =>
            let (tss, Env, C) ← goBlock C Env tss [] labels
            let (ess, Env, C) ← goBlock C Env ess [] labels
            let s' := Stmt.ite .nondet tss ess md
            .ok (s', Env, C)
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .loop guard measure invariant bss md => do try
          let guardResult ← match guard with
            | .det g => do
              let _ ← Env.freeVarCheck g f!"[{s}]" |>.mapError DiagnosticModel.fromFormat
              let (conda, Env) ← LExpr.resolve C Env g |>.mapError DiagnosticModel.fromFormat
              let condty := conda.toLMonoTy
              if condty != .tcons "bool" [] then
                throw <| md.toDiagnosticF f!"[{s}]: Loop's guard {g} is not of type `bool`!"
              pure (some conda, Env)
            | .nondet => pure (none, Env)
          let (guarda, Env) := guardResult
          let (mt, Env) ← (match measure with
          | .some m => do
            let _ ← Env.freeVarCheck m f!"[{s}]" |>.mapError DiagnosticModel.fromFormat
            let (ma, Env) ← LExpr.resolve C Env m |>.mapError DiagnosticModel.fromFormat
            .ok (some ma, Env)
          | _ => .ok (none, Env))
          let (it, Env) ← invariant.foldlM (fun (acc, E) (lbl, i) => do
            let _ ← E.freeVarCheck i f!"[{s}]" |>.mapError DiagnosticModel.fromFormat
            let (ia, E') ← LExpr.resolve C E i |>.mapError DiagnosticModel.fromFormat
            if ia.toLMonoTy == .tcons "bool" [] then
              .ok (acc ++ [(lbl, ia)], E')
            else
              .error <| md.toDiagnosticF f!"[{s}]: Loop's invariant {i} is not of type `bool`!"
          ) (([] : List (String × _)), Env)
          let mty := mt.map LExpr.toLMonoTy
          match mty with
          | none | some (.tcons "int" []) =>
            let (tb, Env, C) ← goBlock C Env bss [] labels
            let guarda' : ExprOrNondet Expression := match guarda with
              | some e => .det e.unresolved
              | none => .nondet
            let s' := Stmt.loop guarda' (mt.map LExpr.unresolved)
              (it.map (fun (lbl, e) => (lbl, e.unresolved))) tb md
            .ok (s', Env, C)
          | _ =>
            .error <| md.toDiagnosticF f!"[{s}]: Loop's measure {measure} is not of type `int`!"
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .exit label md => do try
          match op with
          | .some _ =>
            match label with
            | .none =>
              if labels.isEmpty then
                .error <| md.toDiagnosticF f!"{s}: exit occurs outside any block."
              else
                .ok (s, Env, C)
            | .some l =>
              if labels.contains l then
                .ok (s, Env, C)
              else
                .error <| md.toDiagnosticF f!"{s}: exit label \"{l}\" does not match any enclosing block."
          | .none => .error <| md.toDiagnosticF f!"{s} occurs outside a procedure."
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .funcDecl decl md => do try
          -- Recursive functions are only allowed as top-level declarations
          if decl.isRecursive then
            .error (md.toDiagnosticF f!"recursive functions are not allowed as local declarations")
          -- Type check the function declaration using the shared helper
          -- which returns both the type-checked PureFunc and the Function
          let (decl', func, Env) ← PureFunc.typeCheck C Env decl |>.mapError DiagnosticModel.fromFormat
          let C := C.addFactoryFunction func
          .ok (.funcDecl decl' md, Env, C)
          catch e =>
            .error (errorWithSourceLoc e md)

        | .typeDecl tc md => do try
          -- Add the type to the context. Shadowing is not allowed: if a
          -- type with the same name was already declared (at the program
          -- level or in an enclosing scope), this will return an error.
          let C ← C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs }
            (md.toDiagnosticF f!"Type '{tc.name}' is already declared")
          .ok (.typeDecl tc md, Env, C)
          catch e =>
            .error (errorWithSourceLoc e md)

      go C Env srest (s' :: acc) labels
  goBlock (C : LContext CoreLParams) (Env : TEnv Unit) (bss : Imperative.Block Core.Expression Core.Command) (acc : List Statement)
    (labels : List String) :
    Except DiagnosticModel (List Statement × TEnv Unit × LContext CoreLParams) := do
    let Env := Env.pushEmptyContext
    let (ss', Env, C) ← go C Env bss acc labels
    .ok (ss', Env.popContext, C)

private def substOptionExpr (S : Subst) (oe : Option Expression.Expr) : Option Expression.Expr :=
  match oe with
  | some e => some (LExpr.applySubst e S)
  | none => none

private def substExprOrNondet (S : Subst) (e : Imperative.ExprOrNondet Expression) : Imperative.ExprOrNondet Expression :=
  e.map (LExpr.applySubst · S)

/--
Apply type substitution `S` to a command.
-/
def Command.subst (S : Subst) (c : Command) : Command :=
  match c with
  | .cmd c => match c with
    | .init x ty e md =>
      .cmd $ .init x (LTy.subst S ty) (substExprOrNondet S e) md
    | .set x e md =>
      .cmd $ .set x (substExprOrNondet S e) md
    | .assert label b md =>
      .cmd $ .assert label (b.applySubst S) md
    | .assume label b md =>
      .cmd $ .assume label (b.applySubst S) md
    | .cover label b md =>
      .cmd $ .cover label (b.applySubst S) md
  | .call pname callArgs md =>
    .call pname (callArgs.map fun
      | .inArg e => .inArg (e.applySubst S)
      | .inoutArg id => .inoutArg id
      | .outArg id => .outArg id) md

/--
Apply type substitution `S` to a statement.

Note: This substitutes type variables in types, not term variables. For
`funcDecl`, the input identifiers (term-level names like `x`, `y`) are
unchanged; only the types of those inputs are substituted. There is no
name collision concern between type variables in `S` and term-level
input identifiers.
-/
def Statement.subst (S : Subst) (s : Statement) : Statement :=
  match s with
  | .cmd cmd => .cmd (Command.subst S cmd)
  | .block label bss md =>
    .block label (go S bss []) md
  | .ite cond tss ess md =>
    .ite (cond.map (LExpr.applySubst · S)) (go S tss []) (go S ess []) md
  | .loop guard m i bss md =>
    .loop (guard.map (LExpr.applySubst · S)) (substOptionExpr S m)
      (i.map (fun (l, e) => (l, e.applySubst S))) (go S bss []) md
  | .exit _ _ => s
  | .funcDecl decl md =>
    let decl' := { decl with
      inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.subst S ty)),
      output := Lambda.LTy.subst S decl.output,
      body := decl.body.map (·.applySubst S),
      axioms := decl.axioms.map (·.applySubst S) }
    .funcDecl decl' md
  | .typeDecl _ _ => s  -- Type declarations don't contain type variables to substitute
  where
    go S ss acc : List Statement :=
    match ss with
    | [] => acc.reverse
    | s :: srest => go S srest ((Statement.subst S s) :: acc)

/--
Type checker and annotater for Statements.

Note that this function needs the entire program to type-check statements to
check whether `exit` statements occur inside a procedure (or .none for statements that don't occur
inside a procedure).
-/
def typeCheck (C: Expression.TyContext) (Env : Expression.TyEnv) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except DiagnosticModel (List Statement × Expression.TyEnv) := do
  let (ss', Env, _C) ← typeCheckAux C Env P op ss
  let context := TContext.subst Env.context Env.stateSubstInfo.subst
  let Env := Env.updateContext context
  let ss' := Statement.subst.go Env.stateSubstInfo.subst ss' []
  .ok (ss', Env)

---------------------------------------------------------------------

end Statement
end Core

end -- public section
