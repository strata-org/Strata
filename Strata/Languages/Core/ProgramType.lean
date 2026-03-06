/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExprType
import Strata.Languages.Core.Program
import Strata.Languages.Core.FunctionType
import Strata.Languages.Core.ProcedureType

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda
open Strata (DiagnosticModel FileRange)

namespace Factory

def typeCheck (C : Expression.TyContext) (T : Expression.TyEnv)
    : Except Format Expression.TyEnv :=
  C.functions.foldlM (fun Env func => do
    match func.body with
    | none => .ok Env
    | some body =>
      if body.freeVars.idents.all (fun k => k ∈ func.inputs.keys) then
        -- Temporarily add formals in the context.
        let Env := Env.pushEmptyContext
        let Env := Env.addInNewestContext func.inputPolyTypes
        -- Type check the body and ensure that it unifies with the return type.
        -- let (bodyty, Env) ← infer Env body
        let (body_typed, Env) ← LExpr.resolve C Env body
        let bodyty := body_typed.toLMonoTy
        let (retty, Env) ← func.outputPolyType.instantiateWithCheck C Env
        let S ← Constraints.unify [(retty, bodyty)] Env.stateSubstInfo |>.mapError format
        let Env := Env.updateSubst S
        let Env := Env.popContext
        .ok Env
      else
        .error f!"Function body contains free variables!\n\
                  {func}") T

end Factory

namespace Program

/--
Type check the program. The function assumes that all functions registered to
C are already well-typed.
-/
def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (program : Program) :
  Except DiagnosticModel (Program × Core.Expression.TyEnv) := do
    -- Push a type substitution scope to store global type variables.
    let Env := Env.updateSubst { subst := [[]], isWF := SubstWF_of_empty_empty }
    let (decls, Env) ← go C Env program.decls []
    .ok ({ decls }, Env)

  where go C Env remaining acc : Except DiagnosticModel (Decls × Core.Expression.TyEnv) :=
  match remaining with
  | [] => .ok (acc.reverse, Env)
  | decl :: drest => do
    let fileRange := Imperative.getFileRange decl.metadata |>.getD FileRange.unknown
    -- Add all names from the declaration (multiple for mutual datatypes)
    let idents ← C.idents.addListWithError decl.names (fun n =>
      (DiagnosticModel.withRange fileRange f!"Error in {decl.kind} {n}: a declaration of this name already exists."))
    let C := {C with idents}
    let (decl', C, Env) ←
      match decl with

      | .var x ty val md =>
        let (s', Env) ← Statement.typeCheck C Env program .none [Statement.init x ty val md]
        match s' with
        | [Statement.init x' ty' val' _] => .ok (Decl.var x' ty' val', C, Env)
        | _ => .error <| DiagnosticModel.withRange fileRange f!"Implementation error! \
                         Statement typeChecker returned the following: \
                         {Format.line}\
                         {s'}{Format.line}
                         Declaration: {decl}"

      | .type td _ => try
          match td with
          | .con tc =>
            let C ← C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } (DiagnosticModel.withRange fileRange f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {C.knownTypes.keywords}")
            .ok (Decl.type td, C, Env)
          | .syn ts =>
            let Env ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C Env
               |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
            .ok (.type td, C, Env)
          | .data block =>
            let (block, Env) ← MutualDatatype.resolveAliases block Env |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
            let C ← C.addMutualBlock block
            .ok (.type (.data block), C, Env)
          catch e =>
            .error (e.withRangeIfUnknown fileRange)

      | .ax a _ => try
        let (ae, Env) ← LExpr.resolve C Env a.e |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
        match ae.toLMonoTy with
        | .bool => .ok (Decl.ax { a with e := ae.unresolved }, C, Env)
        | _ => .error <| DiagnosticModel.withRange fileRange f!"Axiom {a.name} has non-boolean type."
          catch e =>
            .error (e.withRangeIfUnknown fileRange)

      | .distinct l es md => try
        let es' ← es.mapM (LExpr.resolve C Env) |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
        .ok (Decl.distinct l (es'.map (λ e => e.fst.unresolved)) md, C, Env)
        catch e =>
          .error (e.withRangeIfUnknown fileRange)

      | .proc proc md =>
        -- Already reports source locations.
        let Env := Env.pushEmptySubstScope
        let (proc', Env) ← Procedure.typeCheck C Env program proc md
        let Env := Env.popSubstScope
        .ok (Decl.proc proc', C, Env)

      | .func func _ => try
        let Env := Env.pushEmptySubstScope
        let (func', Env) ← Function.typeCheck C Env func |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
        let C := C.addFactoryFunction func'
        let Env := Env.popSubstScope
        .ok (Decl.func func', C, Env)
          catch e =>
            .error (e.withRangeIfUnknown fileRange)

    go C Env drest (decl' :: acc)

end Program
end Core
