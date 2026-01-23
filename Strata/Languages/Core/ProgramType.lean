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


namespace Program

def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (program : Program) :
  Except Format (Program × Core.Expression.TyEnv) := do
    -- Push a type substitution scope to store global type variables.
    let Env := Env.updateSubst { subst := [[]], isWF := SubstWF_of_empty_empty }
    let (decls, Env) ← go C Env program.decls []
    .ok ({ decls }, Env)

  where go C Env remaining acc : Except Format (Decls × Core.Expression.TyEnv) :=
  match remaining with
  | [] => .ok (acc.reverse, Env)
  | decl :: drest => do
    let sourceLoc := Imperative.MetaData.formatFileRangeD decl.metadata (includeEnd? := true)
    let errorWithSourceLoc := fun e => if sourceLoc.isEmpty then e else f!"{sourceLoc} {e}"
    -- Add all names from the declaration (multiple for mutual datatypes)
    let idents ← C.idents.addListWithError decl.names (fun n =>
      f!"{sourceLoc} Error in {decl.kind} {n}: a declaration of this name already exists."
    )
    let C := {C with idents}
    let (decl', C, Env) ←
      match decl with

      | .var x ty val md =>
        let (s', Env) ← Statement.typeCheck C Env program .none [.init x ty val md]
        match s' with
        | [.init x' ty' val' _] => .ok (.var x' ty' val', C, Env)
        | _ => .error f!"{sourceLoc}Implementation error! \
                         Statement typeChecker returned the following: \
                         {Format.line}\
                         {s'}{Format.line}
                         Declaration: {decl}"

      | .type td _ => try
          match td with
          | .con tc =>
            let C ← C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {C.knownTypes.keywords}"
            .ok (.type td, C, Env)
          | .syn ts =>
            let Env ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C Env
            .ok (.type td, C, Env)
          | .data block =>
            let (block, Env) := MutualDatatype.resolveAliases block Env
            let C ← C.addMutualBlock block
            .ok (.type (.data block), C, Env)
          catch e =>
            .error (errorWithSourceLoc e)

      | .ax a _ => try
        let (ae, Env) ← LExpr.resolve C Env a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.unresolved }, C, Env)
        | _ => .error f!"Axiom {a.name} has non-boolean type."
          catch e =>
            .error (errorWithSourceLoc e)

      | .distinct l es md => try
        let es' ← es.mapM (LExpr.resolve C Env)
        .ok (.distinct l (es'.map (λ e => e.fst.unresolved)) md, C, Env)
        catch e =>
          .error (errorWithSourceLoc e)

      | .proc proc md =>
        -- Already reports source locations.
        let Env := Env.pushEmptySubstScope
        let (proc', Env) ← Procedure.typeCheck C Env program proc md
        let Env := Env.popSubstScope
        .ok (.proc proc', C, Env)

      | .func func _ => try
        let Env := Env.pushEmptySubstScope
        let (func', Env) ← Function.typeCheck C Env func
        let C := C.addFactoryFunction func'
        let Env := Env.popSubstScope
        .ok (.func func', C, Env)
          catch e =>
            .error (errorWithSourceLoc e)

    go C Env drest (decl' :: acc)

---------------------------------------------------------------------

end Program
end Core
