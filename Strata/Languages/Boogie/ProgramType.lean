/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExprType
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.FunctionType
import Strata.Languages.Boogie.ProcedureType

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Lambda


namespace Program

def typeCheck (C: Boogie.Expression.TyContext) (Env : Boogie.Expression.TyEnv) (program : Program) :
  Except Format (Program × Boogie.Expression.TyEnv) := do
    -- Push a type substitution scope to store global type variables.
    let Env := Env.updateSubst { subst := [[]], isWF := SubstWF_of_empty_empty }
    let (decls, Env) ← go C Env program.decls []
    .ok ({ decls }, Env)

  where go C Env remaining acc : Except Format (Decls × Boogie.Expression.TyEnv) :=
  match remaining with
  | [] => .ok (acc.reverse, Env)
  | decl :: drest => do
    let C := {C with idents := (← C.idents.addWithError decl.name f!"Error in Boogie declaration {decl}: {decl.name} already defined")}
    let (decl', C, Env) ←
      match decl with

      | .var x ty val _ =>
        let (s', Env) ← Statement.typeCheck C Env program .none [.init x ty val .empty]
        match s' with
        | [.init x' ty' val' _] => .ok (.var x' ty' val', C, Env)
        | _ => .error f!"Implementation error! \
                         Statement typeChecker returned the following: \
                         {Format.line}\
                         {s'}{Format.line}
                         Declaration: {decl}"

      | .type td _ =>
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
          | .data d =>
            let C ← C.addDatatype d
            .ok (.type td, C, Env)

      | .ax a _ =>
        let (ae, Env) ← LExpr.resolve C Env a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.unresolved }, C, Env)
        | _ => .error f!"Axiom has non-boolean type: {a}"

      | .distinct l es md =>
        let es' ← es.mapM (LExpr.resolve C Env)
        .ok (.distinct l (es'.map (λ e => e.fst.unresolved)) md, C, Env)

      | .proc proc _ =>
        let Env := Env.pushEmptySubstScope
        let (proc', Env) ← Procedure.typeCheck C Env program proc
        let Env := Env.popSubstScope
        .ok (.proc proc', C, Env)

      | .func func _ =>
        let Env := Env.pushEmptySubstScope
        let (func', Env) ← Function.typeCheck C Env func
        let C := C.addFactoryFunction func'
        let Env := Env.popSubstScope
        .ok (.func func', C, Env)

    go C Env drest (decl' :: acc)

---------------------------------------------------------------------

end Program
end Boogie
