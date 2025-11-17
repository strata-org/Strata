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

<<<<<<< HEAD
def typeCheck (Env : Boogie.Expression.TyEnv) (program : Program) :
  Except Format (Program × Boogie.Expression.TyEnv) := do
  -- Check for duplicates in declaration names.
  let varNames  := program.getNames  .var
  let procNames := program.getNames .proc
  let funcNames := program.getNames .func
  if !varNames.Nodup then
    .error f!"Duplicate name(s) found for global variables! \
              List of global variables:{Format.line}\
              {varNames}"
  else if !procNames.Nodup then
    .error f!"Duplicate name(s) found for procedures! \
              List of procedure names:{Format.line}\
              {procNames}"
  else if !funcNames.Nodup then
    .error f!"Duplicate name(s) found for functions! \
              List of function names:{Format.line}\
              {funcNames}"
  else
    let (decls, Env) ← go Env program.decls []
    .ok ({ decls }, Env)

  where go Env remaining acc : Except Format (Decls × Boogie.Expression.TyEnv) :=
=======
def typeCheck (C: Boogie.Expression.TyContext) (T : Boogie.Expression.TyEnv) (program : Program) :
  Except Format (Program × Boogie.Expression.TyEnv) := do
    -- Push a type substitution scope to store global type variables.
    let T := T.updateSubst { subst := [[]], isWF := SubstWF_of_empty_empty }
    let (decls, T) ← go C T program.decls []
    .ok ({ decls }, T)

  where go C T remaining acc : Except Format (Decls × Boogie.Expression.TyEnv) :=
>>>>>>> origin/main
  match remaining with
  | [] => .ok (acc.reverse, Env)
  | decl :: drest => do
<<<<<<< HEAD
    let (decl', Env) ←
      match decl with

      | .var x ty val _ =>
        let (s', Env) ← Statement.typeCheck Env program .none [.init x ty val .empty]
        match s' with
        | [.init x' ty' val' _] => .ok (.var x' ty' val', Env)
=======
    let C := {C with idents := (← C.idents.addWithError decl.name f!"Error in Boogie declaration {decl}: {decl.name} already defined")}
    let (decl', C, T) ←
      match decl with

      | .var x ty val _ =>
        let (s', T) ← Statement.typeCheck C T program .none [.init x ty val .empty]
        match s' with
        | [.init x' ty' val' _] => .ok (.var x' ty' val', C, T)
>>>>>>> origin/main
        | _ => .error f!"Implementation error! \
                         Statement typeChecker returned the following: \
                         {Format.line}\
                         {s'}{Format.line}
                         Declaration: {decl}"

      | .type td _ =>
<<<<<<< HEAD
        match Program.find?.go .type td.name acc with
        | some decl =>
          .error f!"Type declaration of the same name already exists!\n\
                    {decl}"
        | none =>
          if td.name.snd ∈ Env.knownTypes.keywords then
            .error f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {Env.knownTypes.keywords}"
          else match td with
          | .con tc =>
            let Env := Env.addKnownType { name := tc.name, arity := tc.numargs }
            .ok (.type td, Env)
          | .syn ts =>
            let Env ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } Env
            .ok (.type td, Env)

      | .ax a _ =>
        let (ae, Env) ← LExpr.fromLExpr Env a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.unresolved } , Env)
=======
          match td with
          | .con tc =>
            let C ← C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {C.knownTypes.keywords}"
            .ok (.type td, C, T)
          | .syn ts =>
            let T ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C T
            .ok (.type td, C, T)

      | .ax a _ =>
        let (ae, T) ← LExprT.fromLExpr C T a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.toLExpr }, C, T)
>>>>>>> origin/main
        | _ => .error f!"Axiom has non-boolean type: {a}"

      | .distinct l es md =>
        let es' ← es.mapM (LExprT.fromLExpr C T)
        .ok (.distinct l (es'.map (λ e => e.fst.toLExpr)) md, C, T)

      | .proc proc _ =>
<<<<<<< HEAD
        let (proc', Env) ← Procedure.typeCheck Env program proc
        .ok (.proc proc', Env)

      | .func func _ =>
        let (func', Env) ← Function.typeCheck Env func
        let Env := Env.addFactoryFunction func'
        .ok (.func func', Env)

    go Env drest (decl' :: acc)
=======
        let T := T.pushEmptySubstScope
        let (proc', T) ← Procedure.typeCheck C T program proc
        let T := T.popSubstScope
        .ok (.proc proc', C, T)

      | .func func _ =>
        let T := T.pushEmptySubstScope
        let (func', T) ← Function.typeCheck C T func
        let C := C.addFactoryFunction func'
        let T := T.popSubstScope
        .ok (.func func', C, T)

    go C T drest (decl' :: acc)
>>>>>>> origin/main

---------------------------------------------------------------------

end Program
end Boogie
