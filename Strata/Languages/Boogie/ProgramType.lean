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

def typeCheck (T : Boogie.Expression.TyEnv) (program : Program) :
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
    let (decls, T) ← go T program.decls []
    .ok ({ decls }, T)

  where go T remaining acc : Except Format (Decls × Boogie.Expression.TyEnv) :=
  match remaining with
  | [] => .ok (acc.reverse, T)
  | decl :: drest => do
    let (decl', T) ←
      match decl with

      | .var x ty val _ =>
        let (s', T) ← Statement.typeCheck T program .none [.init x ty val .empty]
        match s' with
        | [.init x' ty' val' _] => .ok (.var x' ty' val', T)
        | _ => .error f!"Implementation error! \
                         Statement typeChecker returned the following: \
                         {Format.line}\
                         {s'}{Format.line}
                         Declaration: {decl}"

      | .type td _ =>
        match Program.find?.go .type td.name acc with
        | some decl =>
          .error f!"Type declaration of the same name already exists!\n\
                    {decl}"
        | none =>
          if td.name.snd ∈ T.knownTypes.keywords then
            .error f!"This type declaration's name is reserved!\n\
                      {td}\n\
                      KnownTypes' names:\n\
                      {T.knownTypes.keywords}"
          else match td with
          | .con tc =>
            let T := T.addKnownType { name := tc.name, arity := tc.numargs }
            .ok (.type td, T)
          | .syn ts =>
            let T ← TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } T
            .ok (.type td, T)

      | .ax a _ =>
        let (ae, T) ← LExprT.fromLExpr T a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.unresolved } , T)
        | _ => .error f!"Axiom has non-boolean type: {a}"

      | .proc proc _ =>
        let (proc', T) ← Procedure.typeCheck T program proc
        .ok (.proc proc', T)

      | .func func _ =>
        let (func', T) ← Function.typeCheck T func
        let T := T.addFactoryFunction func'
        .ok (.func func', T)

    go T drest (decl' :: acc)

---------------------------------------------------------------------

end Program
end Boogie
