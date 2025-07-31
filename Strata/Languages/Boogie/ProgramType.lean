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
    let (decls, T) ← go T program.decls
    .ok ({ decls }, T)
  where go T decls : Except Format (Decls × Boogie.Expression.TyEnv) :=
  match decls with
  | [] => .ok ([], T)
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
        match td with
        | .con tc =>
          let ty := tc.toType
          let T := T.addKnownType ty
          .ok (.type td, T)
        | .syn ts =>
          if !ts.typeArgs.Nodup then
            .error f!"[Type Synonym] Duplicates found in the type arguments!\n\
                      {decl}"
          else if !((ts.type.freeVars ⊆ ts.typeArgs) &&
                    (ts.toLHSLTy.freeVars ⊆ ts.typeArgs)) then
            .error f!"[Type Synonym] Type definition contains free type arguments!\n\
                      {decl}"
          else
            let (mtys, T) := Lambda.LMonoTys.instantiate ts.typeArgs [ts.toLHSLMonoTy, ts.type] T
            match mtys with
            | [lhs, rhs] =>
              let newTyArgs := lhs.freeVars
              -- We expect `ts.type` to be a known, legal type, hence the use of
              -- `instantiateWithCheck` below. Note that we only store type
              -- declarations -- not synonyms -- as values in the alias table;
              -- i.e., we don't store a type alias mapped to another type alias.
              let (rhsmty, _) ← (Lambda.LTy.forAll [] rhs).instantiateWithCheck T
              let new_aliases := { args := newTyArgs,
                                   lhs := lhs,
                                   rhs := rhsmty } :: T.context.aliases
              let context := { T.context with aliases := new_aliases }
              let T := { T with context := context }
              .ok (.type td, T)
            | _ => .error f!"[Type Synonym] Implementation error! \n\
                             {decl}"

      | .ax a _ =>
        let (ae, T) ← LExprT.fromLExpr T a.e
        match ae.toLMonoTy with
        | .bool => .ok (.ax { a with e := ae.toLExpr } , T)
        | _ => .error f!"Axiom has non-boolean type: {a}"

      | .proc proc _ =>
        let (proc', T) ← Procedure.typeCheck T program proc
        .ok (.proc proc', T)

      | .func func _ =>
        let (func', T) ← Function.typeCheck T func
        let T := T.addFactoryFunction func'
        .ok (.func func', T)

    let (drest', T) ← go T drest
    .ok ((decl' :: drest'), T)

---------------------------------------------------------------------

end Program
end Boogie
