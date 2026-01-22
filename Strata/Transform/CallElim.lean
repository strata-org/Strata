/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CoreTransform

/-! # Call Elimination Transformation -/

namespace Core
namespace CallElim

open Core.Transform

/--
The main call elimination transformation algorithm on a single command.
The returned result is a sequence of statements
-/
def callElimCmd (cmd: Command) (p : Program)
  : CoreTransformM (List Statement) := do
    match cmd with
      | .call lhs procName args _ =>

        let some proc := Program.Procedure.find? p procName | throw s!"Procedure {procName} not found in program"

        let postconditions := OldExpressions.normalizeOldExprs $ proc.spec.postconditions.values.map Procedure.Check.expr

        -- extract old variables in all post conditions
        let oldVars := postconditions.flatMap OldExpressions.extractOldExprVars

        let oldVars := List.eraseDups oldVars

        -- filter out non-global variables
        let oldVars := oldVars.filter (isGlobalVar p)

        let genArgTrips := genArgExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs) args
        let argTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Expr)
            ← genArgTrips

        let genOutTrips := genOutExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs) lhs
        let outTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOutTrips

        -- Monadic operation, generate var mapping for each unique oldVars.
        let genOldTrips := genOldExprIdentsTrip p oldVars
        let oldTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOldTrips

        -- initialize/declare the newly generated variables
        let argInit := createInits argTrips
        let outInit := createInitVars outTrips
        let oldInit := createInitVars oldTrips

        -- construct substitutions of old variables
        let oldSubst := createOldVarsSubst oldTrips

        -- only need to substitute post conditions.
        let postconditions := OldExpressions.substsOldExprs oldSubst postconditions

        -- generate havoc for return variables, modified variables
        let havoc_ret := createHavocs lhs
        let havoc_mod := createHavocs proc.spec.modifies
        let havocs := havoc_ret ++ havoc_mod

        -- construct substitutions for argument and return
        let arg_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.inputs).zip $ createFvars argTrips.unzip.fst.unzip.fst
        let ret_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.outputs).zip $ createFvars lhs

        -- construct assumes and asserts in place of pre/post conditions
        -- generate asserts based on pre-conditions, substituting procedure arguments
        let asserts := createAsserts
                        (Procedure.Spec.getCheckExprs
                          proc.spec.preconditions)
                        (arg_subst ++ ret_subst)
        -- generate assumes based on post-conditions, substituting procedure arguments and returns
        let assumes := createAssumes postconditions
                        (arg_subst ++ ret_subst)

        return argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes
      | _ => return [ .cmd cmd ]

-- Visits top-level statements and do call elimination
def callElimStmts (ss: List Statement) (prog : Program) :=
  runStmts callElimCmd ss prog

def callElimL (dcls : List Decl) (prog : Program) :=
  runProcedures callElimCmd dcls prog

/-- Call Elimination for an entire program by walking through all procedure
bodies -/
def callElim' (p : Program) : CoreTransformM Program :=
  runProgram callElimCmd p

end CallElim
end Core
