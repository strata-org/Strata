/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Backends.CBMC.GOTO.InstToJson

import StrataTest.Backends.CBMC.ToCProverGOTO

open Std (ToFormat Format format)
-------------------------------------------------------------------------------

abbrev Boogie.ExprStr : Imperative.PureExpr :=
   { Ident := String,
     Expr := Lambda.LExpr Lambda.LMonoTy String,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv BoogieIdent,
     EvalEnv := Lambda.LState BoogieIdent
     EqIdent := instDecidableEqString }

namespace BoogieToGOTO

private def lookupType (T : Boogie.Expression.TyEnv) (i : Boogie.Expression.Ident) :
    Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => .error s!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else .error f!"Poly-type unexpected in the context for {i}: {ty}"

private def updateType (T : Boogie.Expression.TyEnv) (i : Boogie.Expression.Ident)
    (ty : Boogie.Expression.Ty) : Boogie.Expression.TyEnv :=
  T.insertInContext i ty

instance : Imperative.ToGoto Boogie.Expression where
  lookupType := lookupType
  updateType := updateType
  identToString := (fun i => i.toPretty)
  toGotoType := (fun ty => Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe)
  toGotoExpr := Lambda.LExpr.toGotoExpr

private def lookupTypeStr (T : Boogie.ExprStr.TyEnv) (i : Boogie.ExprStr.Ident) :
    Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => .error s!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else .error f!"Poly-type unexpected in the context for {i}: {ty}"

private def updateTypeStr (T : Boogie.ExprStr.TyEnv) (i : Boogie.ExprStr.Ident)
    (ty : Boogie.ExprStr.Ty) : Boogie.ExprStr.TyEnv :=
  T.insertInContext i ty

instance : Imperative.ToGoto Boogie.ExprStr where
  lookupType := lookupTypeStr
  updateType := updateTypeStr
  identToString := (fun x => x)
  toGotoType := (fun ty => Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe)
  toGotoExpr := Lambda.LExpr.toGotoExpr

open Lambda in
def substVarNames {Identifier: Type} [DecidableEq Identifier]
    (fn : Identifier → String)
    (e : LExpr LMonoTy Identifier) (frto : Map String String) : (LExpr LMonoTy String) :=
  match e with
  | .const c ty => .const c ty
  | .bvar b => .bvar b
  | .op o ty => .op (fn o) ty
  | .fvar  name ty =>
    let name_alt := frto.find? (fn name)
    .fvar (name_alt.getD (fn name)) ty
  | .mdata info e' => .mdata info (substVarNames fn e' frto)
  | .abs   ty e' => .abs ty (substVarNames fn e' frto)
  | .quant qk ty tr' e' => .quant qk ty (substVarNames fn tr' frto) (substVarNames fn e' frto)
  | .app   f e' => .app (substVarNames fn f frto) (substVarNames fn e' frto)
  | .ite   c t e' => .ite (substVarNames fn c frto) (substVarNames fn t frto) (substVarNames fn e' frto)
  | .eq    e1 e2 => .eq (substVarNames fn e1 frto) (substVarNames fn e2 frto)

def Boogie.Cmd.renameVars (frto : Map String String) (c : Imperative.Cmd Boogie.Expression)
    : Imperative.Cmd Boogie.ExprStr :=
  match c with
  | .init name ty e _ =>
    let e' := substVarNames Boogie.BoogieIdent.toPretty e frto
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .init new ty e' .empty
  | .set name e _ =>
    let e' := substVarNames Boogie.BoogieIdent.toPretty e frto
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .set new e' .empty
  | .havoc name _ =>
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .havoc new .empty
  | .assume label e _ =>
    let e' := substVarNames Boogie.BoogieIdent.toPretty e frto
    .assume label e' .empty
  | .assert label e _ =>
    let e' := substVarNames Boogie.BoogieIdent.toPretty e frto
    .assert label e' .empty

def Boogie.Cmds.renameVars (frto : Map String String)
    (cs : Imperative.Cmds Boogie.Expression) : Imperative.Cmds Boogie.ExprStr :=
  match cs with
  | [] => []
  | c :: crest => [(Boogie.Cmd.renameVars frto c)] ++ (renameVars frto crest)

open Lambda.LTy.Syntax in
def transformToGoto (boogie : Boogie.Program) : Except Format (CProverGOTO.Program) := do
  let T := { Lambda.TEnv.default with functions := Boogie.Factory, knownTypes := Boogie.KnownTypes }
  let (boogie, _T) ← Boogie.Program.typeCheck T boogie
  dbg_trace f!"[Strata.Boogie] Type Checking Succeeded!"
  let decl := boogie.decls[0]!
  match decl.getProc? with
  | none => .error f!""
  | some p =>
    let cmds := p.body.map (fun b => match b with | .cmd (.cmd c) => c | _ => .havoc "error")
    let cmds := Boogie.Cmds.renameVars [("x", "simpleAddUnsigned::x"),
                                        ("y", "simpleAddUnsigned::y"),
                                        ("z", "simpleAddUnsigned::1::z")] cmds
    let ans ← @Imperative.Cmds.toGotoTransform Boogie.ExprStr BoogieToGOTO.instToGotoExprStr T cmds (loc := 10)
    let ending_insts : Array CProverGOTO.Instruction :=
      #[{ type := .DEAD, locationNum := ans.nextLoc + 1,
          code := .dead (.symbol "simpleAddUnsigned::1::z" (.UnsignedBV 32))},
        { type := .END_FUNCTION, locationNum := ans.nextLoc + 2}]
    let insts := ans.instructions ++ ending_insts
    let _ := format f!"cmds: {cmds}"
    return { instructions := insts }

-- #eval do let ans ← transformToGoto boogie
--           return CProverGOTO.programToJson "simpleAddUnsigned" ans

open Strata in
def writeToGotoJson (fileName programName : String) (env : Program) : IO Unit := do
  let (program, errors) := TransM.run (translateProgram env)
  if errors.isEmpty then
    (match (transformToGoto program) with
      | .error _e => return ()
      | .ok ans =>
        CProverGOTO.writeProgramToFile
          fileName programName ans)
  else
    panic! s!"DDM Transform Error: {repr errors}"

end BoogieToGOTO

-------------------------------------------------------------------------------
