/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Backends.CBMC.GOTO.InstToJson
import StrataTest.Backends.CBMC.ToCProverGOTO

open Std (ToFormat Format format)

/-
We map Boogie's procedures to a CProverGOTO program, which is then written to
CBMC-compatible JSON files that contain all the necessary information to
construct a GOTO binary.

Also see `mkGotoBin.sh`, where we use CBMC's `symtab2gb` to construct and
model-check a Strata-generated GOTO binary.
-/

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
  if h : boogie.decls.length = 1 then
    let decl := boogie.decls[0]'(by exact Nat.lt_of_sub_eq_succ h)
    match decl.getProc? with
    | none => .error f!"[transformToGoto] We can process only Boogie procedures at this time. \
                        Declaration encountered: {decl}"
    | some p =>
      let pname := Boogie.BoogieIdent.toPretty p.header.name
      let cmds ← p.body.mapM
        (fun b => match b with
          | .cmd (.cmd c) => return c
          | _ => .error f!"[transformToGoto] We can process Boogie commands only, not statements! \
                           Statement encountered: {b}")
      let formals := p.header.inputs.keys.map Boogie.BoogieIdent.toPretty
      -- CBMC expects formals to be in the namespace of the program.
      -- So, e.g., `x` appears as `program::x`.
      let formals_renamed := formals.map (fun f => (f, pname ++ "::" ++ f))
      let locals := (Imperative.Stmts.definedVars p.body).map Boogie.BoogieIdent.toPretty
      -- Local variables use `program::1::<var>` notation.
      -- (FIXME): Does `1` refer to the scope depth?
      let locals_renamed := locals.map (fun l => (l, pname ++ "::1::" ++ l))
      let args_renamed := formals_renamed ++ locals_renamed
      let cmds := Boogie.Cmds.renameVars args_renamed cmds
      let ans ← @Imperative.Cmds.toGotoTransform Boogie.ExprStr
                    BoogieToGOTO.instToGotoExprStr T cmds (loc := 0)
      let ending_insts : Array CProverGOTO.Instruction := #[
        -- (FIXME): Add lifetime markers.
        -- { type := .DEAD, locationNum := ans.nextLoc + 1,
        --     code := .dead (.symbol "simpleAddUnsigned::1::z" (.UnsignedBV 32))},
          { type := .END_FUNCTION, locationNum := ans.nextLoc + 1}]
      let insts := ans.instructions ++ ending_insts
      let _ := format f!"cmds: {cmds}"
      return {
        name := Boogie.BoogieIdent.toPretty p.header.name,
        parameterIdentifiers := (formals_renamed.map (fun f => f.snd)).toArray,
        instructions := insts
        }
  else
    .error f!"[transformToGoto] We can transform a single Boogie procedure to \
              GOTO at this time!"

-- #eval do let ans ← transformToGoto boogie
--           return CProverGOTO.programToJson "simpleAddUnsigned" ans

open Strata in
def printToGotoJson (programName : String) (env : Program) : IO Lean.Json := do
  let (program, errors) := TransM.run (translateProgram env)
  if errors.isEmpty then
    (match (BoogieToGOTO.transformToGoto program) with
      | .error e =>
        dbg_trace s!"{e}"
        return (Lean.Json.null)
      | .ok ans =>
        return (CProverGOTO.programToJson programName ans))
  else
    panic! s!"DDM Transform Error: {repr errors}"

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
