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

abbrev BoogieParams : Lambda.LExprParams := ⟨Unit, Boogie.Visibility⟩

abbrev Boogie.ExprStr : Imperative.PureExpr :=
   { Ident := BoogieParams.Identifier,
     Expr := Lambda.LExpr BoogieParams.mono,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv BoogieParams.IDMeta,
     TyContext := @Lambda.LContext BoogieParams,
     EvalEnv := Lambda.LState BoogieParams
     EqIdent := inferInstanceAs (DecidableEq BoogieParams.Identifier) }

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
  @Lambda.TEnv.insertInContext ⟨Boogie.ExpressionMetadata, Boogie.Visibility⟩ _ T i ty

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
  identToString := (fun x => x.name)
  toGotoType := (fun ty => Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe)
  toGotoExpr := Lambda.LExpr.toGotoExpr

open Lambda in
def substVarNames {Metadata IDMeta: Type} [DecidableEq IDMeta]
    (e : LExpr ⟨⟨Metadata, IDMeta⟩, LMonoTy⟩) (frto : Map String String) : (LExpr ⟨⟨Unit, Boogie.Visibility⟩, LMonoTy⟩) :=
  match e with
  | .const _ c => .const () c
  | .bvar _ b => .bvar () b
  | .op _ o ty => .op () (Lambda.Identifier.mk o.name Boogie.Visibility.unres) ty
  | .fvar _ name ty =>
    let name_alt := frto.find? name.name
    .fvar () (Lambda.Identifier.mk (name_alt.getD name.name) Boogie.Visibility.unres) ty
  | .abs _ ty e' => .abs () ty (substVarNames e' frto)
  | .quant _ qk ty tr' e' => .quant () qk ty (substVarNames tr' frto) (substVarNames e' frto)
  | .app _ f e' => .app () (substVarNames f frto) (substVarNames e' frto)
  | .ite _ c t e' => .ite () (substVarNames c frto) (substVarNames t frto) (substVarNames e' frto)
  | .eq _ e1 e2 => .eq () (substVarNames e1 frto) (substVarNames e2 frto)

def Boogie.Cmd.renameVars (frto : Map String String) (c : Imperative.Cmd Boogie.Expression)
    : Imperative.Cmd Boogie.ExprStr :=
  match c with
  | .init name ty e _ =>
    let e' := substVarNames e frto
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .init new ty e' .empty
  | .set name e _ =>
    let e' := substVarNames e frto
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .set new e' .empty
  | .havoc name _ =>
    let name_alt := frto.find? (Boogie.BoogieIdent.toPretty name)
    let new := name_alt.getD (Boogie.BoogieIdent.toPretty name)
    .havoc new .empty
  | .assume label e _ =>
    let e' := substVarNames e frto
    .assume label e' .empty
  | .assert label e _ =>
    let e' := substVarNames e frto
    .assert label e' .empty

def Boogie.Cmds.renameVars (frto : Map String String)
    (cs : Imperative.Cmds Boogie.Expression) : Imperative.Cmds Boogie.ExprStr :=
  match cs with
  | [] => []
  | c :: crest => [(Boogie.Cmd.renameVars frto c)] ++ (renameVars frto crest)

-------------------------------------------------------------------------------

structure CProverGOTO.Context where
  program : CProverGOTO.Program
  locals : List String
  formals : Map String CProverGOTO.Ty
  ret : CProverGOTO.Ty

structure CProverGOTO.Json where
  symtab : Lean.Json := .null
  goto   : Lean.Json := .null

open Strata in
def CProverGOTO.Context.toJson (programName : String) (ctx : CProverGOTO.Context) :
  CProverGOTO.Json :=
  let fn_symbol : Map String CProverGOTO.CBMCSymbol :=
    [CProverGOTO.createFunctionSymbol programName ctx.formals ctx.ret]
  let formals : Map String CProverGOTO.CBMCSymbol :=
    ctx.formals.map (fun (name, ty) =>
        CProverGOTO.createGOTOSymbol programName name (CProverGOTO.mkFormalSymbol programName name)
          (isParameter := true) (isStateVar := true) (ty := some ty))
  let locals : Map String CProverGOTO.CBMCSymbol :=
    ctx.locals.map (fun name =>
        CProverGOTO.createGOTOSymbol programName name (CProverGOTO.mkLocalSymbol programName name)
          (isParameter := false) (isStateVar := false) (ty := none))
  let symbols := Lean.toJson (fn_symbol ++ formals ++ locals)
  let goto_functions := CProverGOTO.programsToJson [(programName, ctx.program)]
  { symtab := symbols, goto := goto_functions }

open Lambda.LTy.Syntax in
def transformToGoto (boogie : Boogie.Program) : Except Format CProverGOTO.Context := do
  let Ctx := { Lambda.LContext.default with functions := Boogie.Factory, knownTypes := Boogie.KnownTypes }
  let Env := Lambda.TEnv.default
  let (boogie, _Env) ← Boogie.Program.typeCheck Ctx Env boogie
  dbg_trace f!"[Strata.Boogie] Type Checking Succeeded!"
  if h : boogie.decls.length = 1 then
    let decl := boogie.decls[0]'(by exact Nat.lt_of_sub_eq_succ h)
    match decl.getProc? with
    | none => .error f!"[transformToGoto] We can process only Boogie procedures at this time. \
                        Declaration encountered: {decl}"
    | some p =>
      let pname := Boogie.BoogieIdent.toPretty p.header.name

      if !p.header.typeArgs.isEmpty then
        .error f!"[transformToGoto] Translation for polymorphic Boogie procedures is unimplemented."

      let cmds ← p.body.mapM
        (fun b => match b with
          | .cmd (.cmd c) => return c
          | _ => .error f!"[transformToGoto] We can process Boogie commands only, not statements! \
                           Statement encountered: {b}")

      if 1 < p.header.outputs.length then
        .error f!"[transformToGoto] Translation for multi-return value Boogie procedures is unimplemented."
      let ret_tys ← p.header.outputs.values.mapM (fun ty => Lambda.LMonoTy.toGotoType ty)
      let ret_ty := if ret_tys.isEmpty then CProverGOTO.Ty.Empty else ret_tys[0]!

      let formals := p.header.inputs.keys.map Boogie.BoogieIdent.toPretty
      let formals_tys ← p.header.inputs.values.mapM (fun ty => Lambda.LMonoTy.toGotoType ty)
      let new_formals := formals.map (fun f => CProverGOTO.mkFormalSymbol pname f)
      let formals_renamed := formals.zip new_formals
      let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys

      let locals := (Imperative.Stmts.definedVars p.body).map Boogie.BoogieIdent.toPretty
      let new_locals := locals.map (fun l => CProverGOTO.mkLocalSymbol pname l)
      let locals_renamed := locals.zip new_locals

      let args_renamed := formals_renamed ++ locals_renamed
      let cmds := Boogie.Cmds.renameVars args_renamed cmds

      let ans ← @Imperative.Cmds.toGotoTransform Boogie.ExprStr
                    BoogieToGOTO.instToGotoExprStr Env pname cmds (loc := 0)
      let ending_insts : Array CProverGOTO.Instruction := #[
        -- (FIXME): Add lifetime markers.
        -- { type := .DEAD, locationNum := ans.nextLoc + 1,
        --     code := .dead (.symbol "simpleAddUnsigned::1::z" (.UnsignedBV 32))},
          { type := .END_FUNCTION, locationNum := ans.nextLoc + 1}]
      let insts := ans.instructions ++ ending_insts

      let pgm := {  name := Boogie.BoogieIdent.toPretty p.header.name,
                    parameterIdentifiers := new_formals.toArray,
                    instructions := insts
                    }
      return { program := pgm,
               formals := formals_tys,
               ret := ret_ty,
               locals := locals }
  else
    .error f!"[transformToGoto] We can transform only a single Boogie procedure to \
              GOTO at a time!"

open Strata in
def getGotoJson (programName : String) (env : Program) : IO CProverGOTO.Json := do
  let (program, errors) := TransM.run Inhabited.default (translateProgram env)
  if errors.isEmpty then
    (match (BoogieToGOTO.transformToGoto program) with
      | .error e =>
        dbg_trace s!"{e}"
        return {}
      | .ok ctx =>
        return (CProverGOTO.Context.toJson programName ctx))
  else
    panic! s!"DDM Transform Error: {repr errors}"

open Strata in
def writeToGotoJson (programName symTabFileName gotoFileName : String) (env : Program) : IO Unit := do
  let json ← getGotoJson programName env
  IO.FS.writeFile symTabFileName json.symtab.pretty
  IO.FS.writeFile gotoFileName json.goto.pretty

end BoogieToGOTO

-------------------------------------------------------------------------------
