/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.LambdaToCProverGOTO
public import Strata.Languages.GOTO.ToCProverGOTO
public import Strata.Languages.GOTO.Program
public import Strata.Languages.Core.Program
public import Strata.DL.Util.Map
public import Lean.Data.Json
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.Factory

public section

open Std (ToFormat Format format)

/-
We translate Strata Core's procedures into a CProverGOTO program (a
`CoreToGOTO.CProverGOTO.Context`). Emitting that program as CBMC-compatible JSON
(the symbol table and GOTO functions) and writing it to disk lives separately in
the CBMC backend (`Strata.Backends.CBMC.GOTO.CoreToCProverGOTO`).

Also see `mkGotoBin.sh`, where we use CBMC's `symtab2gb` to construct and
model-check a Strata-generated GOTO binary.
-/

-------------------------------------------------------------------------------

abbrev CoreParams : Lambda.LExprParams := ⟨Unit, Unit⟩

abbrev Core.ExprStr : Imperative.PureExpr :=
   { Ident := CoreParams.Identifier,
     Expr := Lambda.LExpr CoreParams.mono,
     Ty := Lambda.LTy,
     ExprMetadata := CoreParams.Metadata,
     TyEnv := @Lambda.TEnv CoreParams.IDMeta,
     TyContext := @Lambda.LContext CoreParams,
     EvalEnv := Lambda.LState CoreParams
     EqIdent := inferInstanceAs (DecidableEq CoreParams.Identifier) }

namespace CoreToGOTO

def lookupType (T : Core.Expression.TyEnv) (i : Core.Expression.Ident) :
    Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => throw f!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else throw f!"Poly-type unexpected in the context for {i}: {ty}"

def updateType (T : Core.Expression.TyEnv) (i : Core.Expression.Ident)
    (ty : Core.Expression.Ty) : Core.Expression.TyEnv :=
  @Lambda.TEnv.addInNewestContext ⟨Core.ExpressionMetadata, Unit⟩ T [(i, ty)]

instance : Imperative.ToGoto Core.Expression where
  lookupType := lookupType
  updateType := updateType
  identToString := (fun i => i.toPretty)
  toGotoType := (fun ty => Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe)
  toGotoExpr := Lambda.LExpr.toGotoExpr

def lookupTypeStr (T : Core.ExprStr.TyEnv) (i : Core.ExprStr.Ident) :
    Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => throw f!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else throw f!"Poly-type unexpected in the context for {i}: {ty}"

def updateTypeStr (T : Core.ExprStr.TyEnv) (i : Core.ExprStr.Ident)
    (ty : Core.ExprStr.Ty) : Core.ExprStr.TyEnv :=
  T.addInNewestContext [(i, ty)]

instance : Imperative.ToGoto Core.ExprStr where
  lookupType := lookupTypeStr
  updateType := updateTypeStr
  identToString := (fun x => x.name)
  toGotoType := (fun ty => Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe)
  toGotoExpr := Lambda.LExpr.toGotoExpr

open Lambda in
def substVarNames {Metadata IDMeta: Type} [DecidableEq IDMeta]
    (e : LExpr ⟨⟨Metadata, IDMeta⟩, LMonoTy⟩) (frto : Map String String) : (LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩) :=
  match e with
  | .const _ c => .const () c
  | .bvar _ b => .bvar () b
  | .op _ o ty => .op () (Lambda.Identifier.mk o.name ()) ty
  | .fvar _ name ty =>
    let name_alt := frto.find? name.name
    .fvar () (Lambda.Identifier.mk (name_alt.getD name.name) ()) ty
  | .abs _ name ty e' => .abs () name ty (substVarNames e' frto)
  | .quant _ qk name ty tr' e' => .quant () qk name ty (substVarNames tr' frto) (substVarNames e' frto)
  | .app _ f e' => .app () (substVarNames f frto) (substVarNames e' frto)
  | .ite _ c t e' => .ite () (substVarNames c frto) (substVarNames t frto) (substVarNames e' frto)
  | .eq _ e1 e2 => .eq () (substVarNames e1 frto) (substVarNames e2 frto)

/-- Convert metadata from `Core.Expression` to `Core.ExprStr`, preserving
    label-keyed elements (fileRange, propertySummary, etc.) and dropping
    variable-keyed elements whose identifier type changes. -/
def convertMetaData (md : Imperative.MetaData Core.Expression)
    : Imperative.MetaData Core.ExprStr :=
  md.filterMap fun elem =>
    match elem.fld with
    | .label l => match elem.value with
      | .msg s => some ⟨.label l, .msg s⟩
      | .switch b => some ⟨.label l, .switch b⟩
      | .provenance p => some ⟨.label l, .provenance p⟩
      | .expr _ => none
    | .var _ => none

def Core.Cmd.renameVars (frto : Map String String) (c : Imperative.Cmd Core.Expression)
    : Imperative.Cmd Core.ExprStr :=
  match c with
  | .init name ty e md =>
    let e' := e.map (substVarNames · frto)
    let name_alt := frto.find? (Core.CoreIdent.toPretty name)
    let new := name_alt.getD (Core.CoreIdent.toPretty name)
    .init new ty e' (convertMetaData md)
  | .set name e md =>
    let e' := e.map (substVarNames · frto)
    let name_alt := frto.find? (Core.CoreIdent.toPretty name)
    let new := name_alt.getD (Core.CoreIdent.toPretty name)
    .set new e' (convertMetaData md)
  | .assume label e md =>
    let e' := substVarNames e frto
    .assume label e' (convertMetaData md)
  | .assert label e md =>
    let e' := substVarNames e frto
    .assert label e' (convertMetaData md)
  | .cover label e md =>
    let e' := substVarNames e frto
    .cover label e' (convertMetaData md)

def Core.Cmds.renameVars (frto : Map String String)
    (cs : Imperative.Cmds Core.Expression) : Imperative.Cmds Core.ExprStr :=
  match cs with
  | [] => []
  | c :: crest => [(Core.Cmd.renameVars frto c)] ++ (renameVars frto crest)

-------------------------------------------------------------------------------

structure CProverGOTO.Context where
  program : CProverGOTO.Program
  locals : List String
  formals : Map String CProverGOTO.Ty
  ret : CProverGOTO.Ty
  /-- Contract annotations for the code type (e.g., `#spec_requires`, `#spec_ensures`). -/
  contracts : List (String × Lean.Json) := []
  /-- Optional types for local variables (output parameters, typed locals). -/
  localTypes : Std.HashMap String CProverGOTO.Ty := {}

open Lambda.LTy.Syntax in
def transformToGoto (cprog : Core.Program) : Except Format CProverGOTO.Context := do
  let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
  let Env := Lambda.TEnv.default
  let (cprog, _Env) ← Core.Program.typeCheck Ctx Env cprog |>.mapError (fun dm => dm.format none)
  dbg_trace f!"[Strata.Core] Type Checking Succeeded!"
  if h : cprog.decls.length = 1 then
    let decl := cprog.decls[0]'(by exact Nat.lt_of_sub_eq_succ h)
    match decl.getProc? with
    | none => throw f!"[transformToGoto] We can process only Strata Core procedures at this time. \
                        Declaration encountered: {decl}"
    | some p =>
      let pname := Core.CoreIdent.toPretty p.header.name

      if !p.header.typeArgs.isEmpty then
        throw f!"[transformToGoto] Translation for polymorphic Strata Core procedures is unimplemented."

      -- TODO: This pass could be split into a two-stage transformation:
      -- 1. structured → cfg (via StructuredToUnstructured)
      -- 2. cfg → CProverGOTO (always operates on CFG, no pattern matching needed)
      let bodyStmts ← p.body.getStructured.mapError fun s => f!"{s}"
      let cmds ← bodyStmts.mapM
        (fun b => match b with
          | .cmd (.cmd c) => return c
          | _ => throw f!"[transformToGoto] We can process Strata Core commands only, not statements! \
                           Statement encountered: {b}")

      if 1 < p.header.outputs.length then
        throw f!"[transformToGoto] Translation for multi-return value Strata Core procedures is unimplemented."
      let ret_tys ← p.header.outputs.values.mapM (fun ty => Lambda.LMonoTy.toGotoType ty)
      let ret_ty := if ret_tys.isEmpty then CProverGOTO.Ty.Empty else ret_tys[0]!

      let formals := p.header.inputs.keys.map Core.CoreIdent.toPretty
      let formals_tys ← p.header.inputs.values.mapM (fun ty => Lambda.LMonoTy.toGotoType ty)
      let new_formals := formals.map (fun f => CProverGOTO.mkFormalSymbol pname f)
      let formals_renamed := formals.zip new_formals
      let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys

      let locals := (Imperative.Block.definedVars bodyStmts false).map Core.CoreIdent.toPretty
      let new_locals := locals.map (fun l => CProverGOTO.mkLocalSymbol pname l)
      let locals_renamed := locals.zip new_locals

      let args_renamed := formals_renamed ++ locals_renamed
      let cmds := Core.Cmds.renameVars args_renamed cmds

      let ans ← @Imperative.Cmds.toGotoTransform Core.ExprStr
                    CoreToGOTO.instToGotoExprStr _ Env pname cmds (loc := 0) (sourceText := none)
      let ending_insts : Array CProverGOTO.Instruction := #[
        -- (FIXME): Add lifetime markers.
        -- { type := .DEAD, locationNum := ans.nextLoc + 1,
        --     code := .dead (.symbol "simpleAddUnsigned::1::z" (.UnsignedBV 32))},
          { type := .END_FUNCTION, locationNum := ans.nextLoc + 1}]
      let insts := ans.instructions ++ ending_insts

      let pgm := {  name := Core.CoreIdent.toPretty p.header.name,
                    parameterIdentifiers := new_formals.toArray,
                    instructions := insts
                    }
      return { program := pgm,
               formals := formals_tys,
               ret := ret_ty,
               locals := locals }
  else
    throw f!"[transformToGoto] We can transform only a single Strata Core procedure to \
              GOTO at a time!"

end CoreToGOTO

-------------------------------------------------------------------------------
