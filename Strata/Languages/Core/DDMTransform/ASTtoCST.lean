/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
open StrataDDM

public section

/-!
# Core.Program → CoreCST Conversion (Program-level)

This module extends `FormatCore.lean` with Program-level conversion functions
that require `Core.Program`, `Core.Decl`, and related types (`Axiom`,
`Function`, `TypeDecl`).

For expression, statement, procedure, and command conversion and formatting,
see `FormatCore.lean`.
-/

namespace Strata

open Core
open Strata.CoreDDM

---------------------------------------------------------------------
-- Program-level CST Conversion
---------------------------------------------------------------------

section ToCST

def typeConToCST {M} [Inhabited M] (tcons : TypeConstructor)
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  let name : Ann String M := ⟨default, tcons.name⟩
  modify (·.addGlobalFreeVars #[name.val])
  let args := typeConArgsToCST (M := M) tcons
  let annotsAnn := metadataToAnn md (← get).annFilter
  pure (.command_typedecl default annotsAnn name args)

/-- Convert a datatype declaration to CST -/
def datatypeToCST {M} [Inhabited M] (datatypes : List (Lambda.LDatatype Visibility))
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (List (Command M)) := do
  -- Register datatype names first, then constructor/tester/destructor names.
  -- For mutual datatypes, names may already be in context from forward
  -- declarations.
  let dtNames := datatypes.map (·.name)
  for dtName in dtNames.reverse do
    let ctx ← get
    if ctx.freeVarIndex? dtName |>.isNone then
      modify (·.addGlobalFreeVars #[dtName])

  -- Then register constructor, tester, and destructor names
  -- for each datatype.
  for dt in datatypes do
    let constrNames := dt.constrs.map (·.name.name)
    let testerNames := dt.constrs.map (·.testerName)
    let destructorNames :=
        dt.constrs.flatMap (fun c => c.args.map
                              (fun (id, _) =>
                                Lambda.destructorFuncName dt id))
    let unsafeDestructorNames :=
        dt.constrs.flatMap (fun c => c.args.map
                              (fun (id, _) =>
                                Lambda.unsafeDestructorFuncName dt id))
    modify (·.addGlobalFreeVars (constrNames.toArray ++
                           testerNames.toArray ++
                           destructorNames.toArray ++
                           unsafeDestructorNames.toArray))

  let processDatatype (dt : Lambda.LDatatype Visibility) :
      ToCSTM M (DatatypeDecl M) := do
    let name : Ann String M := ⟨default, dt.name⟩
    let args : Ann (Option (Bindings M)) M :=
      if dt.typeArgs.isEmpty then
        ⟨default, none⟩
      else
        let bindings := dt.typeArgs.map fun param =>
          let paramName : Ann String M := ⟨default, param⟩
          let paramType := TypeP.type default
          Binding.mkBinding default paramName paramType
        ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
    let processConstr (c : Lambda.LConstr Visibility) :
          ToCSTM M (Constructor M) := do
      let constrName : Ann String M := ⟨default, c.name.name⟩
      let constrArgs ←
        if c.args.isEmpty then
          pure ⟨default, none⟩
        else do
          let bindings ← c.args.mapM fun (id, ty) => do
            let paramName : Ann String M := ⟨default, id.name⟩
            let paramType ← lmonoTyToCoreType ty
            pure (Binding.mkBinding default paramName (TypeP.expr paramType))
          pure ⟨default, some ⟨default, bindings.toArray⟩⟩
      pure (Constructor.constructor_mk default constrName constrArgs)
    let constrs ← dt.constrs.mapM processConstr
    let constrList ←
      if constrs.isEmpty then
        ToCSTM.logError "datatypeToCST" "datatype has no constructors" dt.name
        pure (ConstructorList.constructorListAtom default default)
      else if constrs.length == 1 then
        pure (ConstructorList.constructorListAtom default constrs[0]!)
      else
        pure (constrs.tail.foldl
          (fun acc c => ConstructorList.constructorListPush default acc c)
          (ConstructorList.constructorListAtom default constrs[0]!))
    pure (DatatypeDecl.datatype_decl default name args constrList)

  let decls ← datatypes.mapM processDatatype
  let annotsAnn := metadataToAnn md (← get).annFilter
  let datatypesCmd := Command.command_datatypes default annotsAnn ⟨default, decls.toArray⟩
  pure [datatypesCmd]

/-- Convert a type synonym declaration to CST -/
def typeSynToCST {M} [Inhabited M] (syn : Core.TypeSynonym)
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, syn.name⟩
  modify (·.addGlobalFreeVars #[name.val])
  let args : Ann (Option (Bindings M)) M :=
    if syn.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let bindings := syn.typeArgs.map fun param =>
        let paramName : Ann String M := ⟨default, param⟩
        let paramType := TypeP.type default
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  let targs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let rhs ← lmonoTyToCoreType syn.type
  modify ToCSTContext.popScope
  let annotsAnn := metadataToAnn md (← get).annFilter
  pure (.command_typesynonym default annotsAnn name args targs rhs)

/-- Convert a recursive function to a RecFnDecl CST node -/
def recFnDeclToCST {M} [Inhabited M]
    (func : Lambda.LFunc Core.CoreLParams)
    : ToCSTM M (RecFnDecl M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, func.name.name⟩
  let typeArgs := mkTypeArgsAnn func.typeArgs
  let processInput (id : Core.CoreLParams.Identifier) (ty : Lambda.LMonoTy) (isCases : Bool) :
          ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := if isCases then
      Binding.casesBinding default paramName (TypeP.expr paramType)
    else
      Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let casesIdx := func.attr.findSome? fun
    | .inlineIfConstr i => some i
    | _ => none
  let results ← func.inputs.toArray.mapIdxM fun idx (id, ty) =>
    processInput id ty (casesIdx == some idx)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2)
  let b : Bindings M := .mkBindings default ⟨default, bindings⟩
  let r ← lmonoTyToCoreType func.output
  modify (·.addScopedBoundVars (reverse? := false) paramNames)
  let preconds ← precondsToSpecElts func.preconditions
  let decreases : Ann (Option (Measure M)) M ← match func.measure with
    | some m =>
      let mExpr ← lexprToExpr m 0
      pure ⟨default, some (.measure_mk default mExpr)⟩
    | none => pure ⟨default, none⟩
  let bodyExpr ← match func.body with
    | some body => lexprToExpr body 0
    | none => pure (.btrue default)  -- shouldn't happen for recursive functions
  modify ToCSTContext.popScope
  pure (.recfn_decl default name typeArgs b r preconds decreases bodyExpr)

/-- Convert a function declaration to CST -/
def funcToCST {M} [Inhabited M]
    (func : Lambda.LFunc Core.CoreLParams)
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, func.name.name⟩
  let typeArgs := mkTypeArgsAnn func.typeArgs
  let processInput (id : Core.CoreLParams.Identifier) (ty : Lambda.LMonoTy) :
          ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let results ← func.inputs.toArray.mapM (fun (id, ty) => processInput id ty)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2)
  let b : Bindings M := .mkBindings default ⟨default, bindings⟩
  let r ← lmonoTyToCoreType func.output
  let annotsAnn := metadataToAnn md (← get).annFilter
  let result ← match func.body with
  | none => pure (.command_fndecl default annotsAnn name typeArgs b r)
  | some body => do
    -- Add formals to the context.
    modify (·.addScopedBoundVars (reverse? := false) paramNames)
    -- Convert preconditions
    let preconds ← precondsToSpecElts func.preconditions
    let bodyExpr ← lexprToExpr body 0
    let inline? : Ann (Option (Inline M)) M :=
      if func.attr.any (· == .inline) then ⟨default, some (.inline default)⟩
      else ⟨default, none⟩
    pure (.command_fndef default annotsAnn name typeArgs b r preconds bodyExpr inline?)
  modify ToCSTContext.popScope
  -- Register function name as free variable.
  modify (·.addGlobalFreeVars #[name.val])
  pure result

/-- Convert an axiom to CST -/
def axiomToCST {M} [Inhabited M] (ax : Core.Axiom)
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨
      default, some (.label default ⟨default, ax.name⟩)⟩
  let exprCST ← lexprToExpr ax.e 0
  let annotsAnn := metadataToAnn md (← get).annFilter
  pure (.command_axiom default annotsAnn labelAnn exprCST)

/-- Convert a distinct declaration to CST -/
def distinctToCST {M} [Inhabited M] (name : Core.CoreIdent) (es : List (Lambda.LExpr Core.CoreLParams.mono))
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, name.toPretty⟩)⟩
  let exprsCST ← es.mapM (fun a => lexprToExpr a 0)
  let exprsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, exprsCST.toArray⟩
  let annotsAnn := metadataToAnn md (← get).annFilter
  pure (.command_distinct default annotsAnn labelAnn exprsAnn)

/-- Convert a `Core.Decl` to a Core `Command` -/
def declToCST {M} [Inhabited M] (decl : Core.Decl) : ToCSTM M (List (Command M)) :=
  match decl with
  | .type (.con tcons) md => do
    let cmd ← typeConToCST tcons md
    pure [cmd]
  | .type (.syn syn) md => do
    let cmd ← typeSynToCST syn md
    pure [cmd]
  | .type (.data datatypes) md =>
    datatypeToCST datatypes md
  | .func func md => do
    let cmd ← funcToCST func md
    pure [cmd]
  | .proc proc md => do
    let cmd ← procToCST proc md
    pure [cmd]
  | .ax ax md => do
    let cmd ← axiomToCST ax md
    pure [cmd]
  | .distinct name es md => do
    let cmd ← distinctToCST name es md
    pure [cmd]
  | .recFuncBlock funcs md => do
    -- Register function names as free variables so self/sibling calls resolve
    let fnNames := funcs.map (·.name.name)
    modify (·.addGlobalFreeVars fnNames.toArray)
    let recFnDecls ← funcs.mapM fun func => recFnDeclToCST func
    let annotsAnn := metadataToAnn md (← get).annFilter
    let cmd := Command.command_recfndefs default annotsAnn ⟨default, recFnDecls.toArray⟩
    pure [cmd]

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST {M} [Inhabited M] (prog : Core.Program)
    (initCtx : ToCSTContext M := ToCSTContext.empty) :
    ToCSTContext M × List (Command M) :=
  let rec go (decls : List Core.Decl) (acc : List (Command M))
      (ctx : ToCSTContext M) : List (Command M) × ToCSTContext M :=
    match decls with
    | [] => (acc, ctx)
    | d :: ds =>
      let (cmds, ctx') := (declToCST d).run ctx
      go ds (cmds.reverse ++ acc) ctx'
  let (cmds, finalCtx) := go prog.decls [] initCtx
  (finalCtx, cmds.reverse)

/-- Canonical formatter for `Core.Program`. Controls metadata annotation
emission via `annFilter` (default `.none` — no annotations emitted).
To emit annotations, call this directly with a non-default filter. -/
def Core.formatProgram (ast : Core.Program)
    (extraFreeVars : Array String := #[])
    (annFilter : MetadataAnnFilter := .none) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := { initCtx with annFilter }
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (finalCtx, cmds) := programToCST ast initCtx
  let header : Std.Format := "program Core;\n\n"
  header ++ formatWithDDM finalCtx fun ctx state =>
    Std.Format.joinSep (cmds.map fun cmd =>
      (mformat (ArgF.op cmd.toAst) ctx state).format) ""

/-- Uses `Core.formatProgram` with default filter (`.none` — no annotations). -/
instance instCoreProgramFormat : Std.ToFormat Core.Program where
  format := Core.formatProgram

/-- Uses `Core.formatProgram` with default filter (`.none` — no annotations). -/
instance instCoreProgramString : ToString Core.Program where
  toString p := toString (Core.formatProgram p)

end ToCST

---------------------------------------------------------------------

end Strata

end -- public section
