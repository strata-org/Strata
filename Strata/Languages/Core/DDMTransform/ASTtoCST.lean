/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program

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
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let name : Ann String M := ⟨default, tcons.name⟩
  modify (·.addGlobalFreeVars #[name.val])
  let args := typeConArgsToCST (M := M) tcons
  pure (.command_typedecl default name args)

/-- Convert a datatype declaration to CST -/
def datatypeToCST {M} [Inhabited M] (datatypes : List (Lambda.LDatatype Visibility))
    (_md : Imperative.MetaData Expression) : ToCSTM M (List (Command M)) := do
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
  let datatypesCmd := Command.command_datatypes default ⟨default, decls.toArray⟩
  pure [datatypesCmd]

/-- Convert a type synonym declaration to CST -/
def typeSynToCST {M} [Inhabited M] (syn : Core.TypeSynonym)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
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
  pure (.command_typesynonym default name args targs rhs)

/-- Convert a recursive function to a RecFnDecl CST node -/
def recFnDeclToCST {M} [Inhabited M]
    (func : Lambda.LFunc Core.CoreLParams)
    (_md : Imperative.MetaData Expression) : ToCSTM M (RecFnDecl M) := do
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
  let bodyExpr ← match func.body with
    | some body => lexprToExpr body 0
    | none => pure (.btrue default)  -- shouldn't happen for recursive functions
  modify ToCSTContext.popScope
  pure (.recfn_decl default name typeArgs b r preconds bodyExpr)

/-- Convert a function declaration to CST -/
def funcToCST {M} [Inhabited M]
    (func : Lambda.LFunc Core.CoreLParams)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
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
  let result ← match func.body with
  | none => pure (.command_fndecl default name typeArgs b r)
  | some body => do
    -- Add formals to the context.
    modify (·.addScopedBoundVars (reverse? := false) paramNames)
    -- Convert preconditions
    let preconds ← precondsToSpecElts func.preconditions
    let bodyExpr ← lexprToExpr body 0
    let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
    pure (.command_fndef default name typeArgs b r preconds bodyExpr inline?)
  modify ToCSTContext.popScope
  -- Register function name as free variable.
  modify (·.addGlobalFreeVars #[name.val])
  pure result

/-- Convert an axiom to CST -/
def axiomToCST {M} [Inhabited M] (ax : Core.Axiom)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨
      default, some (.label default ⟨default, ax.name⟩)⟩
  let exprCST ← lexprToExpr ax.e 0
  pure (.command_axiom default labelAnn exprCST)

/-- Convert a distinct declaration to CST -/
def distinctToCST {M} [Inhabited M] (name : Core.CoreIdent) (es : List (Lambda.LExpr Core.CoreLParams.mono))
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, name.toPretty⟩)⟩
  let exprsCST ← es.mapM (fun a => lexprToExpr a 0)
  let exprsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, exprsCST.toArray⟩
  pure (.command_distinct default labelAnn exprsAnn)

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
  | .proc proc _md => do
    let cmd ← procToCST proc
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
    let recFnDecls ← funcs.mapM fun func => recFnDeclToCST func md
    let cmd := Command.command_recfndefs default ⟨default, recFnDecls.toArray⟩
    pure [cmd]

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST {M} [Inhabited M] (prog : Core.Program)
    (initCtx : ToCSTContext M := ToCSTContext.empty) :
    ToCSTContext M × List (Command M) :=
  let (cmds, finalCtx) := (do
    let cmdLists ← prog.decls.mapM declToCST
    pure cmdLists.flatten).run initCtx
  (finalCtx, cmds)

/-- Render `Core.Program` to a format object.

If the Core program is expected to have some constructs not defined in the
Grammar (e.g., via a custom Factory), then use `extraFreeVars` to add
their names globally to the translation and formatting context.
-/
def Core.formatProgram (ast : Core.Program)
    (extraFreeVars : Array String := #[]) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (finalCtx, cmds) := programToCST ast initCtx
  let header : Std.Format := "program Core;\n\n"
  header ++ formatWithDDM finalCtx fun ctx state =>
    Std.Format.joinSep (cmds.map fun cmd =>
      (mformat (ArgF.op cmd.toAst) ctx state).format) ""

instance instCoreProgramFormat : Std.ToFormat Core.Program where
  format := Core.formatProgram

instance instCoreProgramString : ToString Core.Program where
  toString p := toString (Core.formatProgram p)

end ToCST

---------------------------------------------------------------------

end Strata

end -- public section
