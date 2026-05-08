/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Datatypes
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Types
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Expressions
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Statements
public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.CoreMatch.ToCore
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.TypeDecl
public import Strata.Languages.Core.Program

/-!
Top-level command translation and the public entry points
(`toMProgram`, `getProgram`, `toCoreProgram`) that drive the full
`Strata.Program → Core.Program` pipeline.
-/

namespace Strata.CoreMatch.Translate

open Lambda
open Strata.CoreMatchDDM

public section

private def toCoreBinding (b : Binding SourceRange)
    : TransM (Core.Expression.Ident × LMonoTy) := do
  match b with
  | .mkBinding    _ ⟨_, n⟩ tp
  | .outBinding   _ ⟨_, n⟩ tp
  | .inoutBinding _ ⟨_, n⟩ tp
  | .casesBinding _ ⟨_, n⟩ tp =>
    match tp with
    | .expr ty  => return (mkIdent n, ← toCoreMonoType ty)
    | .type m   => throwAt m "unexpected Type parameter in term binding"

private def toCoreSpec (procName : String) (spec? : Option (Spec SourceRange))
    : TransM Core.Procedure.Spec := do
  let some (.spec_mk _ ⟨_, elts⟩) := spec? | return default
  let mut requires : List (Core.CoreLabel × Core.Procedure.Check) := []
  let mut ensures  : List (Core.CoreLabel × Core.Procedure.Check) := []
  for e in elts.toList do
    match e with
    | .requires_spec m ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      let lbl  ← freshLabel m s!"{procName}_requires" l?
      let attr := if free?.isSome then Core.Procedure.CheckAttr.Free else .Default
      requires := (lbl, { expr := ← toCoreExpr cond, attr }) :: requires
    | .ensures_spec m ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      let lbl  ← freshLabel m s!"{procName}_ensures" l?
      let attr := if free?.isSome then Core.Procedure.CheckAttr.Free else .Default
      ensures  := (lbl, { expr := ← toCoreExpr cond, attr }) :: ensures
  return { preconditions := requires.reverse, postconditions := ensures.reverse }

private def toCoreDatatype (dtName : String) (typeParams : List String)
    (ctors : ConstructorList SourceRange) : TransM (LDatatype Unit) := do
  let toLConstr (c : Constructor SourceRange) : TransM (LConstr Unit) := do
    let .constructor_mk _ ⟨_, cname⟩ _ := c
    return { name       := mkIdent cname
             args       := ← (ctorFields c).mapM toCoreBinding
             testerName := s!"{dtName}..is{cname}" }
  match constructorListToList ctors with
  | [] => throw <| .fromMessage s!"datatype {dtName} must have at least one constructor"
  | c :: rest =>
    return { name       := dtName
             typeArgs   := typeParams
             constrs    := (← toLConstr c) :: (← rest.mapM toLConstr)
             constrs_ne := by simp }

/-- Cache `(ctorName, fieldNames)` info for a datatype declaration so
later commands can resolve match arms against it. -/
private def cacheDatatype : DatatypeDecl SourceRange → TransM Unit
  | .datatype_decl _ ⟨_, dtName⟩ _ ctors =>
    let info := (constructorListToList ctors).map fun c =>
      let .constructor_mk _ ⟨_, cname⟩ _ := c
      (cname, (ctorFields c).map bindingName)
    addDatatype dtName info

/-- Translate a function body in scope of its inputs. When `recFns`
is non-empty the body is translated under `withRecFns`, so
self-references in match arms get rewritten to rec-result slots. -/
private def translateFnBody
    (ins : Bindings SourceRange) (ret : CoreMatchType SourceRange)
    (body : CoreMatchDDM.Expr SourceRange) (recFns : List String := [])
    : TransM (List (Core.Expression.Ident × LMonoTy) × LMonoTy × Core.Expression.Expr) := do
  let bs       := bindingsToList ins
  let inputs   ← bs.mapM toCoreBinding
  let outMTy   ← toCoreMonoType ret
  let translate := if recFns.isEmpty then toCoreExpr body
                   else withRecFns recFns (toCoreExpr body)
  let bodyE    ← withBVars (bs.map bindingName) translate
  return (inputs, outMTy, bodyE)

private def mkMFunction (name : String)
    (inputs : List (Core.Expression.Ident × LMonoTy))
    (output : LMonoTy) (bodyExpr : Core.Expression.Expr)
    : Strata.CoreMatch.MFunction :=
  { name     := mkIdent name
    typeArgs := []
    inputs
    output
    body := some (.core bodyExpr) }

def toCoreDecls : Command SourceRange → TransM (List Strata.CoreMatch.MDecl)
  | .command_procedure _ ⟨_, n⟩ _ ins ⟨_, spec?⟩ ⟨_, body?⟩ => do
    let bs     := bindingsToList ins
    let inputs ← bs.mapM toCoreBinding
    let names  := bs.map bindingName
    let spec   ← withBVars names (toCoreSpec n spec?)
    let body   ← match body? with
      | none   => pure []
      | some b => withBVars names (toMBlock b)
    let header : Core.Procedure.Header :=
      { name := mkIdent n, typeArgs := [], inputs, outputs := [] }
    return [.proc { header, spec, body } {}]
  | .command_datatypes _ ⟨_, decls⟩ => do
    for d in decls do cacheDatatype d
    let lds ← decls.toList.mapM fun
      | .datatype_decl _ ⟨_, n⟩ _ ctors => toCoreDatatype n [] ctors
    return [.type (.data lds) {}]
  | .command_fndef _ ⟨_, n⟩ _ ins ret _ body _ => do
    let (inputs, outMTy, e) ← translateFnBody ins ret body
    return [.func (mkMFunction n inputs outMTy e) {}]
  | .command_recfndefs _ ⟨_, fns⟩ => do
    let allNames := fns.toList.filterMap fun
      | .recfn_decl _ ⟨_, n⟩ _ _ _ _ _ => some n
    fns.toList.mapM fun
      | .recfn_decl _ ⟨_, n⟩ _ ins ret _ body => do
        let (inputs, outMTy, e) ← translateFnBody ins ret body (recFns := allNames)
        return .func (mkMFunction n inputs outMTy e) {}
  | cmd => throw <| .fromMessage s!"unsupported CoreMatch top-level command: {repr cmd}"

/-- Per command, list whether each symbol it introduces resolves as
an op (`true`) or a term-level fvar (`false`). Order must match the
order DDM pushes symbols into `GlobalContext`. Mirrors
`Boole.initFVarIsOp`. -/
private def commandSymbolKinds : Command SourceRange → List Bool
  | .command_typedecl     _ _ _              => [false]
  | .command_typesynonym  _ _ _ _ _          => [false]
  | .command_constdecl    _ _ _ _            => [true]
  | .command_fndecl       _ _ _ _ _          => [true]
  | .command_fndef        _ _ _ _ _ _ _ _    => [true]
  | .command_recfndefs    _ ⟨_, fs⟩          => fs.toList.map fun _ => true
  | .command_datatypes    _ ⟨_, decls⟩       => decls.toList.map fun _ => false
  | _                                        => []

def initFVarIsOp (cmds : Array (Command SourceRange)) : Array Bool :=
  (cmds.toList.flatMap commandSymbolKinds).toArray

@[expose]
def toMProgram (p : CoreMatchDDM.Program SourceRange) (gctx : GlobalContext)
    (fileName : String) : Except DiagnosticModel Strata.CoreMatch.MProgram := do
  let .prog _ ⟨_, cmds⟩ := p
  let init : TransState := { fileName, gctx, fvarIsOp := initFVarIsOp cmds }
  let act : TransM Strata.CoreMatch.MProgram := do
    let dss ← cmds.toList.mapM toCoreDecls
    return { decls := dss.flatten }
  Prod.fst <$> StateT.run act init

@[expose]
def getProgram (p : Strata.Program)
    : Except DiagnosticModel (CoreMatchDDM.Program SourceRange) := do
  let cmds : Array Arg := p.commands.map ArgF.op
  let progOp : Operation :=
    { ann  := default
      name := q`CoreMatch.prog
      args := #[.seq default .spacePrefix cmds] }
  match CoreMatchDDM.Program.ofAst progOp with
  | .ok prog   => return prog
  | .error msg => throw <| .fromMessage msg

@[expose]
def toCoreProgram (p : Strata.Program) (fileName : String := "")
    : Except DiagnosticModel Core.Program := do
  let typed ← getProgram p
  let mprog ← toMProgram typed p.globalContext fileName
  return Strata.CoreMatch.ToCore.compileProgram mprog

end

end Strata.CoreMatch.Translate
