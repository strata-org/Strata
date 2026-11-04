/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypeSpecShared
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.WF
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.LTyWFSpec

/-! ## Typing relation: well-typedness of commands, statements, procedures, functions and programs

The annotated program typing rules of `ProgramTypeSpec` restated over variable scopes alone,
without the reserved-name and cross-kind name conditions; datatype blocks are registered with
`LContext.addMutualBlock`. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Strata.Util (HMaps)

public section

/-- `e` has the annotated type `mty`, its binder annotations use registered type constructors, and
    its annotations agree with the variable scopes `ts` and the function table of `C`. -/
@[expose] def ExprWellTyped (C : LContext CoreLParams) (ts : TypeScopes) (e : Expression.Expr)
    (mty : LMonoTy) : Prop :=
  LExpr.HasTypeA [] e mty ∧ BinderAnnotsKnown C e ∧ ScopesAnnotAgree C ts e

/-- Well-typedness of imperative commands from variable scopes `ts` to `ts'`. -/
inductive CmdWellTyped (C : LContext CoreLParams) :
    TypeScopes → Cmd Expression → TypeScopes → Prop where
  /-- `var x : T := e` declares a new `x` at the well-kinded monotype `T` of `e`, where `x` is not
      free in `e`. -/
  | init_det : ∀ ts x (xty : LTy) e mty md ts',
      ts.find? x = none →
      x ∉ HasFvars.getFvars (P := Expression) e →
      xty = .forAll [] mty →
      C.WellKindedTy mty →
      ExprWellTyped C ts e mty →
      HMaps.Equiv ts' (ts.insert x (.forAll [] mty)) →
      CmdWellTyped C ts (.init x xty (.det e) md) ts'
  /-- `var x : T := *` declares a new `x` at the well-kinded monotype `T`. -/
  | init_nondet : ∀ ts x (xty : LTy) mty md ts',
      ts.find? x = none →
      xty = .forAll [] mty →
      C.WellKindedTy mty →
      HMaps.Equiv ts' (ts.insert x (.forAll [] mty)) →
      CmdWellTyped C ts (.init x xty .nondet md) ts'
  /-- `x := e` assigns to a declared `x` of monotype `mty` an `e` of that type. -/
  | set_det : ∀ ts x mty e md ts',
      ts.find? x = some (.forAll [] mty) →
      ExprWellTyped C ts e mty →
      HMaps.Equiv ts' ts →
      CmdWellTyped C ts (.set x (.det e) md) ts'
  /-- `x := *` havocs a declared `x` of a monotype. -/
  | set_nondet : ∀ ts x mty md ts',
      ts.find? x = some (.forAll [] mty) →
      HMaps.Equiv ts' ts →
      CmdWellTyped C ts (.set x .nondet md) ts'
  /-- `assert l e` checks a boolean `e`. -/
  | assert : ∀ ts l e md ts',
      ExprWellTyped C ts e .bool →
      HMaps.Equiv ts' ts →
      CmdWellTyped C ts (.assert l e md) ts'
  /-- `assume l e` assumes a boolean `e`. -/
  | assume : ∀ ts l e md ts',
      ExprWellTyped C ts e .bool →
      HMaps.Equiv ts' ts →
      CmdWellTyped C ts (.assume l e md) ts'
  /-- `cover l e` covers a boolean `e`. -/
  | cover : ∀ ts l e md ts',
      ExprWellTyped C ts e .bool →
      HMaps.Equiv ts' ts →
      CmdWellTyped C ts (.cover l e md) ts'

/-- Well-typedness of extended commands from variable scopes `ts` to `ts'`. -/
inductive CmdExtWellTyped (C : LContext CoreLParams) (P : Program) :
    TypeScopes → Command → TypeScopes → Prop where
  /-- An imperative command is typed by `CmdWellTyped`. -/
  | cmd : ∀ ts c ts',
      CmdWellTyped C ts c ts' →
      CmdExtWellTyped C P ts (.cmd c) ts'
  /-- A well-formed call (`WF.WFcallProp`) of a procedure of `P` whose formals, instantiated by
      `σ`, are the types of its arguments and of its declared left-hand sides. -/
  | call : ∀ ts (pname : String) callArgs proc md (σ : List (TyIdentifier × LMonoTy)) ts',
      Program.Procedure.find? P pname = some proc →
      WF.WFcallProp P pname callArgs →
      (∀ v, v ∈ CallArg.getLhs callArgs → (ts.find? v).isSome) →
      (∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
           (hj : i < proc.header.inputs.values.length),
        match (CallArg.getInputExprs callArgs)[i] with
        | .fvar _ x none => ts.find? x =
            some (.forAll [] (LMonoTy.subst (HMaps.ofScopes [σ]) (proc.header.inputs.values[i])))
        | e => ExprWellTyped C ts e
            (LMonoTy.subst (HMaps.ofScopes [σ]) (proc.header.inputs.values[i]))) →
      (∀ i (hi : i < (CallArg.getLhs callArgs).length)
           (hj : i < proc.header.outputs.values.length),
        ts.find? ((CallArg.getLhs callArgs)[i]) =
          some (.forAll [] (LMonoTy.subst (HMaps.ofScopes [σ]) (proc.header.outputs.values[i])))) →
      HMaps.Equiv ts' ts →
      CmdExtWellTyped C P ts (.call pname callArgs md) ts'

/-- The kind of a declaration, counting a recursive function block as functions. -/
@[expose] def declNameKind (d : Decl) : DeclKind :=
  match d with
  | .recFuncBlock _ _ => .func
  | d => d.kind

/-- The names declared in `P` by declarations of kind `k`. -/
@[expose] def programNamesOfKind (P : Program) (k : DeclKind) : List Expression.Ident :=
  (P.decls.filter (fun d => declNameKind d == k)).flatMap Decl.names

mutual

/-- Well-typedness of statements: under program `P`, from context `C`, variable scopes
    `ts` and enclosing block labels `L`, to `C'` and `ts'`. -/
inductive StatementWellTyped (P : Program) :
    LContext CoreLParams → TypeScopes → List String → Statement →
    LContext CoreLParams → TypeScopes → Prop where
  /-- An extended command typed by `CmdExtWellTyped`. -/
  | cmd : ∀ C ts L c ts',
      CmdExtWellTyped C P ts c ts' →
      StatementWellTyped P C ts L (.cmd c) C ts'
  /-- A block whose label is not an enclosing one and whose body is typed with its label
      enclosing; its declarations end with it. -/
  | block : ∀ C ts C_body ts_body L label body md ts',
      label ∉ L →
      StatementsWellTyped P C ts (label :: L) body C_body ts_body →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.block label body md) C ts'
  /-- A conditional on a boolean with typed branches. -/
  | ite_det : ∀ C ts C_t ts_t C_e ts_e L cond thenb elseb md ts',
      ExprWellTyped C ts cond .bool →
      StatementsWellTyped P C ts L thenb C_t ts_t →
      StatementsWellTyped P C ts L elseb C_e ts_e →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.ite (.det cond) thenb elseb md) C ts'
  /-- A nondeterministic choice between typed branches. -/
  | ite_nondet : ∀ C ts C_t ts_t C_e ts_e L thenb elseb md ts',
      StatementsWellTyped P C ts L thenb C_t ts_t →
      StatementsWellTyped P C ts L elseb C_e ts_e →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.ite .nondet thenb elseb md) C ts'
  /-- A loop with a boolean guard if deterministic, an integer measure if any, boolean invariants
      and a typed body. -/
  | loop : ∀ C ts C_body ts_body L guard measure invariants body md ts',
      (∀ g, guard = .det g → ExprWellTyped C ts g .bool) →
      (∀ m, measure = some m → ExprWellTyped C ts m .int) →
      (∀ p, p ∈ invariants → ExprWellTyped C ts p.2 .bool) →
      StatementsWellTyped P C ts L body C_body ts_body →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.loop guard measure invariants body md) C ts'
  /-- An exit to an enclosing block. -/
  | exit : ∀ C ts L label md ts',
      label ∈ L →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.exit label md) C ts'
  /-- A type declaration, not named like a type declared in `P`, that adds a new known type to
      `C`. -/
  | typeDecl : ∀ C C' ts L tc md ts',
      (∀ n ∈ programNamesOfKind P .type, n.name ≠ tc.name) →
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      HMaps.Equiv ts' ts →
      StatementWellTyped P C ts L (.typeDecl tc md) C' ts'

/-- Well-typedness of statement lists, threading known types and variable scopes. -/
inductive StatementsWellTyped (P : Program) :
    LContext CoreLParams → TypeScopes → List String → List Statement →
    LContext CoreLParams → TypeScopes → Prop where
  /-- The empty list keeps the scopes. -/
  | nil : ∀ C ts L ts',
      HMaps.Equiv ts' ts →
      StatementsWellTyped P C ts L [] C ts'
  /-- The first statement is typed, then the rest from its output. -/
  | cons : ∀ C C' C'' ts ts' ts'' L s ss,
      StatementWellTyped P C ts L s C' ts' →
      StatementsWellTyped P C' ts' L ss C'' ts'' →
      StatementsWellTyped P C ts L (s :: ss) C'' ts''

end

/-- Well-typedness of a procedure body from context `C` and variable scopes `ts`; a CFG
    body carries no obligation. -/
inductive ProcBodyWellTyped (P : Program) (C : LContext CoreLParams) (ts : TypeScopes) :
    Procedure.Body → Prop where
  /-- A structured body is a statement list typed with no enclosing block. -/
  | structured : ∀ ss C' ts',
      StatementsWellTyped P C ts [] ss C' ts' →
      ProcBodyWellTyped P C ts (.structured ss)
  | cfg : ∀ c, ProcBodyWellTyped P C ts (.cfg c)

/-- Well-typedness of a procedure under program `P`, in context `C` and variable scopes
    `ts`. -/
structure ProcWellTyped (P : Program) (C : LContext CoreLParams) (ts : TypeScopes)
    (proc : Procedure) : Prop where
  inputsNodup : proc.header.inputs.keys.Nodup
  outputsNodup : proc.header.outputs.keys.Nodup
  /-- No parameter is named like the saved starting value of an in-out parameter. -/
  oldNamesFresh : proc.header.oldNamesFresh
  typeArgsNodup : proc.header.typeArgs.Nodup
  /-- Every type variable of the signature is a type parameter. -/
  noUndeclaredVars : ∀ v,
    v ∈ LMonoTys.freeVars proc.header.inputs.values ++
        LMonoTys.freeVars proc.header.outputs.values →
    v ∈ proc.header.typeArgs
  signatureWellKinded : ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values,
    C.WellKindedTy ty
  /-- Every variable the body modifies is an output or defined in the body. -/
  modRights : ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body →
    v ∈ proc.header.outputs.keys ++
        HasVarsImp.definedVars (P := Expression) proc.body false
  /-- Each precondition is boolean over the inputs. -/
  preconditionsTyped : ∀ c ∈ proc.spec.preconditions.values,
    ExprWellTyped C (procInputScopes ts proc) c.expr .bool
  /-- Each postcondition is boolean over the inputs, outputs and `old` in-outs. -/
  postconditionsTyped : ∀ c ∈ proc.spec.postconditions.values,
    ExprWellTyped C (procBodyScopes ts proc) c.expr .bool
  /-- The body is typed over the inputs, outputs and `old` in-outs. -/
  bodyTyped : ProcBodyWellTyped P C (procBodyScopes ts proc) proc.body

/-- Well-typedness of a function in context `C` and variable scopes `ts`. -/
structure FuncWellTyped (C : LContext CoreLParams) (ts : TypeScopes) (func : Function) : Prop
    where
  inputsNodup : func.inputs.keys.Nodup
  typeArgsNodup : func.typeArgs.Nodup
  /-- Every type variable of the signature is a type parameter. -/
  noUndeclaredVars : ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) →
    v ∈ func.typeArgs
  /-- Every type parameter occurs in the signature. -/
  typeArgsInSignature : ∀ ta ∈ func.typeArgs,
    ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values)
  signatureWellKinded : ∀ ty ∈ func.output :: func.inputs.values, C.WellKindedTy ty
  /-- A body has the return type over the formals. -/
  bodyTyped : ∀ body, func.body = some body →
    ExprWellTyped C (funcScopes ts func) body func.output
  /-- Only a recursive function has a measure. -/
  measureOnlyRecursive : func.isRecursive = false → func.measure = none
  /-- A bare-variable measure is a formal of type `int` or of a registered datatype; any other
      measure has type `int`. -/
  measureTyped : ∀ m, func.measure = some m →
    match m with
    | .fvar _ x _ => ∃ ty, func.inputs.find? x = some ty ∧
        (ExprWellTyped C (funcScopes ts func) m .int ∨
          ∃ n args, ty = .tcons n args ∧ (C.datatypes.getType n).isSome ∧
            ExprWellTyped C (funcScopes ts func) m (.tcons n args))
    | _ => ExprWellTyped C (funcScopes ts func) m .int
  /-- Each precondition is boolean over the formals. -/
  preconditionsTyped : ∀ p ∈ func.preconditions,
    ExprWellTyped C (funcScopes ts func) p.expr .bool
  /-- Each axiom is boolean over the formals. -/
  axiomsTyped : ∀ ax ∈ func.axioms, ExprWellTyped C (funcScopes ts func) ax .bool
  /-- Every annotation type variable is a type parameter. -/
  annotsScoped : ∀ e ∈ func.exprs, ∀ v ∈ annotTyVars e, v ∈ func.typeArgs
  constrNoBody : func.isConstr = true → func.body = none

/-- Well-typedness of a declaration under program `P`, from context `C` in variable scopes
    `ts` to context `C'`. -/
inductive DeclWellTyped (P : Program) :
    LContext CoreLParams → TypeScopes → Decl → LContext CoreLParams → Prop where
  /-- A type constructor added to `C` as a new known type. -/
  | type_con : ∀ C C' ts tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      DeclWellTyped P C ts (.type (.con tc) md) C'
  /-- A type definition `type N params := body` that is a well-formed alias, with `N` not a known
      type of `C`, whose body is a resolved type. -/
  | type_syn : ∀ C ts syn md,
      TypeAlias.WF { name := syn.name, typeArgs := syn.typeArgs, type := syn.type } →
      ¬ C.knownTypes.containsName syn.name →
      ResolvedTyWF C TyVarAdmissibility.all syn.type →
      DeclWellTyped P C ts (.type (.syn syn) md) C
  /-- A mutual datatype block that `LContext.addMutualBlock` adds to `C`. -/
  | type_data : ∀ C C' ts block md,
      C.addMutualBlock block = .ok C' →
      DeclWellTyped P C ts (.type (.data block) md) C'
  /-- An axiom: a boolean with no annotation type variables. -/
  | ax : ∀ C ts a md,
      ExprWellTyped C ts a.e .bool →
      annotTyVars a.e = [] →
      DeclWellTyped P C ts (.ax a md) C
  /-- A lemma: a boolean whose annotation type variables are its distinct type parameters. -/
  | lemma : ∀ C ts l md,
      ExprWellTyped C ts l.e .bool →
      l.typeArgs.Nodup →
      (∀ v ∈ annotTyVars l.e, v ∈ l.typeArgs) →
      DeclWellTyped P C ts (.lemma l md) C
  /-- A `distinct` declaration: two or more expressions of one monotype, with no annotation type
      variables. -/
  | distinct : ∀ C ts l es md,
      2 ≤ es.length →
      (∃ mty, ∀ e ∈ es, ExprWellTyped C ts e mty) →
      (∀ e ∈ es, annotTyVars e = []) →
      DeclWellTyped P C ts (.distinct l es md) C
  /-- A procedure typed by `ProcWellTyped`; the context is unchanged. -/
  | proc : ∀ C ts proc md,
      ProcWellTyped P C ts proc →
      DeclWellTyped P C ts (.proc proc md) C
  /-- A non-recursive function, not named like a function of `C`, typed by `FuncWellTyped` and
      added to `C`. -/
  | func : ∀ C C' ts func md,
      ¬ func.isRecursive →
      func.name.name ∉ C.functions →
      FuncWellTyped C ts func →
      FactoryExtendedBy (fun f g => g = f) C C' [func.toLFunc] →
      DeclWellTyped P C ts (.func func md) C'
  /-- A non-empty block of recursive, non-inline functions, none named like a function of `C`,
      each typed against `C` extended with the signatures of all of them; the output adds every
      function to `C`. -/
  | recFuncBlock : ∀ C Cstub C' ts funcs md stubs fullFuncs,
      funcs ≠ [] →
      (∀ f ∈ funcs, f.name.name ∉ C.functions) →
      (∀ f ∈ funcs, ∀ a ∈ f.attr, a ≠ .inline) →
      stubs = funcs.map (fun f => { name := f.name, typeArgs := f.typeArgs,
                                    inputs := f.inputs, output := f.output }) →
      fullFuncs = funcs.map (·.toLFunc) →
      FactoryExtendedBy (fun f g => g = f) C Cstub stubs →
      FactoryExtendedBy (fun f g => g = f) C C' fullFuncs →
      (∀ f ∈ funcs, FuncWellTyped Cstub ts f) →
      (∀ f ∈ funcs, f.isRecursive = true) →
      DeclWellTyped P C ts (.recFuncBlock funcs md) C'

/-- Well-typedness of a declaration list under program `P`, threading the context. -/
inductive DeclsWellTyped (P : Program) :
    LContext CoreLParams → TypeScopes → List Decl → LContext CoreLParams → Prop where
  | nil : ∀ C ts, DeclsWellTyped P C ts [] C
  | cons : ∀ C C' C'' ts d ds,
      DeclWellTyped P C ts d C' →
      DeclsWellTyped P C' ts ds C'' →
      DeclsWellTyped P C ts (d :: ds) C''

/-- Well-typedness of a program in context `C` and variable scopes `ts`: names are
    distinct within each kind of declaration, and the declarations are typed. -/
@[expose] def ProgramWellTyped (C : LContext CoreLParams) (ts : TypeScopes) (P : Program) : Prop :=
  (∀ k, (programNamesOfKind P k).Nodup) ∧ ∃ C', DeclsWellTyped P C ts P.decls C'

end -- public section

end TypeSpec
end Core
