/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.CallWF
import Strata.Util.String
import Strata.DL.Imperative.CmdType
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprType
import Strata.Languages.Core.CmdType
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.FunctionType
import Strata.Languages.Core.WrittenTyVarScope
import Strata.DL.Lambda.LTyUnifyProps

public section

namespace Core

/-- Instantiate `h`'s type parameters with fresh type variables, shared by its
    inputs and outputs. -/
def Procedure.Header.instantiate (C : Lambda.LContext CoreLParams)
    (Env : Lambda.TEnv CoreLParams.IDMeta) (h : Procedure.Header) :
    Except Std.Format (@Lambda.LMonoTySignature Unit × @Lambda.LMonoTySignature Unit ×
                       Lambda.TEnv CoreLParams.IDMeta) := do
  let (sig, Env) ← Lambda.LMonoTySignature.instantiate C Env h.typeArgs (h.inputs ++ h.outputs)
  let (inp, out) := sig.splitAt h.inputs.length
  return (inp, out, Env)

namespace Statement

open Lambda Imperative
open Std (ToFormat Format format)
open Strata (Message FileRange)
---------------------------------------------------------------------

/-- The error for the ill-formed call `c` at `md`, explained by `msg`. -/
def illFormedCallError (c : Command) (md : MetaData Expression) (msg : String) : Message :=
  md.toDiagnosticF f!"[{c}]: {illFormedCallText msg}"

/--
Type checker for Strata Core commands.

Note that this function needs the entire program to type-check `call`
commands by looking up the corresponding procedure's information.
-/
def typeCheckCmd (C: LContext CoreLParams) (Env : TEnv Unit) (P : Program) (c : Command) :
  Except Message (Command × (TEnv Unit)) := do
  match c with
  | .cmd c =>
    let _ ← (match c with
      | .init x _ _ md => do
          if x.name ∈ C.functions then
            throw (md.toDiagnosticF
              (nameClashMsg s!"Local variable '{x.name}'"))
      | _ => pure ())
    -- Any errors in `Imperative.Cmd.typeCheck` already include source
    -- locations.
    let (c, Env) ← Imperative.Cmd.typeCheck C Env c
    .ok (.cmd c, Env)
  | .call pname callArgs md => try
    let lhs := CallArg.getLhs callArgs
    let args := CallArg.getInputExprs callArgs
    -- `try`: to augment any errors with source location info.
     match Program.Procedure.find? P pname with
     | none => .error <| illFormedCallError c md (undeclaredProcedureMessage pname)
     | some proc =>
       if let some msg := callArgsError? pname proc callArgs then
         .error <| illFormedCallError c md msg
       else if lhs.any (fun (l: CoreIdent) => (Env.context.types.find? l).isNone) then
         .error <| md.toDiagnosticF f!"[{c}]: All the return variables {lhs} must exist in the context!"
       else do
         -- Get the types of lhs variables and unify with the procedures'
         -- return types.
         let lhsinsts ← Lambda.Identifier.instantiateAndSubsts lhs C Env |>.mapError Message.fromFormat
         match lhsinsts with
         | none => .error <| md.toDiagnosticF f!"Implementation error. \
                             Types of {lhs} should have been known."
         | some (lhs_tys, Env) =>
           -- Every argument's free variables are reported before any later failure.
           let argsFreeVarErr := fun _ => Env.freeVarChecks args
           let (inp_sig, ret_sig, Env) ←
             SourceExpr.orFreeVarError argsFreeVarErr (proc.header.instantiate C Env)
               |>.mapError Message.fromFormat
           let inp_mtys := LMonoTys.subst Env.stateSubstInfo.subst inp_sig.values
           let ret_mtys := LMonoTys.subst Env.stateSubstInfo.subst ret_sig.values
           let ret_lhs_constraints := lhs_tys.zip ret_mtys
           -- Infer the types of the actuals and unify with the types of the
           -- procedure's formals.
           let (argsa, Env) ←
             SourceExpr.orFreeVarError argsFreeVarErr (SourceExpr.resolves C Env args)
               |>.mapError Message.fromFormat
           let args_tys := argsa.map LExpr.toLMonoTy
           let args' := argsa.map $ LExpr.unresolved
           let lhs_inp_constraints := (args_tys.zip inp_mtys)
           -- Keep the raw error if an enclosing rigid type is involved, else report a mismatch.
           let enclosingRigid :=
             !mtysAllTyConsNames (fun n => !n.startsWith skolemPrefix) (args_tys ++ lhs_tys)
           let S ← Constraints.unify (lhs_inp_constraints ++ ret_lhs_constraints) Env.stateSubstInfo
             |> .mapError (fun e =>
                  if enclosingRigid then Message.fromFormat (format e)
                  else md.toDiagnosticF f!"[call {pname}]: argument types \
                    {displayTys Env.stateSubstInfo.subst args_tys} and return types \
                    {displayTys Env.stateSubstInfo.subst lhs_tys} are incompatible with signature \
                    ({proc.header.inputs.values}) → ({proc.header.outputs.values})")
           let Env := Env.updateSubst S
           let newCallArgs := CallArg.replaceInArgs callArgs args'
           let s' := .call pname newCallArgs md
           .ok (s', Env)
      catch e =>
        -- Add source location to error messages if not already present.
        .error <| e.withRangeIfUnknown (getFileRange md |>.getD FileRange.unknown)

/-- The type variables the inference substitution of `Env` binds or mentions. -/
def substTyVars (Env : TEnv Unit) : List TyIdentifier :=
  Env.stateSubstInfo.subst.keys ++ Subst.freeVars Env.stateSubstInfo.subst

/-- The type variables of the inference substitution and the context of `Env`. -/
def usedTyVars (Env : TEnv Unit) : List TyIdentifier :=
  substTyVars Env ++ TContext.knownTypeVars Env.context

/-- Reject `es` if a free-variable or binder annotation in one has a type variable neither rigid
    nor bound in `m`; with `writable`, only type variables a user may write are checked. -/
def checkAnnotsInScope (writable : Bool) (rigid : List TyIdentifier)
    (m : List (TyIdentifier × TyIdentifier)) (es : List Expression.Expr) : Except Message Unit :=
  match WrittenTyVarScope.unboundAnnotMsg? writable rigid m es with
  | some msg => .error (Message.fromFormat msg)
  | none => .ok ()

/-- The type constructors in `mtys` that `ks` does not register at the arity used. -/
def unknownTysCons (ks : Lambda.KnownTypes) (mtys : LMonoTys) : List String :=
  ((mtys.flatMap getTypeConsArities).filter
    (fun ref => !ks.contains { name := ref.1, metadata := ref.2 })).map Prod.fst

/-- Whether some statement of `ss`, not nested in another statement, declares a variable. -/
def hasTopLevelInit (ss : List Statement) : Bool :=
  ss.any fun
    | .cmd (.cmd (.init ..)) => true
    | _ => false

/-- Check a statement list, solving one type substitution for the whole list. Each written type
    variable is renamed to a checker name unique to its scope. -/
def typeCheckAux (C: LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss : List Statement) :
    Except Message
      (List Statement × TEnv Unit × LContext CoreLParams) := do
  let (ss', Env', C', _) ← go C Env ss [] [] []
    (WrittenTyVarScope.initState C.rigidTypeVars (usedTyVars Env) ss)
  .ok (ss', Env', C')
where
  /-- Check `ss` after the checked statements `acc` (most recent first), renaming each statement
      through `m` before checking it. -/
  go (C : LContext CoreLParams) (Env : TEnv Unit) (ss : List Statement) (acc : List Statement)
    (labels : List String) (m : WrittenTyVarScope.ScopeMap) (st : WrittenTyVarScope.ScopeState) :
    Except Message
      (List Statement × TEnv Unit × LContext CoreLParams × WrittenTyVarScope.ScopeState) :=
    let errorWithSourceLoc := fun (e : Message) md =>
      e.withRangeIfUnknown (getFileRange md |>.getD FileRange.unknown)
    match ss with
    | [] => .ok (acc.reverse, Env, C, st)
    | s :: srest => do
      let (s', Env, C, m, st) ←
        match s with
        | .cmd cmd => do
          let rc := WrittenTyVarScope.renameCmd C.rigidTypeVars m st cmd
          let cmdMd := match cmd with
            | .cmd c => c.getMetaData
            | .call _ _ md => md
          -- An annotation reads the scope after a declaration's own bindings.
          let _ ← (checkAnnotsInScope false C.rigidTypeVars rc.2.1 (cmdExprs cmd)).mapError
            (errorWithSourceLoc · cmdMd)
          let (c', Env) ← typeCheckCmd C Env P rc.1
          .ok (Stmt.cmd c', Env, C, rc.2.1, rc.2.2)

        | .block label bss md => do
          if labels.contains label then
            throw <| md.toDiagnosticF
              f!"Block label \"{label}\" shadows an enclosing block."
          let (bss', Env, C, st) ← goBlock C Env bss [] (label :: labels) m st
          let s' := Stmt.block label bss' md
          .ok (s', Env, C, m, st)

        | .ite cond tss ess md => do try
          checkAnnotsInScope false C.rigidTypeVars m cond.toList
          match WrittenTyVarScope.renameExprOrNondet m cond with
          | .det c =>
            let (conda, Env) ←
              SourceExpr.orFreeVarError (fun _ => Env.freeVarCheck c (fun _ => f!"[{s}]"))
                (SourceExpr.resolve C Env c) |>.mapError Message.fromFormat
            let condty := conda.toLMonoTy
            match condty with
            | .tcons "bool" [] =>
              let (tss, Env, C, st) ← goBlock C Env tss [] labels m st
              let (ess, Env, C, st) ← goBlock C Env ess [] labels m st
              let s' := Stmt.ite (.det conda.unresolved) tss ess md
              .ok (s', Env, C, m, st)
            | _ => .error <| md.toDiagnosticF f!"[{s}]: If's condition {c} is not of type `bool`!"
          | .nondet =>
            let (tss, Env, C, st) ← goBlock C Env tss [] labels m st
            let (ess, Env, C, st) ← goBlock C Env ess [] labels m st
            let s' := Stmt.ite .nondet tss ess md
            .ok (s', Env, C, m, st)
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .loop guard measure invariant bss md => do try
          checkAnnotsInScope false C.rigidTypeVars m (loopExprs guard measure invariant)
          let guardResult ← match WrittenTyVarScope.renameExprOrNondet m guard with
            | .det g => do
              let (conda, Env) ←
                SourceExpr.orFreeVarError (fun _ => Env.freeVarCheck g (fun _ => f!"[{s}]"))
                  (SourceExpr.resolve C Env g) |>.mapError Message.fromFormat
              let condty := conda.toLMonoTy
              if condty != .tcons "bool" [] then
                throw <| md.toDiagnosticF f!"[{s}]: Loop's guard {g} is not of type `bool`!"
              pure (some conda, Env)
            | .nondet => pure (none, Env)
          let (guarda, Env) := guardResult
          let (mt, Env) ← (match measure.map (WrittenTyVarScope.renameExpr m) with
          | .some m => do
            let (ma, Env) ←
              SourceExpr.orFreeVarError (fun _ => Env.freeVarCheck m (fun _ => f!"[{s}]"))
                (SourceExpr.resolve C Env m) |>.mapError Message.fromFormat
            .ok (some ma, Env)
          | _ => .ok (none, Env))
          let (it, Env) ←
            (invariant.map (fun (l, i) => (l, WrittenTyVarScope.renameExpr m i))).foldlM
            (fun (acc, E) (lbl, i) => do
            let (ia, E') ←
              SourceExpr.orFreeVarError (fun _ => E.freeVarCheck i (fun _ => f!"[{s}]"))
                (SourceExpr.resolve C E i) |>.mapError Message.fromFormat
            if ia.toLMonoTy == .tcons "bool" [] then
              .ok (acc ++ [(lbl, ia)], E')
            else
              .error <| md.toDiagnosticF f!"[{s}]: Loop's invariant {i} is not of type `bool`!"
          ) (([] : List (String × _)), Env)
          let mty := mt.map (fun e => e.toLMonoTy)
          match mty with
          | none | some (.tcons "int" []) =>
            let (tb, Env, C, st) ← goBlock C Env bss [] labels m st
            let guarda' : ExprOrNondet Expression := match guarda with
              | some e => .det e.unresolved
              | none => .nondet
            let s' := Stmt.loop guarda' (mt.map (fun e => e.unresolved))
              (it.map (fun (lbl, e) => (lbl, e.unresolved))) tb md
            .ok (s', Env, C, m, st)
          | _ =>
            .error <| md.toDiagnosticF f!"[{s}]: Loop's measure {measure} is not of type `int`!"
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .exit l md => do try
          match op with
          | .some _ =>
            if labels.contains l then
              .ok (s, Env, C, m, st)
            else
              .error <| md.toDiagnosticF f!"{s}: exit label \"{l}\" does not match any enclosing block."
          | .none => .error <| md.toDiagnosticF f!"{s} occurs outside a procedure."
          catch e =>
            -- Add source location to error messages.
            .error (errorWithSourceLoc e md)

        | .typeDecl tc md => do try
          -- Add the type to the context. Shadowing is not allowed: if a
          -- type with the same name was already declared (at the program
          -- level or in an enclosing scope), this will return an error.
          let C ← TypeConstructor.typeCheck tc (.bodyLocal P.getNames) C Env
          .ok (.typeDecl tc md, Env, C, m, st)
          catch e =>
            .error (errorWithSourceLoc e md)

      go C Env srest (s' :: acc) labels m st
  /-- Check the body of a block, a conditional branch or a loop body; its declarations do not
      stay in scope. -/
  goBlock (C : LContext CoreLParams) (Env : TEnv Unit) (bss : Imperative.Block Core.Expression Core.Command) (acc : List Statement)
    (labels : List String) (m : WrittenTyVarScope.ScopeMap) (st : WrittenTyVarScope.ScopeState) :
    Except Message
      (List Statement × TEnv Unit × LContext CoreLParams × WrittenTyVarScope.ScopeState) := do
    -- Only a body with a top-level variable declaration or a scopeless context gets a new scope;
    -- the walk state `st` is kept.
    let push := hasTopLevelInit bss || Env.context.types.isEmpty
    let (ss', Envb, _, st) ← go C (if push then Env.pushEmptyContext else Env) bss acc labels m st
    .ok (ss', if push then Envb.popContext else Envb, C, st)

private def substExprOrNondet (S : Subst) (e : Imperative.ExprOrNondet Expression) : Imperative.ExprOrNondet Expression :=
  e.map (LExpr.applyTypeSubst · S)

/-- Apply type substitution `S` to a basic command's declared type and expressions. -/
def Cmd.subst (S : Subst) : Cmd Expression → Cmd Expression
  | .init x ty e md => .init x (LTy.subst S ty) (substExprOrNondet S e) md
  | .set x e md => .set x (substExprOrNondet S e) md
  | .assert label b md => .assert label (b.applyTypeSubst S) md
  | .assume label b md => .assume label (b.applyTypeSubst S) md
  | .cover label b md => .cover label (b.applyTypeSubst S) md

/-- Apply type substitution `S` to a call argument; only input expressions change. -/
def CallArg.subst (S : Subst) : CallArg Expression → CallArg Expression :=
  CallArg.mapInput (·.applyTypeSubst S)

/--
Apply type substitution `S` to a command.
-/
def Command.subst (S : Subst) (c : Command) : Command :=
  match c with
  | .cmd c => .cmd (Cmd.subst S c)
  | .call pname callArgs md => .call pname (callArgs.map (CallArg.subst S)) md

/--
Apply type substitution `S` to a statement.

Note: This substitutes type variables in types, not term variables.
-/
def Statement.subst (S : Subst) (s : Statement) : Statement :=
  match s with
  | .cmd cmd => .cmd (Command.subst S cmd)
  | .block label bss md =>
    .block label (go S bss []) md
  | .ite cond tss ess md =>
    .ite (cond.map (LExpr.applyTypeSubst · S)) (go S tss []) (go S ess []) md
  | .loop guard m i bss md =>
    .loop (guard.map (LExpr.applyTypeSubst · S))
      (m.map (LExpr.applyTypeSubst · S))
      (i.map (fun (l, e) => (l, e.applyTypeSubst S))) (go S bss []) md
  | .exit _ _ => s
  | .typeDecl _ _ => s  -- Type declarations don't contain type variables to substitute
  where
    go S ss acc : List Statement :=
    match ss with
    | [] => acc.reverse
    | s :: srest => go S srest ((Statement.subst S s) :: acc)

/-- Apply type substitution `S` to a CFG block: its commands and its branch guard. The block's
    other fields are kept. -/
def DetBlock.subst (S : Subst) (blk : DetBlock String Command Expression) :
    DetBlock String Command Expression :=
  { blk with
    cmds := blk.cmds.map (Command.subst S),
    transfer := match blk.transfer with
      | .condGoto p lt lf md => .condGoto (LExpr.applyTypeSubst p S) lt lf md
      | .finish md => .finish md }

/-! ## Types are declared where they are stored

A `type` declaration in a body is in scope for the statements after it in its own block. -/

/-- The types annotating `s` itself, outside any statement list nested in `s`. -/
def stmtOwnAnnotTys (s : Statement) : List LMonoTy :=
  stmtOwnCollect exprAnnotTys ([·]) s

/-- The scope rule for a `type` declaration in a body, as error messages state it. -/
def tyDeclScopeRule : String :=
  "A `type` declaration inside a body is in scope for the statements that \
    follow it, and only within its own block."

/-- The type constructor names `ns`, quoted and separated by commas. -/
def tyNamesList (ns : List String) : String :=
  String.intercalate ", " (ns.map (s!"`{·}`"))

/-- The error message for `what`, occurring at `site`, using the undeclared type constructors
    `ns`. -/
def undeclaredTyUseMsg (what site : String) (ns : List String) : String :=
  let thatTy := if ns.length == 1 then "that type is" else "those types are"
  s!"{what} uses {tyNamesList ns}, but {thatTy} not declared where {site} occurs. \
    {tyDeclScopeRule}"

/-- The error message for the command `c` using the undeclared type constructors `ns`. -/
def cmdUndeclaredTyUseMsg (c : Command) (ns : List String) : String :=
  match c, ns with
  | .cmd (.init x ty _ _), [n] =>
    if ty == .forAll [] (.tcons n []) then
      s!"Variable `{x.name}` has type `{n}`, which is not declared where `{x.name}` is \
        declared. {tyDeclScopeRule}"
    else
      s!"Variable `{x.name}` has type `{format ty}`, which uses `{n}`, but that type is not \
        declared where `{x.name}` is declared. {tyDeclScopeRule}"
  | .cmd (.init x ty _ _), _ =>
    s!"Variable `{x.name}` has type `{format ty}`, which uses {tyNamesList ns}, but those types \
      are not declared where `{x.name}` is declared. {tyDeclScopeRule}"
  | c, _ => undeclaredTyUseMsg s!"The statement `{format c}`" "the statement" ns

/-- Fail with `msg` of the type constructors in `tys` that `ks` does not register at the arity
    used, if there are any. -/
def checkTysKnown (ks : Lambda.KnownTypes) (tys : List LMonoTy) (msg : List String → String) :
    Except String Unit :=
  match (unknownTysCons ks tys).eraseDups with
  | [] => .ok ()
  | ns => .error (msg ns)

mutual
/-- Check `s` against the registrations `ks` where it occurs, returning those in force after `s`,
    or the message for the first statement whose own annotations use a type constructor not
    registered where it occurs. Declarations in nested lists do not escape `s`. -/
def undeclaredTyUseStmt (ks : Lambda.KnownTypes) (s : Statement) :
    Except String Lambda.KnownTypes :=
  match s with
  | .cmd c => do
    checkTysKnown ks (stmtOwnAnnotTys s) (cmdUndeclaredTyUseMsg c)
    .ok ks
  | .ite _ tss ess _ => do
    checkTysKnown ks (stmtOwnAnnotTys s) (undeclaredTyUseMsg "An `if` condition" "the `if`")
    let _ ← undeclaredTyUseStmts ks tss
    let _ ← undeclaredTyUseStmts ks ess
    .ok ks
  | .loop _ _ _ bss _ => do
    checkTysKnown ks (stmtOwnAnnotTys s)
      (undeclaredTyUseMsg "A loop guard, measure or invariant" "the loop")
    let _ ← undeclaredTyUseStmts ks bss
    .ok ks
  | .block _ bss _ => do let _ ← undeclaredTyUseStmts ks bss; .ok ks
  | .typeDecl tc _ => .ok (ks.insert tc.name tc.numargs)
  | .exit _ _ => .ok ks

/-- Check `ss` in order from the registrations `ks`, carrying each `type` declaration to the
    statements after it. -/
def undeclaredTyUseStmts (ks : Lambda.KnownTypes) (ss : List Statement) :
    Except String Lambda.KnownTypes :=
  match ss with
  | [] => .ok ks
  | s :: rest => do
    let ks ← undeclaredTyUseStmt ks s
    undeclaredTyUseStmts ks rest
end

/-- Checks that each stored annotation uses only type constructors declared before that statement
    in its enclosing scope. -/
def tysDeclaredWhereStored (ks : Lambda.KnownTypes) (ss : List Statement) : Except Message Unit :=
  match undeclaredTyUseStmts ks ss with
  | .ok _ => .ok ()
  | .error msg => .error (Message.fromString msg)

/-! ## Statement type checking -/

/-- Whether `key` is one of the canonical names generated while the type-variable counter
    advanced from `before` to `after`: the generator prefix followed by the decimal spelling of a
    number in `[before.tyGen, after.tyGen)`. -/
def generatedDuring (before after : TState) (key : TyIdentifier) : Bool :=
  let pfx := TState.tyPrefix.toList
  let rest := key.toList.drop pfx.length
  pfx.isPrefixOf key.toList &&
    match listCharToNat? rest with
    | some n => before.tyGen ≤ n && n < after.tyGen && (toString n).toList == rest
    | none => false

/-- A check's substitution information with each binding of a pre-existing variable to one
    generated during the check flipped. -/
def ambientSubstInfo (before after : TState) (SI : SubstInfo) : SubstInfo :=
  { subst := ambientSubst (generatedDuring before after) SI.subst
    isWF := ambientSubst_WF (generatedDuring before after) SI.subst SI.isWF }

/-- The walk's final substitution, reoriented so that a type variable the walk did not generate
    keeps its name when solved to one it generated. `before` is the generator state at the start
    of the walk. -/
def finalSubstInfo (before : TState) (Env : Expression.TyEnv) : SubstInfo :=
  ambientSubstInfo before Env.genEnv.genState Env.stateSubstInfo

/--
Type checker and annotater for Statements.

Note that this function needs the entire program to type-check statements to
check whether `exit` statements occur inside a procedure (or .none for statements that don't occur
inside a procedure).

TODO: `Stmt.defUseWellFormed` (in `Strata/DL/Imperative/Stmt.lean`) must be
proven correct: successful type checking here should imply
`Stmt.defUseWellFormed` / `Block.defUseWellFormed` holds on the checked
statements.
-/
def typeCheck (C: Expression.TyContext) (Env : Expression.TyEnv) (P : Program) (op : Option Procedure) (ss : List Statement) :
  Except Message (List Statement × Expression.TyEnv) := do
  let (ss', EnvA, _) ← typeCheckAux C Env P op ss
  let Env := EnvA.updateSubst (finalSubstInfo Env.genEnv.genState EnvA)
  let context := TContext.subst Env.context Env.stateSubstInfo.subst
  let Env := Env.updateContext context
  let ss' := Statement.subst.go Env.stateSubstInfo.subst ss' []
  let _ ← tysDeclaredWhereStored C.knownTypes ss'
  .ok (ss', Env)

---------------------------------------------------------------------

end Statement
end Core

end -- public section
