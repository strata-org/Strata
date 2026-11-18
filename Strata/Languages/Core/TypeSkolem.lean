/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Axiom
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.LExprWF
public import Strata.DL.Lambda.LTy
public import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LTyWF
public import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Util.Name

/-! # Type-parameter renaming and skolemization for Core declarations

Renames the written types and type names of commands, statements and procedures, the
type variables a procedure or lemma mentions, and `Lemma.renameTypeArgs`. It also skolemizes
types and expressions (type parameters become rigid constants), resolves source expressions,
and finishes elaborated expressions by applying the substitution and deskolemizing. -/

public section

namespace Core

open Lambda Imperative
open Std (ToFormat Format format)

/-! ## Rigid skolemization: type parameters are checked as fresh nullary type constants,
    which unification cannot refine, then mapped back to their names. -/

/-- The rigid constant named after the type variable `a`. -/
def skolemName (a : String) : String := skolemPrefix ++ a

/-- A definition's rigid type parameters, each paired with the nullary type
    constant standing in for it. -/
abbrev RigidNames := List (String × String)

/-- The rigid renaming for the type parameters `typeArgs` of the definition `name`: parameter `a`
    gets `$__rigid_{name}_{a}`, or its first `_k` variant, that is neither `taken` nor chosen
    earlier. `fuel` bounds the number of taken names. -/
def mintRigidNames (name : String) (taken : String → Bool) (fuel : Nat)
    (typeArgs : List String) : RigidNames :=
  typeArgs.zip
    (Strata.Name.freshNamesBy taken fuel (typeArgs.map fun a => skolemName s!"{name}_{a}"))

/-- The type constructor names in the types of the literals of `e`. -/
def exprLitTyNames (e : Expression.Expr) : List String :=
  (LExpr.getConsts e).flatMap (fun c => getTypeRefs c.ty)

/-- A renaming of the type parameters among `typeArgs` that start with a reserved prefix
    (`Lambda.isAllowedName`): each gets a fresh name `a`, `a_1`, … that is not among `avoid ()`
    and differs from the names chosen before it. Type checking generates type variables with
    such prefixes, so it renames a declaration's own first instead of rejecting them. `avoid` is
    called only when some type parameter has a reserved prefix. -/
def reservedTypeArgsRenaming (typeArgs : List String) (avoid : Unit → List String) :
    List (String × String) :=
  let reserved := typeArgs.filter (!isAllowedName ·)
  if reserved.isEmpty then []
  else
    reserved.zip
      (Strata.Name.freshNames (Std.HashSet.ofList (avoid ())) (reserved.map fun _ => "a")).1

/-- `rename` applied to the reserved renaming of `typeArgs` away from `avoid ()`
    (`reservedTypeArgsRenaming`), or `x` when that renaming is empty. -/
def renameReservedWith {α : Type} (typeArgs : List String) (avoid : Unit → List String)
    (rename : List (String × String) → α) (x : α) : α :=
  let ren := reservedTypeArgsRenaming typeArgs avoid
  if ren.isEmpty then x else rename ren

/-- The type variables in scope when a declaration is checked in `C` and `Env`: the rigid type
    variables of `C` and the free type variables of the variables in scope. A renamed type
    parameter must avoid them, or it would turn into one of them. -/
def scopeTyVars (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) : List String :=
  C.rigidTypeVars ++ Env.context.knownTypeVars

/-- The type annotations of a command: the declared type of a variable and the annotations of
    its expressions. -/
def cmdAnnotTys (c : Command) : List LMonoTy :=
  cmdCollect exprAnnotTys ([·]) c

/-- The type annotations of a statement. -/
def stmtAnnotTys (s : Statement) : List LMonoTy :=
  stmtCollect exprAnnotTys ([·]) s

/-- The type annotations of a list of statements. -/
def stmtsAnnotTys (ss : List Statement) : List LMonoTy :=
  stmtsCollect exprAnnotTys ([·]) ss

/-- The type annotations of a procedure body, including control-flow graph guards. -/
def bodyAnnotTys (body : Procedure.Body) : List LMonoTy :=
  bodyCollect exprAnnotTys ([·]) body

/-- The types a procedure writes: its parameter types and the type annotations of its conditions
    and body. -/
def procAnnotTys (proc : Procedure) : List LMonoTy :=
  proc.header.inputs.values ++ proc.header.outputs.values ++
    proc.spec.preconditions.values.flatMap (fun chk => exprAnnotTys chk.expr) ++
    proc.spec.postconditions.values.flatMap (fun chk => exprAnnotTys chk.expr) ++
    bodyAnnotTys proc.body

/-- The type constructor names in the types of the literals of a procedure's conditions and
    body. -/
def procLitTyNames (proc : Procedure) : List String :=
  procCollect exprLitTyNames (fun _ => []) proc

/-- The type names a procedure mentions, given the types `annot` it writes: the type
    constructor names of `annot` and of its literals, and the names of the types its body
    declares. -/
def procTyNames (proc : Procedure) (annot : List LMonoTy) : List String :=
  annot.flatMap getTypeRefs ++ procLitTyNames proc ++
    match proc.body with
    | .structured ss => (Imperative.Block.localTypeDecls ss).map (·.name)
    | .cfg _ => []

/-- The type variables a declaration with type parameters `typeArgs` mentions, given the types
    `annot` it writes: its type parameters and the type variables of `annot`. -/
def declMentionedTyVarsIn (typeArgs : List String) (annot : List LMonoTy) : List String :=
  typeArgs ++ annot.flatMap LMonoTy.freeVars

/-- The type variables a procedure mentions, given the types `annot` it writes. -/
def Procedure.mentionedTyVarsIn (proc : Procedure) (annot : List LMonoTy) :
    List String :=
  declMentionedTyVarsIn proc.header.typeArgs annot

/-- The type variables a procedure mentions in its type parameters and annotations. -/
def Procedure.mentionedTyVars (proc : Procedure) : List String :=
  proc.mentionedTyVarsIn (procAnnotTys proc)

/-- Rename each type parameter of `proc` that starts with a reserved prefix to a fresh name,
    throughout the procedure, and keep the others. The new names avoid the type parameters, the
    type variables of `annot ()`, and the names `avoid ()`. -/
def Procedure.renameReservedTypeArgs (avoid : Unit → List String) (proc : Procedure)
    (annot : Unit → List LMonoTy) : Procedure :=
  renameReservedWith proc.header.typeArgs (fun u => proc.mentionedTyVarsIn (annot u) ++ avoid u)
    proc.renameTypeArgs proc

/-- The type variables a lemma mentions, given the types `annot` it writes. -/
def Lemma.mentionedTyVarsIn (l : Lemma) (annot : List LMonoTy) : List String :=
  declMentionedTyVarsIn l.typeArgs annot

/-- The type variables a lemma mentions in its type parameters and annotations. -/
def Lemma.mentionedTyVars (l : Lemma) : List String :=
  l.mentionedTyVarsIn (exprAnnotTys l.e)

/-- `l` with its type parameters renamed by `ren` throughout, as
    `renameTyArgList` does to the parameter list. -/
def Lemma.renameTypeArgs (l : Lemma) (ren : List (String × String)) : Lemma :=
  { l with typeArgs := renameTyArgList ren l.typeArgs,
           e := mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) l.e }

/-- Rename each type parameter of `l` that starts with a reserved prefix to a
    fresh name, throughout the lemma, and keep the others. The new names avoid
    the type parameters, the type variables of `annot ()` and the type variables
    in scope in `C` and `Env` (`scopeTyVars`). -/
def Lemma.renameReservedTypeArgs (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (l : Lemma) (annot : Unit → List LMonoTy) : Lemma :=
  renameReservedWith l.typeArgs
    (fun u => l.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env)
    l.renameTypeArgs l

/-- The type names of a signature with result type `output` and argument types `inputs`. -/
def sigTyNames (output : LMonoTy) (inputs : LMonoTys) : List String :=
  (output :: inputs).flatMap getTypeRefs

/-- The type names of the signature of `f`. -/
def funcSigTyNames (f : LFunc CoreLParams) : List String :=
  sigTyNames f.output f.inputs.values

/-- The type names in scope when a definition is checked in `C` and `Env`, besides the known
    types: the type synonyms with the type names of their bodies, and the type names of the
    variables in scope and of the factory signatures. -/
def scopeTyNames (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) :
    List String :=
  Env.context.aliases.flatMap (fun al => al.name :: getTypeRefs al.type) ++
    Env.context.types.values.flatMap (fun ty => getTypeRefs ty.toMonoTypeUnsafe) ++
    C.functions.toArray.toList.flatMap funcSigTyNames

/-- The type names of the signatures of the functions of `F'` past the first `n`. -/
def Factory.tyNamesFrom (n : Nat) (F' : Lambda.Factory CoreLParams) : List String :=
  (F'.toArray.extract n).toList.flatMap funcSigTyNames

/-- The set of the type names in scope (`scopeTyNames`), computed on first use. -/
def scopeTyNameThunk (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) :
    Thunk (Std.HashSet String) :=
  Thunk.mk fun _ => .ofList (scopeTyNames C Env)

/-- The rigid renaming for the type parameters `typeArgs` of the definition `name` checked in `C`:
    its constants avoid the registered types, the names of `scope` and `progSigs`, and the names
    `own ()`. The sets and `own` are evaluated only for a polymorphic definition. -/
def rigidNamesAvoiding (C : Core.Expression.TyContext)
    (scope progSigs : Thunk (Std.HashSet String)) (name : String) (own : Unit → List String)
    (typeArgs : List String) : RigidNames :=
  if typeArgs.isEmpty then []
  else
    let s := scope.get
    let q := progSigs.get
    let o : Std.HashSet String := .ofList (own ())
    mintRigidNames name
      (fun n => C.knownTypes.containsName n || s.contains n || q.contains n || o.contains n)
      (C.knownTypes.size + s.size + q.size + o.size) typeArgs

/-- Replace each type variable `σ` renames with its constant. -/
def skolemizeTy (σ : RigidNames) (mty : LMonoTy) : LMonoTy :=
  LMonoTy.subst (Subst.ofNullaryConsts σ) mty

mutual
/-- Map each constant `σ` uses back to the type parameter it stands for. -/
def deskolemizeTy (σ : RigidNames) (mty : LMonoTy) : LMonoTy :=
  match mty with
  | .ftvar x => .ftvar x
  | .bitvec n => .bitvec n
  | .tcons name args =>
    match σ.find? (fun p => p.2 == name) with
    | some p => .ftvar p.1
    | none => .tcons name (deskolemizeTys σ args)
/-- Deskolemize a list of monotypes. -/
def deskolemizeTys (σ : RigidNames) (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | t :: rest => deskolemizeTy σ t :: deskolemizeTys σ rest
end

/-- The context for checking a definition's expressions: the constants of `σ` become known
    types of arity 0, and its parameters become rigid type variables. -/
def addSkolemTypes (C : Core.Expression.TyContext) (σ : RigidNames) :
    Core.Expression.TyContext :=
  { C with knownTypes := σ.foldl (fun ks p => ks.insert p.2 0) C.knownTypes,
           rigidTypeVars := C.rigidTypeVars ++ σ.map Prod.fst }

/-! ## Core source-expression resolution -/

namespace SourceExpr

/-- Constrain the type `ty` inferred at an annotated position to the annotation `ann`, keeping
    the identity of its type variables. -/
def linkAnnot (C : Core.Expression.TyContext) (binder : Bool) (ann ty : LMonoTy)
    (Env : Core.Expression.TyEnv) : Except Format Core.Expression.TyEnv := do
  let (ann, Env) ← ann.typeCheckSource C Env TyVarAdmissibility.notGeneratedOrRigid
  unless LMonoTy.checkNoFutureGenVars ty Env.genEnv.genState do
    throw f!"Resolved annotated type contains a future generated type variable"
  let _ ← ty.typeCheckResolved C TyVarAdmissibility.all
  let S ← Constraints.unify (if binder then [(ty, ann)] else [(ann, ty)]) Env.stateSubstInfo
    |>.mapError format
  .ok (Env.updateSubst S)

/-- The domain of an arrow type. -/
def arrowDomain? : LMonoTy → Option LMonoTy
  | .arrow xty _ => some xty
  | _ => none

/-- Constrain a binder annotation, if written, to the bound variable's inferred type, if known. -/
def linkBinderAnnot (C : Core.Expression.TyContext) (ann ty : Option LMonoTy)
    (Env : Core.Expression.TyEnv) : Except Format Core.Expression.TyEnv :=
  match ann, ty with
  | some ann, some ty => linkAnnot C true ann ty Env
  | _, _ => .ok Env

/-- Constrain each annotation on a free-variable occurrence or binder to the type inferred
    for that occurrence or bound variable. -/
def linkFVarAnnotations
    (C : Core.Expression.TyContext) :
    (source : Core.Expression.Expr) →
      (typed : LExprT CoreLParams.mono) →
      (Env : Core.Expression.TyEnv) →
      Except Format Core.Expression.TyEnv
  | .const _ _, .const _ _, Env => .ok Env
  | .op _ _ _, .op _ _ _, Env => .ok Env
  | .bvar _ _, .bvar _ _, Env => .ok Env
  | .fvar _ x none, .fvar _ y _, Env =>
      if x == y then .ok Env else .error f!"Mismatched free variable during source resolution"
  | .fvar _ x (some ann), .fvar m y _, Env => do
      unless x == y do
        throw f!"Mismatched free variable during source resolution"
      linkAnnot C false ann m.type Env
  | .app _ s₁ s₂, .app _ t₁ t₂, Env
  | .eq _ s₁ s₂, .eq _ t₁ t₂, Env => do
      let Env ← linkFVarAnnotations C s₁ t₁ Env
      linkFVarAnnotations C s₂ t₂ Env
  | .abs _ _ ann source, .abs m _ _ typed, Env => do
      let Env ← linkBinderAnnot C ann (arrowDomain? m.type) Env
      linkFVarAnnotations C source typed Env
  | .quant _ _ _ ann sourceTrigger sourceBody,
      .quant m _ _ _ typedTrigger typedBody, Env => do
      -- A typed quantifier records its bound variable's type.
      let Env ← linkBinderAnnot C ann (some m.type) Env
      let Env ← linkFVarAnnotations C sourceTrigger typedTrigger Env
      linkFVarAnnotations C sourceBody typedBody Env
  | .ite _ sourceCond sourceThen sourceElse,
      .ite _ typedCond typedThen typedElse, Env => do
      let Env ← linkFVarAnnotations C sourceCond typedCond Env
      let Env ← linkFVarAnnotations C sourceThen typedThen Env
      linkFVarAnnotations C sourceElse typedElse Env
  | _, _, _ => .error f!"Mismatched expression shape during source resolution"

/-- The first binder annotation in `e` that names a type variable in the generator or rigid
    namespace. -/
def reservedBinderAnnot? (e : Core.Expression.Expr) : Option LMonoTy :=
  (LExpr.binderAnnotations e).find? fun ty =>
    !ty.freeVars.all TyVarAdmissibility.notGeneratedOrRigid

/-- Resolve a Core source expression, keeping the identity of type variables written on
    free-variable occurrences and binders. Binder annotations naming generator or rigid type
    variables are rejected. -/
def resolve
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) :
    Except Format (LExprT CoreLParams.mono × Core.Expression.TyEnv) := do
  if let some ty := reservedBinderAnnot? e then
    throw f!"Binder annotation {ty} contains a free type variable that is not admissible here."
  let (typed, Env) ← LExpr.resolve C Env e
  let Env ← linkFVarAnnotations C e typed Env
  .ok (typed, Env)

/-- Resolve Core source expressions from left to right, threading the inference state. -/
def resolves
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) :
    List Core.Expression.Expr →
      Except Format (List (LExprT CoreLParams.mono) × Core.Expression.TyEnv)
  | [] => .ok ([], Env)
  | e :: es => do
      let (typed, Env) ← resolve C Env e
      let (typedRest, Env) ← resolves C Env es
      .ok (typed :: typedRest, Env)

/-- The result of `act`; if `act` fails and the free-variable check `freeVarErr` also fails,
    the free-variable error instead. Resolution rejects every expression with a free variable
    its context does not bind, so the check runs only when resolution fails and its error still
    takes priority. -/
def orFreeVarError {ε α : Type} (freeVarErr : Unit → Except ε Unit) (act : Except ε α) :
    Except ε α :=
  match act with
  | .ok a => .ok a
  | .error err =>
    match freeVarErr () with
    | .error fvErr => .error fvErr
    | .ok () => .error err

end SourceExpr

/-- Which step of `resolveWithType` rejected the expression. -/
inductive ResolveWithTypeError where
  /-- Elaboration itself failed, with the message it reported. -/
  | resolveFailed (e : Format)
  /-- The elaborated type `resolvedTy`, under elaboration's own substitution, did not unify
      with the expected type; `e` is the unifier's error. -/
  | unifyFailed (e : UnifyError) (resolvedTy : LMonoTy)

/-- Resolve `e` and unify its type with `expected`. The returned environment carries the
    unifier's substitution, which a caller must apply to the elaborated expression. -/
def resolveWithType (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (expected : LMonoTy) :
    Except ResolveWithTypeError (LExprT CoreLParams.mono × Core.Expression.TyEnv) := do
  let (et, Env) ← (SourceExpr.resolve C Env e).mapError ResolveWithTypeError.resolveFailed
  let S ← (Constraints.unify [(et.toLMonoTy, expected)] Env.stateSubstInfo).mapError
    (fun err => .unifyFailed err
      (LMonoTy.subst Env.stateSubstInfo.subst et.toLMonoTy))
  .ok (et, Env.updateSubst S)

/-! ## Annotation maps and sweeps -/


/-- Skolemize the annotations of `e`, leaving each operator annotation unchanged unless the
    operator is `selfName`. -/
def skolemizeBody (selfName : Option String) (σ : RigidNames)
    (e : Core.Expression.Expr) : Core.Expression.Expr :=
  LExpr.replaceUserProvidedType e (skolemizeTy σ)
    (fun o uty => if selfName == some o.name then uty.map (skolemizeTy σ) else uty)

/-- `skolemizeBody nm σ` on each expression of a command; an `.init`'s declared type is
    skolemized too. -/
def skolemizeCmd (nm : Option String) (σ : RigidNames) (c : Command) : Command :=
  mapCmdWith (skolemizeBody nm σ) (skolemizeTy σ) c

/-- Skolemize the type annotations in a statement as `skolemizeCmd` does. -/
def skolemizeStmt (nm : Option String) (σ : RigidNames) (s : Statement) : Statement :=
  Stmt.mapExpr (skolemizeBody nm σ) (skolemizeCmd nm σ) s

/-- Skolemize the type annotations in a list of statements. -/
def skolemizeStmts (nm : Option String) (σ : RigidNames) (ss : List Statement) :
    List Statement :=
  Block.mapExpr (skolemizeBody nm σ) (skolemizeCmd nm σ) ss

/-- The deskolemized form of a type, skipping the walk when `σ` renames nothing. -/
def deskolemizeTyIf (σ : RigidNames) (ty : LMonoTy) : LMonoTy :=
  if σ.isEmpty then ty else deskolemizeTy σ ty

/-- An elaborated expression with `S` applied and each rigid constant of `σ` written back as the
    type variable it stands for, together with whether every annotation of the result satisfies
    `ok`. -/
def finishStored (σ : RigidNames) (S : Subst) (ok : LMonoTy → Bool) :
    LExprT CoreLParams.mono → Core.Expression.Expr × Bool
  | .const m c => (.const m.underlying c, true)
  | .op m o _ =>
    let ty := deskolemizeTyIf σ (LMonoTy.subst S m.type)
    (.op m.underlying o (some ty), ok ty)
  | .bvar m b => (.bvar m.underlying b, true)
  | .fvar m x _ =>
    let ty := deskolemizeTyIf σ (LMonoTy.subst S m.type)
    (.fvar m.underlying x (some ty), ok ty)
  | .app m e1 e2 =>
    let (e1', b1) := finishStored σ S ok e1
    let (e2', b2) := finishStored σ S ok e2
    (.app m.underlying e1' e2', b1 && b2)
  | .abs m name t e =>
    -- The binder takes the domain of the stored type when that type is an arrow.
    let ann := match (LMonoTy.subst S m.type).isArrow with
      | some (aty, _) => some (deskolemizeTyIf σ aty)
      | none => t.map (deskolemizeTyIf σ)
    let (e', b) := finishStored σ S ok e
    (.abs m.underlying name ann e', ann.all ok && b)
  | .quant m qk name _ tr e =>
    let ty := deskolemizeTyIf σ (LMonoTy.subst S m.type)
    let (tr', b1) := finishStored σ S ok tr
    let (e', b2) := finishStored σ S ok e
    (.quant m.underlying qk name (some ty) tr' e', ok ty && b1 && b2)
  | .ite m c t f =>
    let (c', b1) := finishStored σ S ok c
    let (t', b2) := finishStored σ S ok t
    let (f', b3) := finishStored σ S ok f
    (.ite m.underlying c' t' f', b1 && b2 && b3)
  | .eq m e1 e2 =>
    let (e1', b1) := finishStored σ S ok e1
    let (e2', b2) := finishStored σ S ok e2
    (.eq m.underlying e1' e2', b1 && b2)

/-- Is every free type variable of `ty` one of `ps`? -/
def tyVarsIn (ps : List TyIdentifier) (ty : LMonoTy) : Bool :=
  ty.freeVars.all ps.contains

end Core

end -- public section
