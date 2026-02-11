/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Options
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.HeapParameterization
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp)

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LTy LExpr)

def intDivTOp : Core.Expression.Expr :=
  .op () (Core.CoreIdent.unres "Int.DivT") (some (LMonoTy.arrow LMonoTy.int (LMonoTy.arrow LMonoTy.int LMonoTy.int)))

def intModTOp : Core.Expression.Expr :=
  .op () (Core.CoreIdent.unres "Int.ModT") (some (LMonoTy.arrow LMonoTy.int (LMonoTy.arrow LMonoTy.int LMonoTy.int)))

/-- Map from constrained type name to its definition -/
abbrev ConstrainedTypeMap := Std.HashMap Identifier ConstrainedType

/-- Pre-translated constraint: base type and Core expression with free variable for the value -/
structure TranslatedConstraint where
  base : HighType
  valueName : Identifier
  /-- Core expression for constraint, with valueName as free variable -/
  coreConstraint : Core.Expression.Expr

/-- Map from constrained type name to pre-translated constraint -/
abbrev TranslatedConstraintMap := Std.HashMap Identifier TranslatedConstraint

/-- Build a map of constrained types from a program -/
def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with
    | .Constrained ct => m.insert ct.name ct
    | _ => m

/-- Get the base type for a type, resolving constrained types -/
partial def resolveBaseType (ctMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name =>
    match ctMap.get? name with
    | some ct => resolveBaseType ctMap ct.base.val
    | none => ty
  | .Applied ctor args =>
    .Applied ctor (args.map fun arg => ⟨resolveBaseType ctMap arg.val, arg.md⟩)
  | _ => ty

/-
Translate Laurel HighType to Core Type
-/
private theorem HighTypeMd.sizeOf_val_lt (e : HighTypeMd) : sizeOf e.val < sizeOf e := by
  cases e <;> simp_wf <;> omega

/-- Tactic for proving termination of functions that recurse on `StmtExprMd` sub-terms.
    Handles direct sub-terms and list elements of the matched constructor. -/
macro "stmtexpr_wf " e:ident ", " h:ident : tactic =>
  `(tactic| (
    all_goals (cases $e:ident; subst $h:ident; simp_wf)
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_›; omega)))

def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TString => LMonoTy.string
  | .TVoid => LMonoTy.bool
  | .THeap => .tcons "Heap" []
  | .TTypedField valueType => .tcons "Field" [translateType valueType.val]
  | .Applied ctor [elemTy] =>
    match ctor.val with
    | .UserDefined "Array" => .tcons "Array" [translateType elemTy.val]
    | _ => panic s!"unsupported applied type {repr ty}"
  | .UserDefined _ => .tcons "Composite" []
  | .TCore s => .tcons s []
  | _ => panic s!"unsupported type {repr ty}"
termination_by sizeOf ty
decreasing_by all_goals simp_wf; have := HighTypeMd.sizeOf_val_lt ‹_›; omega

/-- Translate type, resolving constrained types to their base type recursively -/
def translateTypeWithCT (ctMap : ConstrainedTypeMap) (ty : HighType) : LMonoTy :=
  match ty with
  | .Applied ctor [elemTy] =>
    match ctor.val with
    | .UserDefined "Array" => .tcons "Array" [translateTypeWithCT ctMap elemTy.val]
    | _ => translateType (resolveBaseType ctMap ty)
  | _ => translateType (resolveBaseType ctMap ty)
termination_by sizeOf ty
decreasing_by all_goals simp_wf; have := HighTypeMd.sizeOf_val_lt ‹_›; omega

/-- Translate HighTypeMd, extracting the value -/
def translateTypeMdWithCT (ctMap : ConstrainedTypeMap) (ty : HighTypeMd) : LMonoTy :=
  translateTypeWithCT ctMap ty.val

abbrev TypeEnv := List (Identifier × HighTypeMd)

def lookupType (ctMap : ConstrainedTypeMap) (env : TypeEnv) (name : Identifier) : Except String LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => pure (translateTypeMdWithCT ctMap ty)
  | none => throw s!"Unknown identifier: {name}"

/-- Sequence bounds: array with start (inclusive) and end (exclusive) indices -/
structure SeqBounds where
  arr : Core.Expression.Expr   -- the underlying array
  start : Core.Expression.Expr -- start index (inclusive)
  «end» : Core.Expression.Expr -- end index (exclusive)
deriving Inhabited

/-- Expand array argument to include length parameter.
    Note: Only works when the argument is a simple Identifier; complex expressions are passed through unchanged. -/
def expandArrayArgs (env : TypeEnv) (args : List StmtExprMd) (translatedArgs : List Core.Expression.Expr) : List Core.Expression.Expr :=
  (args.zip translatedArgs).flatMap fun (arg, translated) =>
    match arg.val with
    | .Identifier arrName =>
      match env.find? (fun (n, _) => n == arrName) with
      | some (_, ty) =>
        match ty.val with
        | .Applied ctor _ =>
          match ctor.val with
          | .UserDefined "Array" => [translated, .fvar () (Core.CoreIdent.locl (arrName ++ "_len")) (some LMonoTy.int)]
          | _ => [translated]
        | _ => [translated]
      | _ => [translated]
    | _ => [translated]

/-- Translate a binary operation to Core -/
def translateBinOp (op : Operation) (e1 e2 : Core.Expression.Expr) : Except String Core.Expression.Expr :=
  let binOp (bop : Core.Expression.Expr) := LExpr.mkApp () bop [e1, e2]
  match op with
  | .Eq => pure (.eq () e1 e2)
  | .Neq => pure (.app () boolNotOp (.eq () e1 e2))
  | .And => pure (binOp boolAndOp) | .Or => pure (binOp boolOrOp)
  | .Implies => pure (binOp boolImpliesOp)
  | .Add => pure (binOp intAddOp) | .Sub => pure (binOp intSubOp) | .Mul => pure (binOp intMulOp)
  | .Div => pure (binOp intDivOp) | .Mod => pure (binOp intModOp)
  | .DivT => pure (binOp intDivTOp) | .ModT => pure (binOp intModTOp)
  | .Lt => pure (binOp intLtOp) | .Leq => pure (binOp intLeOp) | .Gt => pure (binOp intGtOp) | .Geq => pure (binOp intGeOp)
  | _ => throw s!"translateBinOp: unsupported {repr op}"

/-- Translate a unary operation to Core -/
def translateUnaryOp (op : Operation) (e : Core.Expression.Expr) : Except String Core.Expression.Expr :=
  match op with
  | .Not => pure (.app () boolNotOp e)
  | .Neg => pure (.app () intNegOp e)
  | _ => throw s!"translateUnaryOp: unsupported {repr op}"

def isHeapFunction (name : Identifier) : Bool :=
  name == "heapRead" || name == "heapStore"

/-- Translate simple expressions (for constraints - no quantifiers) -/
def translateSimpleExpr (ctMap : ConstrainedTypeMap) (env : TypeEnv) (expr : StmtExprMd) : Except String Core.Expression.Expr :=
  match _h : expr.val with
  | .LiteralBool b => pure (.const () (.boolConst b))
  | .LiteralInt i => pure (.const () (.intConst i))
  | .LiteralString s => pure (.const () (.strConst s))
  | .Identifier name => do
      let ty ← lookupType ctMap env name
      pure (.fvar () (Core.CoreIdent.locl name) (some ty))
  | .PrimitiveOp op [e] => do
      let e' ← translateSimpleExpr ctMap env e
      translateUnaryOp op e'
  | .PrimitiveOp op [e1, e2] => do
      let e1' ← translateSimpleExpr ctMap env e1
      let e2' ← translateSimpleExpr ctMap env e2
      translateBinOp op e1' e2'
  | .Forall _ _ _ => throw "Quantifiers not supported in constrained type constraints"
  | .Exists _ _ _ => throw "Quantifiers not supported in constrained type constraints"
  | _ => throw "Unsupported expression in constrained type constraint"
termination_by sizeOf expr
decreasing_by stmtexpr_wf expr, _h

/-- Build map of pre-translated constraints -/
def buildTranslatedConstraintMap (ctMap : ConstrainedTypeMap) : Except String TranslatedConstraintMap :=
  ctMap.foldM (init := {}) fun m name ct => do
    let env : TypeEnv := [(ct.valueName, ct.base)]
    let coreExpr ← translateSimpleExpr ctMap env ct.constraint
    pure (m.insert name { base := ct.base.val, valueName := ct.valueName, coreConstraint := coreExpr })

/-- Close free variable by name, converting fvar to bvar at depth k -/
def varCloseByName (k : Nat) (x : Core.CoreIdent) (e : Core.Expression.Expr) : Core.Expression.Expr :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y yty => if x == y then .bvar m k else .fvar m y yty
  | .abs m ty e' => .abs m ty (varCloseByName (k + 1) x e')
  | .quant m qk ty tr e' => .quant m qk ty (varCloseByName (k + 1) x tr) (varCloseByName (k + 1) x e')
  | .app m e1 e2 => .app m (varCloseByName k x e1) (varCloseByName k x e2)
  | .ite m c t f => .ite m (varCloseByName k x c) (varCloseByName k x t) (varCloseByName k x f)
  | .eq m e1 e2 => .eq m (varCloseByName k x e1) (varCloseByName k x e2)

/-- Translate simple expression (identifier or literal) to Core - for sequence bounds -/
def translateSimpleBound (expr : StmtExprMd) : Except String Core.Expression.Expr :=
  match expr.val with
  | .Identifier name => pure (.fvar () (Core.CoreIdent.locl name) (some LMonoTy.int))
  | .LiteralInt i => pure (.const () (.intConst i))
  | _ => throw "Expected simple bound expression (identifier or literal)"

/-- Normalize callee name by removing «» quotes if present -/
def normalizeCallee (callee : Identifier) : Identifier :=
  if callee.startsWith "«" && callee.endsWith "»" then
    (callee.drop 1 |>.dropEnd 1).toString
  else
    callee

/-- Extract sequence bounds from Seq.From/Take/Drop chain.
    Note: Seq.From only works with simple Identifier arguments; complex expressions are not supported. -/
def translateSeqBounds (env : TypeEnv) (expr : StmtExprMd) : Except String SeqBounds :=
  match _h : expr.val with
  | .StaticCall callee [arr] =>
      if normalizeCallee callee == "Seq.From" then
        match arr.val with
        | .Identifier name =>
            -- Validate that name is an array
            match env.find? (fun (n, _) => n == name) with
            | some (_, ty) =>
              match ty.val with
              | .Applied ctor _ =>
                match ctor.val with
                | .UserDefined "Array" =>
                    pure { arr := .fvar () (Core.CoreIdent.locl name) none
                         , start := .const () (.intConst 0)
                         , «end» := .fvar () (Core.CoreIdent.locl (name ++ "_len")) (some LMonoTy.int) }
                | _ => throw s!"Seq.From expects array, got {repr ty}"
              | _ => throw s!"Seq.From expects array, got {repr ty}"
            | none => throw s!"Unknown identifier in Seq.From: {name}"
        | _ => throw "Seq.From on complex expressions not supported"
      else
        throw s!"Not a sequence expression: {callee}"
  | .StaticCall callee [seq, n] =>
      let norm := normalizeCallee callee
      if norm == "Seq.Take" then do
        let inner ← translateSeqBounds env seq
        let bound ← translateSimpleBound n
        pure { inner with «end» := bound }
      else if norm == "Seq.Drop" then do
        let inner ← translateSeqBounds env seq
        let bound ← translateSimpleBound n
        pure { inner with start := bound }
      else
        throw s!"Not a sequence expression: {callee}"
  | _ => throw "Not a sequence expression"
termination_by sizeOf expr
decreasing_by stmtexpr_wf expr, _h

/-- Inject constraint into quantifier body. For forall uses ==>, for exists uses &&. -/
def injectQuantifierConstraint (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap)
    (isForall : Bool) (ty : HighTypeMd) (coreIdent : Core.CoreIdent) (closedBody : Core.Expression.Expr) : Core.Expression.Expr :=
  match ty.val with
  | .UserDefined typeName => match tcMap.get? typeName with
    | some tc =>
        let substConstraint := tc.coreConstraint.substFvar (Core.CoreIdent.locl tc.valueName)
          (.fvar () coreIdent (some (translateTypeMdWithCT ctMap ty)))
        let op := if isForall then boolImpliesOp else boolAndOp
        LExpr.mkApp () op [varCloseByName 0 coreIdent substConstraint, closedBody]
    | none => closedBody
  | _ => closedBody

/--
Translate Laurel StmtExpr to Core Expression
-/
def translateExpr (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (env : TypeEnv) (expr : StmtExprMd) : Except String Core.Expression.Expr :=
  match _h : expr.val with
  | .LiteralBool b => pure (.const () (.boolConst b))
  | .LiteralInt i => pure (.const () (.intConst i))
  | .LiteralString s => pure (.const () (.strConst s))
  | .Identifier name => do
        -- Check if it's in the environment
        match env.find? (fun (n, _) => n == name) with
        | some (_, ty) =>
            -- Check if it's a field constant (TTypedField type)
            match ty.val with
            | .TTypedField _ =>
                -- Field constants are nullary functions, translate as global op
                pure (.op () (Core.CoreIdent.glob name) none)
            | _ =>
                let coreTy := translateTypeMdWithCT ctMap ty
                pure (.fvar () (Core.CoreIdent.locl name) (some coreTy))
        | none =>
            -- Not in env - assume it's a global constant
            pure (.op () (Core.CoreIdent.glob name) none)
  | .PrimitiveOp op [e] => do
      let e' ← translateExpr ctMap tcMap env e
      translateUnaryOp op e'
  | .PrimitiveOp op [e1, e2] => do
      let e1' ← translateExpr ctMap tcMap env e1
      let e2' ← translateExpr ctMap tcMap env e2
      translateBinOp op e1' e2'
  | .PrimitiveOp op args =>
    throw s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch => do
      let bcond ← translateExpr ctMap tcMap env cond
      let bthen ← translateExpr ctMap tcMap env thenBranch
      let belse ← match elseBranch with
                  | some e => translateExpr ctMap tcMap env e
                  | none => pure (.const () (.intConst 0))
      pure (.ite () bcond bthen belse)
  | .Assign _ value => translateExpr ctMap tcMap env value
  | .StaticCall callee [arg] =>
      let norm := normalizeCallee callee
      if norm == "Array.Length" then
        match arg.val with
        | .Identifier name => pure (.fvar () (Core.CoreIdent.locl (name ++ "_len")) (some LMonoTy.int))
        | _ => throw "Array.Length on complex expressions not supported"
      else do
        let calleeOp := LExpr.op () (Core.CoreIdent.glob norm) none
        let translated ← translateExpr ctMap tcMap env arg
        let expandedArgs := expandArrayArgs env [arg] [translated]
        pure (expandedArgs.foldl (fun acc a => .app () acc a) calleeOp)
  | .StaticCall callee [arg1, arg2] =>
      let norm := normalizeCallee callee
      if norm == "Array.Get" then do
        let arrExpr ← translateExpr ctMap tcMap env arg1
        let idxExpr ← translateExpr ctMap tcMap env arg2
        -- Note: Element type constraints (e.g., Array<int32>) are not currently enforced on access
        let selectOp := LExpr.op () (Core.CoreIdent.unres "select") none
        pure (LExpr.mkApp () selectOp [arrExpr, idxExpr])
      else if norm == "Seq.Contains" then do
        -- exists i :: start <= i < end && arr[i] == elem
        let bounds ← translateSeqBounds env arg1
        let elemExpr ← translateExpr ctMap tcMap env arg2
        let i := LExpr.bvar () 0
        -- start <= i
        let geStart := LExpr.mkApp () intLeOp [bounds.start, i]
        -- i < end
        let ltEnd := LExpr.mkApp () intLtOp [i, bounds.«end»]
        -- arr[i]
        let selectOp := LExpr.op () (Core.CoreIdent.unres "select") none
        let arrAtI := LExpr.mkApp () selectOp [bounds.arr, i]
        -- arr[i] == elem
        let eqElem := LExpr.eq () arrAtI elemExpr
        -- start <= i && i < end && arr[i] == elem
        let body := LExpr.mkApp () boolAndOp [geStart, LExpr.mkApp () boolAndOp [ltEnd, eqElem]]
        pure (LExpr.quant () .exist (some LMonoTy.int) (LExpr.noTrigger ()) body)
      else do
        -- Default: treat as function call with array expansion
        let calleeOp := LExpr.op () (Core.CoreIdent.glob norm) none
        let e1 ← translateExpr ctMap tcMap env arg1
        let e2 ← translateExpr ctMap tcMap env arg2
        let expandedArgs := expandArrayArgs env [arg1, arg2] [e1, e2]
        pure (expandedArgs.foldl (fun acc a => .app () acc a) calleeOp)
  | .StaticCall name args => do
      let normName := normalizeCallee name
      -- Use glob for all functions including heap functions
      let fnIdent := Core.CoreIdent.glob normName
      let fnOp := LExpr.op () fnIdent none
      let translatedArgs ← args.attach.mapM fun ⟨a, _⟩ => translateExpr ctMap tcMap env a
      let expandedArgs := expandArrayArgs env args translatedArgs
      pure (expandedArgs.foldl (fun acc a => .app () acc a) fnOp)
  | .ReferenceEquals e1 e2 => do
      let e1' ← translateExpr ctMap tcMap env e1
      let e2' ← translateExpr ctMap tcMap env e2
      pure (.eq () e1' e2')
  | .Block [single] _ => translateExpr ctMap tcMap env single
  | .Forall _name ty body => do
      let coreType := translateTypeMdWithCT ctMap ty
      let env' := (_name, ty) :: env
      let bodyExpr ← translateExpr ctMap tcMap env' body
      let coreIdent := Core.CoreIdent.locl _name
      let closedBody := varCloseByName 0 coreIdent bodyExpr
      let finalBody := injectQuantifierConstraint ctMap tcMap true ty coreIdent closedBody
      pure (LExpr.quant () .all (some coreType) (LExpr.noTrigger ()) finalBody)
  | .Exists _name ty body => do
      let coreType := translateTypeMdWithCT ctMap ty
      let env' := (_name, ty) :: env
      let bodyExpr ← translateExpr ctMap tcMap env' body
      let coreIdent := Core.CoreIdent.locl _name
      let closedBody := varCloseByName 0 coreIdent bodyExpr
      let finalBody := injectQuantifierConstraint ctMap tcMap false ty coreIdent closedBody
      pure (LExpr.quant () .exist (some coreType) (LExpr.noTrigger ()) finalBody)
  | .Return (some e) => translateExpr ctMap tcMap env e
  | _ => throw s!"translateExpr: unsupported {Std.Format.pretty (Std.ToFormat.format expr.val)}"
termination_by sizeOf expr
decreasing_by stmtexpr_wf expr, _h

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.range.start})"

def genConstraintCheck (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (param : Parameter) : Option Core.Expression.Expr :=
  match param.type.val with
  | .UserDefined name =>
    match tcMap.get? name with
    | some tc =>
      let paramIdent := Core.CoreIdent.locl param.name
      let valueIdent := Core.CoreIdent.locl tc.valueName
      let baseTy := translateTypeMdWithCT ctMap param.type
      some (tc.coreConstraint.substFvar valueIdent (.fvar () paramIdent (some baseTy)))
    | none => none
  | _ => none

def genConstraintAssert (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (name : Identifier) (ty : HighTypeMd) : List Core.Statement :=
  match genConstraintCheck ctMap tcMap { name, type := ty } with
  | some expr => [Core.Statement.assert s!"{name}_constraint" expr ty.md]
  | none => []

def defaultExprForType (ctMap : ConstrainedTypeMap) (ty : HighTypeMd) : Core.Expression.Expr :=
  let resolved := resolveBaseType ctMap ty.val
  match resolved with
  | .TInt => .const () (.intConst 0)
  | .TBool => .const () (.boolConst false)
  | .TString => .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy := translateType resolved
    .fvar () (Core.CoreIdent.locl "$default") (some coreTy)

/-- Check if a StaticCall should be translated as an expression (not a procedure call) -/
def isExpressionCall (callee : Identifier) : Bool :=
  let norm := normalizeCallee callee
  isHeapFunction norm || norm.startsWith "Seq." || norm.startsWith "Array."

/--
Get element type name if `arr` is `Array<ConstrainedType>` (identifier only).
Generates assumes for constrained array accesses. Limitation: no `obj.field[i]`.
-/
def getArrayElemConstrainedType (env : TypeEnv) (arr : StmtExprMd) : Option Identifier :=
  match arr.val with
  | .Identifier name =>
    if let some (_, { val := .Applied { val := .UserDefined "Array", ..} [{ val := .UserDefined elemName, ..}], ..}) := env.find? (fun (n, _) => n == name) then
      some elemName
    else none
  | _ => none

/-- Collect Array.Get accesses with constrained element types -/
def collectConstrainedArrayAccesses (env : TypeEnv) (tcMap : TranslatedConstraintMap) (e : StmtExprMd) : List (StmtExprMd × StmtExprMd × TranslatedConstraint) :=
  match _h : e.val with
  | .StaticCall callee [arr, idx] =>
    let sub := collectConstrainedArrayAccesses env tcMap arr ++ collectConstrainedArrayAccesses env tcMap idx
    if normalizeCallee callee == "Array.Get" then
      match getArrayElemConstrainedType env arr >>= tcMap.get? with
      | some tc => (arr, idx, tc) :: sub
      | none => sub
    else sub
  | .PrimitiveOp _ args | .StaticCall _ args =>
    args.attach.flatMap fun ⟨a, _⟩ => collectConstrainedArrayAccesses env tcMap a
  | .IfThenElse c t el =>
    collectConstrainedArrayAccesses env tcMap c ++
    collectConstrainedArrayAccesses env tcMap t ++
    (match el with | some x => collectConstrainedArrayAccesses env tcMap x | none => [])
  | .Assign ts v =>
    ts.attach.flatMap (fun ⟨a, _⟩ => collectConstrainedArrayAccesses env tcMap a) ++
    collectConstrainedArrayAccesses env tcMap v
  | .Return (some v) | .Assert v | .Assume v => collectConstrainedArrayAccesses env tcMap v
  | .LocalVariable _ _ (some init) => collectConstrainedArrayAccesses env tcMap init
  | _ => []
termination_by sizeOf e
decreasing_by stmtexpr_wf e, _h

/-- Generate assume statements for constrained array element accesses -/
def genArrayElemAssumes (tcMap : TranslatedConstraintMap) (env : TypeEnv) (expr : StmtExprMd)
    (translateExprFn : StmtExprMd → Except String Core.Expression.Expr) : Except String (List Core.Statement) := do
  let accesses := collectConstrainedArrayAccesses env tcMap expr
  accesses.mapM fun (arr, idx, tc) => do
    let arrExpr ← translateExprFn arr
    let idxExpr ← translateExprFn idx
    let selectExpr := LExpr.mkApp () (LExpr.op () (Core.CoreIdent.unres "select") none) [arrExpr, idxExpr]
    let constraintExpr := tc.coreConstraint.substFvar (Core.CoreIdent.locl tc.valueName) selectExpr
    pure (Core.Statement.assume "array_elem_constraint" constraintExpr expr.md)

/--
Translate Laurel StmtExpr to Core Statements
Takes the type environment, output parameter names, and postconditions to assert at returns
-/
def translateStmt (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (env : TypeEnv) (outputParams : List Parameter) (postconds : List (String × Core.Expression.Expr)) (stmt : StmtExprMd) : Except String (TypeEnv × List Core.Statement) := do
  -- Generate assumes for constrained array element accesses before the statement
  let arrayElemAssumes ← genArrayElemAssumes tcMap env stmt (translateExpr ctMap tcMap env)
  let mkReturnStmts (valueOpt : Option Core.Expression.Expr) : Except String (TypeEnv × List Core.Statement) := do
    let postAsserts := postconds.map fun (label, expr) => Core.Statement.assert label expr stmt.md
    let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) stmt.md
    match valueOpt, outputParams.head? with
    | some value, some outParam =>
        let assignStmt := Core.Statement.set (Core.CoreIdent.locl outParam.name) value
        pure (env, arrayElemAssumes ++ [assignStmt] ++ postAsserts ++ [noFallThrough])
    | none, _ => pure (env, arrayElemAssumes ++ postAsserts ++ [noFallThrough])
    | some _, none => throw "Return statement with value but procedure has no output parameters"
  match _h : stmt.val with
  | .Assert cond => do
      let coreExpr ← translateExpr ctMap tcMap env cond
      pure (env, arrayElemAssumes ++ [Core.Statement.assert ("assert" ++ getNameFromMd stmt.md) coreExpr stmt.md])
  | .Assume cond => do
      let coreExpr ← translateExpr ctMap tcMap env cond
      pure (env, arrayElemAssumes ++ [Core.Statement.assume ("assume" ++ getNameFromMd stmt.md) coreExpr stmt.md])
  | .Block stmts _ => do
      let mut env' := env
      let mut stmtsList := []
      for s in stmts do
        let (e', ss) ← translateStmt ctMap tcMap env' outputParams postconds s
        env' := e'
        stmtsList := stmtsList ++ ss
      pure (env', stmtsList)
  | .LocalVariable name ty initializer => do
      let env' := (name, ty) :: env
      let coreType := LTy.forAll [] (translateTypeMdWithCT ctMap ty)
      let ident := Core.CoreIdent.locl name
      let constraintCheck := genConstraintAssert ctMap tcMap name ty
      match initializer with
      | some init =>
          match init.val with
          | .StaticCall callee args =>
              if isExpressionCall callee then do
                let coreExpr ← translateExpr ctMap tcMap env init
                pure (env', arrayElemAssumes ++ [Core.Statement.init ident coreType coreExpr] ++ constraintCheck)
              else do
                let coreArgs ← args.mapM (translateExpr ctMap tcMap env)
                let expandedArgs := expandArrayArgs env args coreArgs
                let defaultVal := defaultExprForType ctMap ty
                let initStmt := Core.Statement.init ident coreType defaultVal
                let callStmt := Core.Statement.call [ident] callee expandedArgs
                pure (env', arrayElemAssumes ++ [initStmt, callStmt] ++ constraintCheck)
          | _ => do
              let coreExpr ← translateExpr ctMap tcMap env init
              pure (env', arrayElemAssumes ++ [Core.Statement.init ident coreType coreExpr] ++ constraintCheck)
      | none => do
          let defaultVal := defaultExprForType ctMap ty
          pure (env', arrayElemAssumes ++ [Core.Statement.init ident coreType defaultVal] ++ constraintCheck)
  | .Assign targets value =>
      match targets with
      | [target] =>
        match target.val with
        | .Identifier name => do
            let ident := Core.CoreIdent.locl name
            let constraintCheck :=
              match env.find? (fun (n, _) => n == name) with
              | some (_, ty) => genConstraintAssert ctMap tcMap name ty
              | none => []
            match value.val with
            | .StaticCall callee args =>
                if isExpressionCall callee then do
                  let coreExpr ← translateExpr ctMap tcMap env value
                  pure (env, arrayElemAssumes ++ [Core.Statement.set ident coreExpr] ++ constraintCheck)
                else do
                  let coreArgs ← args.mapM (translateExpr ctMap tcMap env)
                  let expandedArgs := expandArrayArgs env args coreArgs
                  pure (env, arrayElemAssumes ++ [Core.Statement.call [ident] callee expandedArgs] ++ constraintCheck)
            | _ => do
                let coreExpr ← translateExpr ctMap tcMap env value
                pure (env, arrayElemAssumes ++ [Core.Statement.set ident coreExpr] ++ constraintCheck)
        | _ => throw s!"translateStmt: unsupported assignment target {Std.Format.pretty (Std.ToFormat.format target.val)}"
      | _ =>
        -- Multi-target assignment: (var1, var2, ...) := call(args)
        match value.val with
        | .StaticCall callee args => do
            let lhsIdents := targets.filterMap fun t =>
              match t.val with
              | .Identifier name => some (Core.CoreIdent.locl name)
              | _ => none
            let coreArgs ← args.mapM (translateExpr ctMap tcMap env)
            let expandedArgs := expandArrayArgs env args coreArgs
            pure (env, arrayElemAssumes ++ [Core.Statement.call lhsIdents callee expandedArgs])
        | _ => throw "Assignments with multiple targets but without a RHS call should not be constructed"
  | .IfThenElse cond thenBranch elseBranch => do
      let bcond ← translateExpr ctMap tcMap env cond
      let (_, bthen) ← translateStmt ctMap tcMap env outputParams postconds thenBranch
      let belse ← match elseBranch with
                  | some e => do let (_, s) ← translateStmt ctMap tcMap env outputParams postconds e; pure s
                  | none => pure []
      pure (env, arrayElemAssumes ++ [Imperative.Stmt.ite bcond bthen belse stmt.md])
  | .While cond invariants _decOpt body => do
      let condExpr ← translateExpr ctMap tcMap env cond
      -- Combine multiple invariants with && for Core (which expects single invariant)
      let invExpr ← match invariants with
        | [] => pure none
        | [single] => do let e ← translateExpr ctMap tcMap env single; pure (some e)
        | first :: rest => do
            let firstExpr ← translateExpr ctMap tcMap env first
            let combined ← rest.foldlM (fun acc inv => do
              let invExpr ← translateExpr ctMap tcMap env inv
              pure (LExpr.mkApp () boolAndOp [acc, invExpr])) firstExpr
            pure (some combined)
      let (_, bodyStmts) ← translateStmt ctMap tcMap env outputParams postconds body
      pure (env, arrayElemAssumes ++ [Imperative.Stmt.loop condExpr none invExpr bodyStmts stmt.md])
  | .StaticCall name args => do
      if isHeapFunction (normalizeCallee name) then pure (env, arrayElemAssumes)
      else do
        let coreArgs ← args.mapM (translateExpr ctMap tcMap env)
        let expandedArgs := expandArrayArgs env args coreArgs
        pure (env, arrayElemAssumes ++ [Core.Statement.call [] name expandedArgs])
  | .Return valueOpt => do
      match valueOpt with
      | some value => do
          let coreExpr ← translateExpr ctMap tcMap env value
          mkReturnStmts (some coreExpr)
      | none => mkReturnStmts none
  | _ =>
      -- Expression-like statements: treat as implicit return if output param exists
      match outputParams.head? with
      | some _ => do
          let coreExpr ← translateExpr ctMap tcMap env stmt
          mkReturnStmts (some coreExpr)
      | none => pure (env, [])  -- No output param - ignore expression result
termination_by sizeOf stmt
decreasing_by stmtexpr_wf stmt, _h

/-- Translate parameter with constrained type resolution -/
def translateParameterToCoreWithCT (ctMap : ConstrainedTypeMap) (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := Core.CoreIdent.locl param.name
  let ty := translateTypeMdWithCT ctMap param.type
  (ident, ty)

/-- Expand array parameter to (arr, arr_len) pair -/
def expandArrayParam (ctMap : ConstrainedTypeMap) (param : Parameter) : List (Core.CoreIdent × LMonoTy) :=
  match param.type.val with
  | .Applied ctor _ =>
    match ctor.val with
    | .UserDefined "Array" =>
        [ (Core.CoreIdent.locl param.name, translateTypeMdWithCT ctMap param.type)
        , (Core.CoreIdent.locl (param.name ++ "_len"), LMonoTy.int) ]
    | _ => [translateParameterToCoreWithCT ctMap param]
  | _ => [translateParameterToCoreWithCT ctMap param]

/--
Translate Laurel Procedure to Core Procedure
-/
def translateProcedure (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap)
  (constants : List Constant) (_heapWriters : List Identifier) (proc : Procedure) : Except String Core.Decl := do
  let inputs := proc.inputs.flatMap (expandArrayParam ctMap)
  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := proc.outputs.flatMap (expandArrayParam ctMap)
  }
  -- Build type environment with original types (for constraint checks)
  -- Include array length parameters
  let arrayLenEnv : TypeEnv := proc.inputs.filterMap (fun p =>
    match p.type.val with
    | .Applied ctor _ =>
      match ctor.val with
      | .UserDefined "Array" => some (p.name ++ "_len", ⟨.TInt, p.type.md⟩)
      | _ => none
    | _ => none)
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           arrayLenEnv ++
                           constants.map (fun c => (c.name, c.type))
  -- Generate constraint checks for input parameters with constrained types
  let inputConstraints : List (Core.CoreLabel × Core.Procedure.Check) ←
    proc.inputs.filterMapM (fun p => do
      match genConstraintCheck ctMap tcMap p with
      | some expr => pure (some (s!"{proc.name}_input_{p.name}_constraint", { expr, md := p.type.md }))
      | none => pure none)
  -- Array lengths are implicitly >= 0
  let arrayLenConstraints : List (Core.CoreLabel × Core.Procedure.Check) :=
    proc.inputs.filterMap (fun p =>
      match p.type.val with
      | .Applied ctor _ =>
        match ctor.val with
        | .UserDefined "Array" =>
          let lenVar := LExpr.fvar () (Core.CoreIdent.locl (p.name ++ "_len")) (some LMonoTy.int)
          let zero := LExpr.intConst () 0
          let geZero := LExpr.mkApp () intLeOp [zero, lenVar]
          some (s!"{proc.name}_input_{p.name}_len_constraint", { expr := geZero, md := p.type.md })
        | _ => none
      | _ => none)
  -- Translate explicit preconditions
  let mut explicitPreconditions : List (Core.CoreLabel × Core.Procedure.Check) := []
  for h : i in [:proc.preconditions.length] do
    let precond := proc.preconditions[i]
    let expr ← translateExpr ctMap tcMap initEnv precond
    let check : Core.Procedure.Check := { expr, md := precond.md }
    explicitPreconditions := explicitPreconditions ++ [(s!"{proc.name}_pre_{i}", check)]
  let preconditions := inputConstraints ++ arrayLenConstraints ++ explicitPreconditions
  -- Generate constraint checks for output parameters with constrained types
  let outputConstraints : List (Core.CoreLabel × Core.Procedure.Check) ←
    proc.outputs.filterMapM (fun p => do
      match genConstraintCheck ctMap tcMap p with
      | some expr => pure (some (s!"{proc.name}_output_{p.name}_constraint", { expr, md := p.type.md }))
      | none => pure none)
  -- Translate explicit postconditions for Opaque bodies
  let mut explicitPostconditions : List (Core.CoreLabel × Core.Procedure.Check) := []
  match proc.body with
  | .Opaque posts _ _ =>
      for h : i in [:posts.length] do
        let postcond := posts[i]
        let expr ← translateExpr ctMap tcMap initEnv postcond
        let check : Core.Procedure.Check := { expr, md := postcond.md }
        explicitPostconditions := explicitPostconditions ++ [(s!"{proc.name}_post_{i}", check)]
  | _ => pure ()
  let postconditions := explicitPostconditions ++ outputConstraints
  -- Extract postcondition expressions for early return checking
  let postcondExprs : List (String × Core.Expression.Expr) :=
    postconditions.map fun (label, check) => (label, check.expr)
  -- Heap is now passed as parameters ($heap_in/$heap_out), no global to modify
  let modifies := []
  let spec : Core.Procedure.Spec := {
    modifies := modifies
    preconditions := preconditions
    postconditions := postconditions
  }
  let body : List Core.Statement ←
    match proc.body with
    | .Transparent bodyExpr => do
        let (_, stmts) ← translateStmt ctMap tcMap initEnv proc.outputs postcondExprs bodyExpr
        pure stmts
    | .Opaque _posts (some impl) _ => do
        let (_, stmts) ← translateStmt ctMap tcMap initEnv proc.outputs postcondExprs impl
        pure stmts
    | _ => pure []
  pure <| Core.Decl.proc ({
    header := header
    spec := spec
    body := body
  }) .empty

def heapTypeDecl : Core.Decl := .type (.con { name := "Heap", numargs := 0 })
def fieldTypeDecl : Core.Decl := .type (.con { name := "Field", numargs := 1 })
def compositeTypeDecl : Core.Decl := .type (.con { name := "Composite", numargs := 0 })
def arrayTypeSynonym : Core.Decl := .type (.syn { name := "Array", typeArgs := ["T"], type := .tcons "Map" [.int, .ftvar "T"] })

def readFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapRead"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy)]
    output := tVar
    body := none
  }

def updateFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapStore"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy),
               (Core.CoreIdent.locl "val", tVar)]
    output := heapTy
    body := none
  }

-- Axiom: forall h, o, f, v :: heapRead(heapStore(h, o, f, v), o, f) == v
-- Using int for field values since Core doesn't support polymorphism in axioms
def readUpdateSameAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Build: heapRead(heapStore(h, o, f, v), o, f) == v using de Bruijn indices
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (o), Heap (h)
  -- So: h is bvar 0, o is bvar 1, f is bvar 2, v is bvar 3
  let h := LExpr.bvar () 0
  let o := LExpr.bvar () 1
  let f := LExpr.bvar () 2
  let v := LExpr.bvar () 3
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o, f, v]
  let readExpr := LExpr.mkApp () readOp [updateExpr, o, f]
  let eqBody := LExpr.eq () readExpr v
  -- Wrap in foralls: forall v:int, f:Field int, o:Composite, h:Heap
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) eqBody
  .ax { name := "heapRead_heapStore_same", e := body }

-- Axiom: forall h, o1, o2, f1, f2, v :: (o1 != o2 || f1 != f2) ==> heapRead(heapStore(h, o1, f1, v), o2, f2) == heapRead(h, o2, f2)
def readUpdateDiffAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Quantifier order (outer to inner): int (v), Field (f2), Field (f1), Composite (o2), Composite (o1), Heap (h)
  -- So: h is bvar 0, o1 is bvar 1, o2 is bvar 2, f1 is bvar 3, f2 is bvar 4, v is bvar 5
  let h := LExpr.bvar () 0
  let o1 := LExpr.bvar () 1
  let o2 := LExpr.bvar () 2
  let f1 := LExpr.bvar () 3
  let f2 := LExpr.bvar () 4
  let v := LExpr.bvar () 5
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o1, f1, v]
  let lhs := LExpr.mkApp () readOp [updateExpr, o2, f2]
  let rhs := LExpr.mkApp () readOp [h, o2, f2]
  let objsDiff := LExpr.app () boolNotOp (LExpr.eq () o1 o2)
  let fieldsDiff := LExpr.app () boolNotOp (LExpr.eq () f1 f2)
  let precond := LExpr.mkApp () boolOrOp [objsDiff, fieldsDiff]
  let implBody := LExpr.mkApp () boolImpliesOp [precond, LExpr.eq () lhs rhs]
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) implBody
  .ax { name := "heapRead_heapStore_diff", e := body }

/-- Truncating division (Java/C semantics): truncates toward zero -/
def intDivTFunc : Core.Decl :=
  let a := LExpr.fvar () (Core.CoreIdent.locl "a") (some LMonoTy.int)
  let b := LExpr.fvar () (Core.CoreIdent.locl "b") (some LMonoTy.int)
  let zero := LExpr.intConst () 0
  let aGeZero := LExpr.mkApp () intGeOp [a, zero]
  let bGeZero := LExpr.mkApp () intGeOp [b, zero]
  let sameSign := LExpr.eq () aGeZero bGeZero
  let euclidDiv := LExpr.mkApp () intDivOp [a, b]
  let negA := LExpr.mkApp () intNegOp [a]
  let negADivB := LExpr.mkApp () intDivOp [negA, b]
  let negResult := LExpr.mkApp () intNegOp [negADivB]
  let body := LExpr.ite () sameSign euclidDiv negResult
  .func {
    name := Core.CoreIdent.unres "Int.DivT"
    typeArgs := []
    inputs := [(Core.CoreIdent.locl "a", LMonoTy.int), (Core.CoreIdent.locl "b", LMonoTy.int)]
    output := LMonoTy.int
    body := some body
  }

/-- Truncating modulo (Java/C semantics): a %t b = a - (a /t b) * b -/
def intModTFunc : Core.Decl :=
  let a := LExpr.fvar () (Core.CoreIdent.locl "a") (some LMonoTy.int)
  let b := LExpr.fvar () (Core.CoreIdent.locl "b") (some LMonoTy.int)
  let divT := LExpr.mkApp () intDivTOp [a, b]
  let mulDivB := LExpr.mkApp () intMulOp [divT, b]
  let body := LExpr.mkApp () intSubOp [a, mulDivB]
  .func {
    name := Core.CoreIdent.unres "Int.ModT"
    typeArgs := []
    inputs := [(Core.CoreIdent.locl "a", LMonoTy.int), (Core.CoreIdent.locl "b", LMonoTy.int)]
    output := LMonoTy.int
    body := some body
  }

def translateConstant (c : Constant) : Core.Decl :=
  let ty := translateType c.type.val
  .func {
    name := Core.CoreIdent.glob c.name
    typeArgs := []
    inputs := []
    output := ty
    body := none
  }

/--
Check if a StmtExpr is a pure expression (can be used as a Core function body).
Pure expressions don't contain statements like assignments, loops, or local variables.
A Block with a single pure expression is also considered pure.
-/
def isPureExpr (e : StmtExprMd) : Bool :=
  match _h : e.val with
  | .LiteralBool _ | .LiteralInt _ | .LiteralString _ | .Identifier _ => true
  | .PrimitiveOp _ args => args.attach.all fun ⟨a, _⟩ => isPureExpr a
  | .IfThenElse c t (some el) => isPureExpr c && isPureExpr t && isPureExpr el
  | .StaticCall _ args => args.attach.all fun ⟨a, _⟩ => isPureExpr a
  | .ReferenceEquals e1 e2 => isPureExpr e1 && isPureExpr e2
  | .Block [single] _ => isPureExpr single
  | .Forall _ _ body => isPureExpr body
  | .Exists _ _ body => isPureExpr body
  | .Return (some ret) => isPureExpr ret
  | _ => false
termination_by sizeOf e
decreasing_by stmtexpr_wf e, _h

/--
Check if a procedure can be translated as a Core function.
A procedure can be a function if:
- It has a transparent body that is a pure expression
- It has no precondition (or just `true`)
- It has exactly one output parameter (the return type)
- The output parameter does not have a constrained type (constraints need postcondition checks)
-/
def canBeCoreFunction (ctMap : ConstrainedTypeMap) (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent bodyExpr =>
    isPureExpr bodyExpr &&
    proc.preconditions.isEmpty &&
    proc.outputs.length == 1 &&
    proc.outputs.all (fun p => match p.type.val with
      | .UserDefined name => !ctMap.contains name
      | _ => true)
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable)
-/
def translateProcedureToFunction (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (proc : Procedure) : Except String Core.Decl := do
  let inputs := proc.inputs.flatMap (expandArrayParam ctMap)
  let outputTy ← match proc.outputs.head? with
    | some p => pure (translateTypeMdWithCT ctMap p.type)
    | none => throw s!"translateProcedureToFunction: {proc.name} has no output parameter"
  let arrayLenEnv : TypeEnv := proc.inputs.filterMap (fun p =>
    match p.type.val with
    | .Applied ctor _ =>
      match ctor.val with
      | .UserDefined "Array" => some (p.name ++ "_len", ⟨.TInt, p.type.md⟩)
      | _ => none
    | _ => none)
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++ arrayLenEnv
  let body ← match proc.body with
    | .Transparent bodyExpr => do
        let expr ← translateExpr ctMap tcMap initEnv bodyExpr
        pure (some expr)
    | _ => pure none
  pure (.func {
    name := Core.CoreIdent.glob proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  })

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) Core.Program := do
  let heapWriters := computeWritesHeap program.staticProcedures
  let heapProgram := heapParameterization program
  let sequencedProgram ← liftExpressionAssignments heapProgram
  -- Build constrained type maps
  let ctMap := buildConstrainedTypeMap sequencedProgram.types
  let tcMap ← buildTranslatedConstraintMap ctMap |>.mapError fun e => #[{ fileRange := default, message := e }]
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := sequencedProgram.staticProcedures.partition (canBeCoreFunction ctMap)
  let procDecls ← procProcs.mapM (translateProcedure ctMap tcMap sequencedProgram.constants heapWriters) |>.mapError fun e => #[{ fileRange := default, message := e }]
  let laurelFuncDecls ← funcProcs.mapM (translateProcedureToFunction ctMap tcMap) |>.mapError fun e => #[{ fileRange := default, message := e }]
  let constDecls := sequencedProgram.constants.map translateConstant
  let typeDecls := [heapTypeDecl, fieldTypeDecl, compositeTypeDecl, arrayTypeSynonym]
  let funcDecls := [readFunction, updateFunction, intDivTFunc, intModTFunc]
  let axiomDecls := [readUpdateSameAxiom, readUpdateDiffAxiom]
  return { decls := typeDecls ++ funcDecls ++ axiomDecls ++ constDecls ++ laurelFuncDecls ++ procDecls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let coreProgramExcept := translate program
    -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  match coreProgramExcept with
    | .error e => return .error e
    | .ok coreProgram =>
      let runner tempDir :=
        EIO.toIO (fun f => IO.Error.userError (toString f))
            (Core.verify smtsolver coreProgram tempDir .none options)
      let ioResult ← match tempDir with
      | .none =>
        IO.FS.withTempDir runner
      | .some p =>
        IO.FS.createDirAll ⟨p⟩
        runner ⟨p⟩
      return .ok ioResult


def verifyToDiagnostics (smtsolver : String) (files: Map Strata.Uri Lean.FileMap) (program : Program): IO (Array Diagnostic) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors.map (fun dm => dm.toDiagnostic files)
  | .ok results => return results.filterMap (fun dm => dm.toDiagnostic files)


def verifyToDiagnosticModels (smtsolver : String) (program : Program): IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors
  | .ok results => return results.filterMap toDiagnosticModel

end Laurel
