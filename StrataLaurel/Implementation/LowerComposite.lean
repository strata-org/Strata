/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

import StrataLaurel.Implementation.HeapParameterizationConstants
import Strata.Util.Tactics
public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.Resolution
import StrataLaurel.Implementation.LaurelTypes
import StrataLaurel.Implementation.MapStmtExpr

public section

namespace Strata.Laurel

open Strata

private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := ⟨e, source⟩

/-- Synthetic source location for compiler-generated type hierarchy nodes. -/
private def syntheticSource : FileRange :=
  { file := .file "StrataLaurel/Implementation/LowerComposite.lean", range := SourceRange.none }

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type.
It enables checking for `<Type>` whether it is assignable to another type using a TotalMap lookup.
- A `ancestorsPerType` constant combining the per-type constants.
It enables checking for any type whether it is assignable to any other type using two TotalMap lookups.
We use this to translate `<value> is <Type>`.
The runtime type of `<value>` is used for the outer TotalMap lookup while `<Type>` for the inner one.

-/
def generateTypeHierarchyDecls (model : SemanticModel) (program: LaurelProgram) : Except String (List Constant) := do
  let composites := program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then return [] else
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", syntheticSource⟩
  let boolTy : HighTypeMd := ⟨.TBool, syntheticSource⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, syntheticSource⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, syntheticSource⟩
  -- Helper: build an inner map (TotalMap TypeTag bool) for a given composite type
  -- Start with mapConst(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : Except String StmtExprMd := do
    let ancestors ← computeAncestors model ct.name
    let falseConst := mkMd (.LiteralBool false) syntheticSource
    let emptyInner := mkMd (.StaticCall "mapConst" [falseConst] []) syntheticSource
    composites.foldlM (init := emptyInner) fun acc otherCt => do
      let isAncestor ← ancestors.anyM (fun anc => otherCt.name.sameId anc.name)
      if isAncestor then
        let otherConst := mkMd (.StaticCall (mkId $ otherCt.name.text ++ "_TypeTag") [] []) syntheticSource
        let boolVal := mkMd (.LiteralBool true) syntheticSource
        pure (mkMd (.StaticCall "update" [acc, otherConst, boolVal] []) syntheticSource)
      else pure acc
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls : List Constant ← composites.mapM fun ct => do
    let innerMap ← mkInnerMap ct
    pure { name := s!"ancestorsFor{ct.name.text}", type := innerMapTy, initializer := some innerMap }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := mkMd (.LiteralBool false) syntheticSource
  let emptyInner := mkMd (.StaticCall "mapConst" [falseConst] []) syntheticSource
  let emptyOuter := mkMd (.StaticCall "mapConst" [emptyInner] []) syntheticSource
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (mkId $ ct.name.text ++ "_TypeTag") [] []) syntheticSource
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name.text}" [] []) syntheticSource
    mkMd (.StaticCall "update" [acc, typeConst, innerMapRef] []) syntheticSource
  ) emptyOuter
  let ancestorsDecl : Constant :=
    { name := "ancestorsPerType"
      type := outerMapTy
      initializer := some outerMapExpr }
  pure (ancestorsForDecls ++ [ancestorsDecl])

/--
Lower `IsType target ty` to Laurel-level map lookups:
  `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
-/
def lowerIsType (target : StmtExprMd) (ty : HighTypeMd) (source : FileRange) : StmtExprMd :=
  match ty.val with
    | .UserDefined name => let typeName := name.text
        let typeTag := mkMd (.StaticCall "Composite..typeTag!" [target] []) source
        let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" [] []) source
        let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag] []) source
        let typeConst := mkMd (.StaticCall (mkId $ typeName ++ "_TypeTag") [] []) source
        ⟨.StaticCall "select" [innerMap, typeConst] [], source⟩
    | _ => { val := .Hole, source := source }

abbrev LCM := Except String

private def isComposite (model : SemanticModel) (name : Identifier) : Bool :=
  match model.get name with
  | .compositeType _ => true
  | _ => false

def resolveQualifiedFieldName (model : SemanticModel) (fieldName : Identifier) : Option Identifier :=
  match model.get fieldName with
  | .field owner _ => some { text := owner.text ++ "." ++ fieldName.text, source := fieldName.source }
  | _ => none

private def refOf (e : StmtExprMd) : StmtExprMd :=
  mkMd (.StaticCall compositeRefAccessor [e] []) e.source

def lowerNew (name : Identifier) (source : FileRange) : StmtExprMd :=
  mkMd (.StaticCall compositeCtorName
    [mkMd (.StaticCall allocateProcName [] []) source,
     mkMd (.StaticCall (name.text ++ "_TypeTag") [] []) source] []) source

private def rewriteReferenceEquality (model : SemanticModel) (e : StmtExprMd) : StmtExprMd :=
  match e.val with
  | .StaticCall callee [a, b] tyArgs =>
    -- For `==` and `!=` on Composite types, compare refs instead. These are
    -- calls to the built-in `$eq`/`$neq` wrappers (see `Operation.procName`);
    -- neither is overloaded, so `UniqueOverloadNames` leaves the names alone
    -- and matching on the text is safe.
    --
    -- The guard is `isComposite`, not `!isValueTypeName`. `.UserDefined` covers three
    -- things, not two: composites (heap references, where `ref!` is right),
    -- datatype values (where it is wrong), and type *parameters* — the `Val` of
    -- `Result<Val, Err>`, which is the type reported for `Result..value!(…)` and
    -- is an ordinary value, often an `int`. A parameter is not a datatype either,
    -- so excluding only datatypes would wrap it in `Composite..ref!` and fail to
    -- unify `(arrow Composite int)` against `(arrow int _)`. Ref-compare genuine
    -- composites and let everything else compare structurally.
    if callee.text == Operation.Eq.procName || callee.text == Operation.Neq.procName then
      match (computeExprType model a).val with
      | .UserDefined name =>
        if isComposite model name then ⟨.StaticCall callee [refOf a, refOf b] tyArgs, e.source⟩
        else e
      | _ => e
    else e
  | _ => e

def quantifyOverReference (isReferenceType : HighType → Bool) (param : Parameter)
    (trigger : Option StmtExprMd) (body : StmtExprMd) :
    Option (Parameter × Option StmtExprMd × StmtExprMd) :=
  if !isReferenceType param.type.val then none else
  let x := param.name.text
  let isX (e : StmtExprMd) : Bool := match e.val with
    | .Var (.Local n) => n.text == x
    | _ => false
  let isRefOfX (e : StmtExprMd) : Bool := match e.val with
    | .StaticCall callee [arg] _ => callee.text == compositeRefAccessor && isX arg
    | _ => false
  let rebinds (e : StmtExprMd) : Bool := match e.val with
    | .Quantifier _ p _ _ => p.name.text == x
    | _ => false
  let parts := body :: trigger.toList
  let count (p : StmtExprMd → Bool) : Nat :=
    parts.foldl (fun n e => foldStmtExpr (fun node k => if p node then k + 1 else k) n e) 0
  let uses := count isX
  if uses == 0 || uses != count isRefOfX || parts.any (anyStmtExpr rebinds) then none else
  let fresh : Identifier := { text := x, source := param.name.source }
  let unwrap := mapStmtExpr fun e => if isRefOfX e then ⟨.Var (.Local fresh), e.source⟩ else e
  some ({ name := fresh, type := ⟨.TInt, param.type.source⟩ }, trigger.map unwrap, unwrap body)

private def lowerCompositeNode (model : SemanticModel) (e : StmtExprMd) : LCM StmtExprMd := do
  let source := e.source
  match e.val with
  | .Var (.Field target fieldName) =>
    match resolveQualifiedFieldName model fieldName with
    | some q => return ⟨.Var (.Field (refOf target) q), source⟩
    | none => return e
  | .Assign targets value =>
    let targets' := targets.map fun t => match t.val with
      | .Field target fieldName =>
        match resolveQualifiedFieldName model fieldName with
        | some q => ⟨.Field (refOf target) q, t.source⟩
        | none => t
      | _ => t
    return ⟨.Assign targets' value, source⟩
  | .PureFieldUpdate target fieldName value =>
    match resolveQualifiedFieldName model fieldName with
    | some q => return ⟨.PureFieldUpdate target q value, source⟩
    | none => return e
  -- Type args are already stripped by MonomorphizeComposites (`new C<τ>` → `new C$…`),
  -- so lowering keys off the concrete name and the residual `_` is safely ignored.
  | .New name _ => return lowerNew name source
  | .IsType target ty => return lowerIsType target ty source
  | .Quantifier mode param trigger body =>
    let isComposite' : HighType → Bool := fun ty => match ty with
      | .UserDefined name => isComposite model name
      | _ => false
    match quantifyOverReference isComposite' param trigger body with
    | some (param', trigger', body') => return ⟨.Quantifier mode param' trigger' body', source⟩
    | none => return e
  | .AsType target ty =>
    match highBaseName? ty.val with
    | some tn => return ⟨.StaticCall (downcastProcName tn) [target] [], source⟩
    | none => throw s!"cast to '{repr ty.val}', which is not a composite type, reached LowerComposite"
  | _ => return e

/--
Rewrite a type so that every reference to a composite type (a name in
`composites`) becomes the flattened `Composite` datatype. After this pass every
composite value is a `Composite`, so its *static* type must follow suit; otherwise
re-resolution sees a `Pixel`-typed value flowing into a `Composite`-typed slot
(`Composite..ref!`, `Composite..typeTag!`, a `downcast$C` helper, …).

Recursion into structural type formers is handled by the generic `HighType.mapType`,
so this only needs to patch the `UserDefined` leaf — a nested reference (the `C` in
`Box<C>`) is flattened rather than falling through a catch-all. -/
def compositeRefToComposite (composites : Std.HashSet String) (ty : HighTypeMd) : HighTypeMd :=
  { ty with val := ty.val.mapType fun t =>
      match t with
      | .UserDefined name =>
        if composites.contains name.text then .UserDefined compositeTypeName else t
      | _ => t }

def generatedNameCollisionHint : String :=
  "this name collides with one introduced by an internal lowering \
   pass; rename the identifier — a reserved internal type name (e.g. `Heap`, \
   `Field`, `TypeTag`, `Composite`) or a name containing `$` / the \
   `$aN$` instantiation-tag shape can clash with a synthetic name"

private def reservedCompositeNames : List String :=
  [compositeTypeName.text, "TypeTag", "Field", heapTypeName.text]

def reservedCompositeNameCollisions (program : LaurelProgram) : List Message :=
  program.types.filterMap fun td =>
    match td with
    | .Composite ct =>
      if reservedCompositeNames.contains ct.name.text then
        some (diagnosticFromSource ct.name.source
          s!"Duplicate definition '{ct.name.text}' is already defined in this scope ({generatedNameCollisionHint})")
      else none
    | _ => none

def heapFieldLocationOwner (ct : CompositeType) : String :=
  match ct.extending.find? isGenericFamilyParent >>= (highBaseName? ·.val) with
  | some family => (family.text.drop genericFamilyPrefix.length).toString
  | none => ct.name.text

def lowerComposite (model : SemanticModel) (program : LaurelProgram) : Except String LaurelProgram := do
  let program := { program with types := program.types.filter fun td =>
    match td with
    | .Composite ct => !isGenericFamilyName ct.name.text
    | _ => true }
  let compositeNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name.text
    | _ => none
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", syntheticSource⟩
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := compositeNames.map fun n => { name := (mkId $ n ++ "_TypeTag"), args := [] } }
  let compositeDatatype : TypeDefinition :=
    .Datatype { name := compositeTypeName, typeArgs := [], constructors := [
      { name := mkId compositeCtorName,
        args := [{ name := "ref", type := ⟨.TInt, syntheticSource⟩ },
                 { name := "typeTag", type := typeTagTy }] }] }
  let typeHierarchyConstants ← generateTypeHierarchyDecls model program
  -- One downcast helper per composite — `procedure downcast$C(p: C) returns (r: C) requires (p is C) { r := p }`
  -- — called by the cast lowering below so an `x as C` cast works in a
  -- contract formula (the `is C` guard is a pure term; PrecondElim discharges it as a
  -- well-definedness obligation). `C` flattens to `Composite` below, so `r := p` type-checks.
  let downcastHelpers : List Procedure := program.types.filterMap fun td =>
    match td with
    | .Composite ct =>
      let cty : HighTypeMd := ⟨.UserDefined ct.name, syntheticSource⟩
      let pRef : StmtExprMd := mkMd (.Var (.Local "p")) syntheticSource
      let assignOutput : StmtExprMd :=
        mkMd (.Assign [⟨.Local "r", syntheticSource⟩] pRef) syntheticSource
      some { name := downcastProcName ct.name, typeArgs := [],
             inputs := [{ name := "p", type := cty }],
             outputs := [{ name := "r", type := cty }],
             preconditions := [{ condition := lowerIsType pRef cty syntheticSource }],
             decreases := none,
             body := .Transparent (mkMd (.Block [assignOutput] none) syntheticSource) }
    | _ => none
  let allocateProc : List Procedure :=
    if compositeNames.isEmpty then []
    else [{ name := mkId allocateProcName, typeArgs := [], inputs := [],
            outputs := [{ name := "r", type := ⟨.TInt, syntheticSource⟩ }],
            preconditions := [], decreases := none, body := .External }]
  -- Program-wide, because the composite-flattening sweep at the end of this pass is too: a
  -- position this missed would keep its `.IsType` node while losing the annotation that node
  -- needs, which the re-resolution after the pass reports as a `strata-bug`.
  let withHelpers := { program with staticProcedures := program.staticProcedures ++ downcastHelpers ++ allocateProc }
  let withRefEq := mapLaurelProgramStmtExpr (rewriteReferenceEquality model) withHelpers
  let lowered ← mapLaurelProgramStmtExprM (lowerCompositeNode model) withRefEq
  let heapFields := lowered.types.flatMap fun td =>
    match td with
    | .Composite ct => ct.fields.map fun f =>
        { toField := { f with name := { text := ct.name.text ++ "." ++ f.name.text, source := f.name.source } }
          location := { text := heapFieldLocationOwner ct ++ "." ++ f.name.text, source := f.name.source } }
    | _ => []
  let remainingTypes := lowered.types.filter fun td =>
    match td with
    | .Composite _ => false
    | _ => true
  let transformed : LaurelProgram :=
    { lowered with
      types := [typeTagDatatype, compositeDatatype] ++ remainingTypes,
      constants := lowered.constants ++ typeHierarchyConstants,
      heapFields := lowered.heapFields ++ heapFields }
  -- Now that `New`/`IsType` have been lowered (they needed the original
  -- composite names), flatten every remaining composite reference type to the
  -- `Composite` datatype so the program re-resolves consistently. The
  -- program-wide `HighType` traversal lives in `MapStmtExpr` so that every
  -- type position is covered uniformly.
  let compositeSet : Std.HashSet String :=
    compositeNames.foldl (init := {}) (·.insert ·)
  pure (mapLaurelProgramHighTypes (compositeRefToComposite compositeSet) transformed)

public def lowerCompositePass : LaurelPass := .onUnordered {
  name := "LowerComposite"
  needsResolves := true
  creates := [
      NodeKind.StmtExpr.StaticCall,
      NodeKind.Procedure.inputs.cons,
      NodeKind.Procedure.preconditions.cons,
      NodeKind.Pseudo.typeTag,
      NodeKind.LaurelProgram.heapFields.cons
    ]
  unsupported := [
      NodeKind.CompositeType.typeArgs.cons,
      NodeKind.CompositeType.instanceProcedures.cons,
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  removes := [
      NodeKind.StmtExpr.IsType,
      NodeKind.StmtExpr.New,
      NodeKind.StmtExpr.AsType,
      NodeKind.TypeDefinition.Composite
    ]
  documentation := "Lowers composite types to the flat `Composite` datatype: every composite field becomes a heap field with a qualified name, accessed on the `int` reference of a `Composite`; allocation becomes `MkComposite($allocate(), C_TypeTag())`; type tests and casts become lookups in the ancestor tables; and reference equality compares the references."
  }
  fun _ p m =>
    match reservedCompositeNameCollisions p with
    | [] =>
      match lowerComposite m p with
      | .ok p' => (p', [], {})
      | .error e => (p, [Message.fromString e .strataBug], {})
    | collisions => (p, collisions, {})

end Strata.Laurel

end -- public section
