/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.Resolution
import Strata.Util.Tactics

/-!
# Subscript Usage Validator

Pure validation pass (Laurel → `List DiagnosticModel`) that reports misuses of
`Seq<T>` and `Array<T>` which would otherwise surface as confusing downstream
errors. Runs alongside `validateDiamondFieldAccesses` in `runLaurelPasses`.

The diagnostics are:

1. `a[i := v]` on `Array<T>` — arrays are mutable; functional update is only
   valid for sequences.
2. `s[i] := v` on `Seq<T>` — sequences are immutable; destructive update is
   only valid for arrays.
3. `Array.length(x)` where `x` is not an `Array<T>`.
4. `Array<T>` where `T ≠ int` (current SMT limitation).
5. `Sequence.fromArray(x)` where `x` is not an `Array<T>`.
-/

namespace Strata.Laurel

open Strata

public section

/-! ## Helpers -/

private def fmtType (t : HighType) : String := (Std.format t).pretty

private def isArrayTy (t : HighType) : Bool :=
  match t with | .TArray _ => true | _ => false

private def isSeqTy (t : HighType) : Bool :=
  match t with | .TSeq _ => true | _ => false

/-- Message wording. Substrings of these strings appear in the
    `// ^^^ error: ...` annotations of T18_Sequences.lean and T19_Arrays.lean;
    update both sides together if you reword. -/
private def msgArrayFuncUpdate : String :=
  "`a[i := v]` is not supported on `Array<T>`: arrays are mutable. " ++
  "Use `a[i] := v` to update in place, or declare `a` as `Seq<T>` to use `s[i := v]`."

private def msgSeqDestructiveUpdate : String :=
  "`s[i] := v` is not allowed: sequences (`Seq<T>`) are immutable. " ++
  "Use `s[i := v]` to produce a new sequence with index `i` set to `v`, " ++
  "or declare `s` as `Array<T>` to update in place."

private def msgArrayLengthArg (actual : String) : String :=
  s!"`Array.length` requires an argument of type `Array<T>`, got `{actual}`."

private def msgSequenceFromArrayArg (actual : String) : String :=
  s!"`Sequence.fromArray` requires an argument of type `Array<T>`, got `{actual}`."

private def msgArrayElementNotInt (actual : String) : String :=
  s!"`Array<T>` is currently only supported for `T = int`. " ++
  s!"Support for other element types is not yet implemented. Found: `Array<{actual}>`."

/-! ## Type-position walk (Array element type diagnostic) -/

/-- Collect diagnostics for any `Array<T>` whose element type is not `int`. -/
partial def validateHighType (ty : HighTypeMd) : List DiagnosticModel :=
  match ty.val with
  | .TArray et =>
    let here : List DiagnosticModel :=
      match et.val with
      | .TInt => []
      | other =>
        [diagnosticFromSource ty.source (msgArrayElementNotInt (fmtType other))]
    -- Recurse into the element type — rare but a nested `Array<Array<int>>`
    -- should still complain about the outer not being int.
    here ++ validateHighType et
  | .TSet et => validateHighType et
  | .TSeq et => validateHighType et
  | .TTypedField vt => validateHighType vt
  | .TMap kt vt => validateHighType kt ++ validateHighType vt
  | .Applied base args =>
    validateHighType base ++ args.flatMap validateHighType
  | .Pure base => validateHighType base
  | .Intersection tys => tys.flatMap validateHighType
  | _ => []

/-! ## Expression-position walk (Subscript and call diagnostics) -/

mutual

/-- Walk a `StmtExprMd` and collect diagnostics for Subscript/Array.length
    misuse, recursing into all subexpressions and embedded types. -/
partial def validateStmtExpr (model : SemanticModel) (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  -- Diagnostic 1: a[i := v] on Array<T>
  -- Note: for Seq<T>, `.Subscript s i (some v)` at STATEMENT position (`s[i] := v`)
  -- is a user error (Seq is immutable) — diagnosed in the `.Block` arm below.
  -- At EXPRESSION position (`x := s[i := v]`), it's fine on Seq<T>.
  | .Subscript target index (some value) =>
    let here :=
      if isArrayTy (computeExprType model target).val then
        [diagnosticFromSource expr.source msgArrayFuncUpdate]
      else []
    here ++ validateStmtExpr model target ++ validateStmtExpr model index ++
      validateStmtExpr model value
  | .Subscript target index none =>
    validateStmtExpr model target ++ validateStmtExpr model index
  -- Diagnostics 3 and 5: Array.length(x) / Sequence.fromArray(x) with x not Array<T>
  | .StaticCall callee args =>
    let lengthDiag : List DiagnosticModel :=
      if callee.text == arrayLengthName then
        match args with
        | [a] =>
          let actualTy := (computeExprType model a).val
          if isArrayTy actualTy then []
          else [diagnosticFromSource expr.source (msgArrayLengthArg (fmtType actualTy))]
        | _ => []
      else []
    let fromArrayDiag : List DiagnosticModel :=
      if callee.text == sequenceFromArrayName then
        match args with
        | [a] =>
          let actualTy := (computeExprType model a).val
          if isArrayTy actualTy then []
          else [diagnosticFromSource expr.source (msgSequenceFromArrayArg (fmtType actualTy))]
        | _ => []
      else []
    lengthDiag ++ fromArrayDiag ++
      args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateStmtExpr model a) []
  -- Everything below: recurse into children; no local diagnostic.
  | .IfThenElse c t (some e) =>
    validateStmtExpr model c ++ validateStmt model t ++ validateStmt model e
  | .IfThenElse c t none =>
    validateStmtExpr model c ++ validateStmt model t
  | .Block stmts _ =>
    stmts.attach.foldl (fun acc ⟨s, _⟩ => acc ++ validateStmt model s) []
  | .Var (.Declare param) => validateHighType param.type
  | .Var (.Field t _) => validateStmtExpr model t
  | .Var (.Local _) => []
  | .Assign targets value =>
    let targetDiags := targets.attach.foldl
      (fun acc ⟨t, _⟩ =>
        acc ++ (match t.val with
          | .Field subTarget _ => validateStmtExpr model subTarget
          | .Declare param => validateHighType param.type
          | .Local _ => [])) []
    targetDiags ++ validateStmtExpr model value
  | .While c invs (some dec) body =>
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    validateStmtExpr model dec ++
    validateStmt model body
  | .While c invs none body =>
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    validateStmt model body
  | .Return (some v) => validateStmtExpr model v
  | .Return none => []
  | .PureFieldUpdate t _ v => validateStmtExpr model t ++ validateStmtExpr model v
  | .PrimitiveOp _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateStmtExpr model a) []
  | .InstanceCall t _ args =>
    validateStmtExpr model t ++
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateStmtExpr model a) []
  | .ReferenceEquals l r => validateStmtExpr model l ++ validateStmtExpr model r
  | .AsType t ty => validateStmtExpr model t ++ validateHighType ty
  | .IsType t ty => validateStmtExpr model t ++ validateHighType ty
  | .Quantifier _ p (some trig) body =>
    validateHighType p.type ++ validateStmtExpr model trig ++ validateStmtExpr model body
  | .Quantifier _ p none body =>
    validateHighType p.type ++ validateStmtExpr model body
  | .Assigned n => validateStmtExpr model n
  | .Old v => validateStmtExpr model v
  | .Fresh v => validateStmtExpr model v
  | .Assert c => validateStmtExpr model c.condition
  | .Assume c => validateStmtExpr model c
  | .ProveBy v p => validateStmtExpr model v ++ validateStmtExpr model p
  | .ContractOf _ f => validateStmtExpr model f
  | .Hole _ (some ty) => validateHighType ty
  -- Leaves: no StmtExprMd children, no types to validate.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children (or embedded
  -- types) is added, it must get its own arm above; otherwise this walker
  -- will silently skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Hole _ none | .New _ | .This | .Abstract | .All => []

/-- Validate a statement-position `StmtExprMd`. Called from every
    statement-position container: `.Block` children, `.IfThenElse`
    branches, `.While` body. Handles the statement-position semantics of
    `.Subscript t i (some v)` (destructive update: valid on `Array<T>`,
    invalid on `Seq<T>` → Diagnostic 2), distinct from expression-position
    functional update (handled by `validateStmtExpr`'s `.Subscript` arm). -/
partial def validateStmt (model : SemanticModel) (s : StmtExprMd) : List DiagnosticModel :=
  match s.val with
  | .Subscript target index value =>
    let diag : List DiagnosticModel :=
      match value with
      | some _ =>
        if isSeqTy (computeExprType model target).val then
          [diagnosticFromSource s.source msgSeqDestructiveUpdate]
        else []
      | none => []
    diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
      (match value with | some v => validateStmtExpr model v | none => [])
  | _ => validateStmtExpr model s

end

/-! ## Per-procedure and per-type validation -/

private def validateBody (model : SemanticModel) (body : Body) : List DiagnosticModel :=
  match body with
  | .Transparent b => validateStmtExpr model b
  | .Opaque posts impl mods =>
    posts.foldl (fun acc c => acc ++ validateStmtExpr model c.condition) [] ++
    (match impl with | some i => validateStmtExpr model i | none => []) ++
    mods.foldl (fun acc m => acc ++ validateStmtExpr model m) []
  | .Abstract posts =>
    posts.foldl (fun acc c => acc ++ validateStmtExpr model c.condition) []
  | .External => []

private def validateProcedure (model : SemanticModel) (proc : Procedure) : List DiagnosticModel :=
  proc.inputs.flatMap (fun p => validateHighType p.type) ++
  proc.outputs.flatMap (fun p => validateHighType p.type) ++
  proc.preconditions.foldl (fun acc c => acc ++ validateStmtExpr model c.condition) [] ++
  (match proc.decreases with | some d => validateStmtExpr model d | none => []) ++
  (match proc.invokeOn with | some v => validateStmtExpr model v | none => []) ++
  validateBody model proc.body

private def validateTypeDefinition (model : SemanticModel)
    (td : TypeDefinition) : List DiagnosticModel :=
  match td with
  | .Composite ct =>
    ct.fields.flatMap (fun f => validateHighType f.type) ++
    ct.instanceProcedures.flatMap (validateProcedure model)
  | .Constrained ct =>
    validateHighType ct.base ++ validateStmtExpr model ct.constraint ++
    validateStmtExpr model ct.witness
  | .Datatype dt =>
    dt.constructors.flatMap fun c => c.args.flatMap (fun p => validateHighType p.type)
  | .Alias ta => validateHighType ta.target

private def validateConstant (model : SemanticModel) (c : Constant) : List DiagnosticModel :=
  validateHighType c.type ++
  (match c.initializer with | some i => validateStmtExpr model i | none => [])

/-- Run the Subscript/Array-length usage validator on the whole program. -/
def validateSubscriptUsage (model : SemanticModel) (program : Program) : List DiagnosticModel :=
  program.staticProcedures.flatMap (validateProcedure model) ++
  program.staticFields.flatMap (fun f => validateHighType f.type) ++
  program.types.flatMap (validateTypeDefinition model) ++
  program.constants.flatMap (validateConstant model)

end -- public section
end Strata.Laurel
