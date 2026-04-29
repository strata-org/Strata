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

The four diagnostics are:

1. `a[i := v]` on `Array<T>` — arrays are mutable; functional update is only
   valid for sequences.
2. `s[i] := v` on `Seq<T>` — sequences are immutable; destructive update is
   only valid for arrays.
3. `Array.length(x)` where `x` is not an `Array<T>`.
4. `Array<T>` where `T ≠ int` (current SMT limitation).
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

private def msgArrayElementNotInt (actual : String) : String :=
  s!"`Array<T>` is currently only supported for `T = int`. " ++
  s!"Support for other element types is not yet implemented. Found: `Array<{actual}>`."

/-! ## Type-position walk (diagnostic 4) -/

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

/-! ## Expression-position walk (diagnostics 1, 2, 3) -/

/-- Walk a `StmtExprMd` and collect diagnostics for Subscript/Array.length
    misuse, recursing into all subexpressions and embedded types. -/
def validateStmtExpr (model : SemanticModel) (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  -- Diagnostic 1: a[i := v] on Array<T>
  | .Subscript target index (some value) =>
    let here :=
      if isArrayTy (computeExprType model target).val then
        [diagnosticFromSource expr.source msgArrayFuncUpdate]
      else []
    here ++ validateStmtExpr model target ++ validateStmtExpr model index ++
      validateStmtExpr model value
  | .Subscript target index none =>
    validateStmtExpr model target ++ validateStmtExpr model index
  -- Diagnostic 2: s[i] := v on Seq<T>
  | .Assign targets value =>
    let assignDiag : List DiagnosticModel :=
      match targets with
      | [⟨.Subscript target _ none, ssrc⟩] =>
        if isSeqTy (computeExprType model target).val then
          [diagnosticFromSource ssrc msgSeqDestructiveUpdate]
        else []
      | _ => []
    let targetDiags := targets.attach.foldl
      (fun acc ⟨t, _⟩ => acc ++ validateStmtExpr model t) []
    assignDiag ++ targetDiags ++ validateStmtExpr model value
  -- Diagnostic 3: Array.length(x) with x not Array<T>
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
    lengthDiag ++ args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateStmtExpr model a) []
  -- Everything below: recurse into children; no local diagnostic.
  | .IfThenElse c t (some e) =>
    validateStmtExpr model c ++ validateStmtExpr model t ++ validateStmtExpr model e
  | .IfThenElse c t none =>
    validateStmtExpr model c ++ validateStmtExpr model t
  | .Block stmts _ =>
    stmts.attach.foldl (fun acc ⟨s, _⟩ => acc ++ validateStmtExpr model s) []
  | .LocalVariable _ ty (some init) =>
    validateHighType ty ++ validateStmtExpr model init
  | .LocalVariable _ ty none => validateHighType ty
  | .While c invs (some dec) body =>
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    validateStmtExpr model dec ++
    validateStmtExpr model body
  | .While c invs none body =>
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    validateStmtExpr model body
  | .Return (some v) => validateStmtExpr model v
  | .Return none => []
  | .FieldSelect t _ => validateStmtExpr model t
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
  | _ => []
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals omega

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
