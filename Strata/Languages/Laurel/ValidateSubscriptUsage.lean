/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.SubscriptElim
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
4. `Array<T>` where `T ≠ int` (not yet implemented at the Laurel layer).
5. `Sequence.fromArray(x)` where `x` is not an `Array<T>`.
-/

namespace Strata.Laurel

open Strata

public section

/-! ## Helpers -/

private def fmtType (t : HighType) : String := (Std.format t).pretty

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

private def msgArrayLengthArity (got : Nat) : String :=
  s!"`Array.length` takes exactly one argument of type `Array<T>`, got {got}."

private def msgSequenceFromArrayArity (got : Nat) : String :=
  s!"`Sequence.fromArray` takes exactly one argument of type `Array<T>`, got {got}."


/-! ## Type-position walk (Array element type diagnostic) -/

/-- Collect diagnostics for any `Array<T>` whose element type is not `int`.

    Like `containsTArray`, each constructor has its own arm so adding a new
    `HighType` variant produces a missing-cases error. `Unknown` and
    `MultiValuedExpr` are explicit no-op arms (they cannot carry
    user-declared types that need validating). -/
def validateHighType (ty : HighTypeMd) : List DiagnosticModel :=
  match _hht : ty.val with
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
  | .TMap kt vt => validateHighType kt ++ validateHighType vt
  | .Applied base args =>
    validateHighType base ++ args.flatMap validateHighType
  | .Pure base => validateHighType base
  | .Intersection tys => tys.flatMap validateHighType
  | .Unknown | .MultiValuedExpr _ => []
  | .TVoid | .TBool | .TInt | .TFloat64 | .TReal | .TString
  | .TBv _ | .UserDefined _ | .TCore _ => []
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals (try term_by_mem)
  -- Single-child recursion (TArray/TSet/TSeq/TMap/Applied-base/Pure).
  all_goals (try term_by_val ty, _hht)
  -- List-member recursion (Applied args / Intersection types): also chain
  -- through `List.sizeOf_lt_of_mem`.
  all_goals (have := List.sizeOf_lt_of_mem ‹_›; term_by_val ty, _hht)

/-! ## Expression-position walk (Subscript and call diagnostics) -/

/-- Walk a `StmtExprMd` and collect diagnostics for Subscript/Array.length
    misuse, recursing into all subexpressions and embedded types. The
    `.Subscript`-vs-`.SubscriptWrite` node distinction carries the
    functional-vs-destructive meaning, so no position decoding is needed. -/
def validateStmtExpr (model : SemanticModel) (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  -- Diagnostic 1: functional update `a[i := v]` on Array<T> (not supported).
  | .Subscript target index (some value) =>
    let here :=
      if (computeExprType model target).val.isArray then
        [diagnosticFromSource expr.source msgArrayFuncUpdate]
      else []
    here ++ validateStmtExpr model target ++ validateStmtExpr model index ++
      validateStmtExpr model value
  | .Subscript target index none =>
    validateStmtExpr model target ++ validateStmtExpr model index
  -- Diagnostic 2: destructive write `s[i] := v` on Seq<T> (immutable).
  | .SubscriptWrite target index value =>
    let here :=
      if (computeExprType model target).val.isSeq then
        [diagnosticFromSource expr.source msgSeqDestructiveUpdate]
      else []
    here ++ validateStmtExpr model target ++ validateStmtExpr model index ++
      validateStmtExpr model value
  -- Diagnostics 3 and 5: Array.length(x) / Sequence.fromArray(x) with x not Array<T>
  | .StaticCall callee args =>
    let lengthDiag : List DiagnosticModel :=
      if callee.text == arrayLengthName then
        match args with
        | [a] =>
          let actualTy := (computeExprType model a).val
          if actualTy.isArray then []
          else [diagnosticFromSource expr.source (msgArrayLengthArg (fmtType actualTy))]
        | _ => [diagnosticFromSource expr.source (msgArrayLengthArity args.length)]
      else []
    let fromArrayDiag : List DiagnosticModel :=
      if callee.text == sequenceFromArrayName then
        match args with
        | [a] =>
          let actualTy := (computeExprType model a).val
          if actualTy.isArray then []
          else [diagnosticFromSource expr.source (msgSequenceFromArrayArg (fmtType actualTy))]
        | _ => [diagnosticFromSource expr.source (msgSequenceFromArrayArity args.length)]
      else []
    lengthDiag ++ fromArrayDiag ++
      args.attach.flatMap (fun ⟨a, _⟩ => validateStmtExpr model a)
  -- Everything below: recurse into children; no local diagnostic.
  | .IfThenElse c t (some e) =>
    validateStmtExpr model c ++ validateStmtExpr model t ++ validateStmtExpr model e
  | .IfThenElse c t none =>
    validateStmtExpr model c ++ validateStmtExpr model t
  | .Block stmts _ =>
    stmts.attach.flatMap (fun ⟨s, _⟩ => validateStmtExpr model s)
  | .Var (.Declare param) => validateHighType param.type
  | .Var (.Field t _) => validateStmtExpr model t
  | .Var (.Local _) => []
  | .Assign targets value =>
    let targetDiags := targets.attach.flatMap fun ⟨t, _⟩ =>
      match _htv : t.val with
      | .Field subTarget _ => validateStmtExpr model subTarget
      | .Declare param => validateHighType param.type
      | .Local _ => []
    targetDiags ++ validateStmtExpr model value
  | .While c invs (some dec) body =>
    validateStmtExpr model c ++
    invs.attach.flatMap (fun ⟨i, _⟩ => validateStmtExpr model i) ++
    validateStmtExpr model dec ++
    validateStmtExpr model body
  | .While c invs none body =>
    validateStmtExpr model c ++
    invs.attach.flatMap (fun ⟨i, _⟩ => validateStmtExpr model i) ++
    validateStmtExpr model body
  | .Return (some v) => validateStmtExpr model v
  | .Return none => []
  | .PureFieldUpdate t _ v => validateStmtExpr model t ++ validateStmtExpr model v
  | .IncrDecr _ _ ⟨.Field subTarget _, _⟩ => validateStmtExpr model subTarget
  | .IncrDecr _ _ ⟨.Declare param, _⟩ => validateHighType param.type
  | .IncrDecr _ _ ⟨.Local _, _⟩ => []
  | .PrimitiveOp _ args _ =>
    args.attach.flatMap (fun ⟨a, _⟩ => validateStmtExpr model a)
  | .InstanceCall t _ args =>
    validateStmtExpr model t ++
    args.attach.flatMap (fun ⟨a, _⟩ => validateStmtExpr model a)
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
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Hole _ none | .New _ | .This | .Abstract | .All => []
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  -- Assign-target list, .Field inner
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := Variable.sizeOf_field_target_lt_of_eq _htv
    simp_all; omega))
  -- .Subscript / .SubscriptWrite children (target/index/value/update).
  all_goals (try term_by_val expr, _h)
  -- Block / container list members.
  all_goals (try (have := List.sizeOf_lt_of_mem ‹_›; simp_all; omega))

/-! ## Per-procedure and per-type validation -/

private def validateBody (model : SemanticModel) (body : Body) : List DiagnosticModel :=
  match body with
  | .Transparent b => validateStmtExpr model b
  | .Opaque posts impl mods =>
    posts.flatMap (fun c => validateStmtExpr model c.condition) ++
    (match impl with | some i => validateStmtExpr model i | none => []) ++
    mods.flatMap (validateStmtExpr model)
  | .Abstract posts =>
    posts.flatMap (fun c => validateStmtExpr model c.condition)
  | .External => []

private def validateProcedure (model : SemanticModel) (proc : Procedure) : List DiagnosticModel :=
  proc.inputs.flatMap (fun p => validateHighType p.type) ++
  proc.outputs.flatMap (fun p => validateHighType p.type) ++
  proc.preconditions.flatMap (fun c => validateStmtExpr model c.condition) ++
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
    dt.constructors.flatMap fun c =>
      c.args.flatMap fun p => validateHighType p.type
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
