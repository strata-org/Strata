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

private def msgArrayLengthArity (got : Nat) : String :=
  s!"`Array.length` takes exactly one argument of type `Array<T>`, got {got}."

private def msgSequenceFromArrayArity (got : Nat) : String :=
  s!"`Sequence.fromArray` takes exactly one argument of type `Array<T>`, got {got}."

private def msgArrayInDatatypeArg : String :=
  "`Array<T>` is not supported as a datatype constructor argument. " ++
  "Datatypes carry value semantics whereas `Array<T>` is a heap reference; " ++
  "the combination does not typecheck. Use a `composite` instead, or wrap " ++
  "the array's contents as `Seq<T>` (which has value semantics)."


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
  | .TTypedField vt => validateHighType vt
  | .TMap kt vt => validateHighType kt ++ validateHighType vt
  | .Applied base args =>
    validateHighType base ++ args.flatMap validateHighType
  | .Pure base => validateHighType base
  | .Intersection tys => tys.flatMap validateHighType
  | .Unknown | .MultiValuedExpr _ => []
  | .TVoid | .TBool | .TInt | .TFloat64 | .TReal | .TString | .THeap
  | .TBv _ | .UserDefined _ | .TCore _ => []
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals (try term_by_mem)
  all_goals (try (have := HighType.sizeOf_tarray_et_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_tset_et_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_tseq_et_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_ttypedfield_vt_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_tmap_kt_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_tmap_vt_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_applied_base_lt_of_eq _hht; omega))
  all_goals (try (have := HighType.sizeOf_pure_base_lt_of_eq _hht; omega))
  -- For Applied args / Intersection types list iteration:
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := HighType.sizeOf_applied_args_lt_of_eq _hht
    omega))
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := HighType.sizeOf_intersection_types_lt_of_eq _hht
    omega))

/-! ## Expression-position walk (Subscript and call diagnostics) -/

/-- Walk a `StmtExprMd` and collect diagnostics for Subscript/Array.length
    misuse, recursing into all subexpressions and embedded types.
    Statement-position handling for `.Subscript t i (some v)` (destructive
    update — Diagnostic 2 on Seq) is inlined at the `.Block`, `.IfThenElse`,
    and `.While` arms. -/
def validateStmtExpr (model : SemanticModel) (expr : StmtExprMd) : List DiagnosticModel :=
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
        | _ => [diagnosticFromSource expr.source (msgArrayLengthArity args.length)]
      else []
    let fromArrayDiag : List DiagnosticModel :=
      if callee.text == sequenceFromArrayName then
        match args with
        | [a] =>
          let actualTy := (computeExprType model a).val
          if isArrayTy actualTy then []
          else [diagnosticFromSource expr.source (msgSequenceFromArrayArg (fmtType actualTy))]
        | _ => [diagnosticFromSource expr.source (msgSequenceFromArrayArity args.length)]
      else []
    lengthDiag ++ fromArrayDiag ++
      args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateStmtExpr model a) []
  -- Everything below: recurse into children; no local diagnostic.
  | .IfThenElse c t (some e) =>
    let tDiags := match _htsub : t.val with
      | .Subscript target index (some value) =>
        let diag := if isSeqTy (computeExprType model target).val then
                      [diagnosticFromSource t.source msgSeqDestructiveUpdate]
                    else []
        diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
          validateStmtExpr model value
      | _ => validateStmtExpr model t
    let eDiags := match _hesub : e.val with
      | .Subscript target index (some value) =>
        let diag := if isSeqTy (computeExprType model target).val then
                      [diagnosticFromSource e.source msgSeqDestructiveUpdate]
                    else []
        diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
          validateStmtExpr model value
      | _ => validateStmtExpr model e
    validateStmtExpr model c ++ tDiags ++ eDiags
  | .IfThenElse c t none =>
    let tDiags := match _htsub : t.val with
      | .Subscript target index (some value) =>
        let diag := if isSeqTy (computeExprType model target).val then
                      [diagnosticFromSource t.source msgSeqDestructiveUpdate]
                    else []
        diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
          validateStmtExpr model value
      | _ => validateStmtExpr model t
    validateStmtExpr model c ++ tDiags
  | .Block stmts _ =>
    stmts.attach.foldl (fun acc ⟨s, _⟩ => acc ++
      (match _hsub : s.val with
       | .Subscript target index (some value) =>
         let diag := if isSeqTy (computeExprType model target).val then
                       [diagnosticFromSource s.source msgSeqDestructiveUpdate]
                     else []
         diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
           validateStmtExpr model value
       | _ => validateStmtExpr model s)) []
  | .Var (.Declare param) => validateHighType param.type
  | .Var (.Field t _) => validateStmtExpr model t
  | .Var (.Local _) => []
  | .Assign targets value =>
    let targetDiags := targets.attach.foldl
      (fun acc ⟨t, _⟩ =>
        acc ++ (match _htv : t.val with
          | .Field subTarget _ => validateStmtExpr model subTarget
          | .Declare param => validateHighType param.type
          | .Local _ => [])) []
    targetDiags ++ validateStmtExpr model value
  | .While c invs (some dec) body =>
    let bodyDiags := match _hbsub : body.val with
      | .Subscript target index (some value) =>
        let diag := if isSeqTy (computeExprType model target).val then
                      [diagnosticFromSource body.source msgSeqDestructiveUpdate]
                    else []
        diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
          validateStmtExpr model value
      | _ => validateStmtExpr model body
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    validateStmtExpr model dec ++
    bodyDiags
  | .While c invs none body =>
    let bodyDiags := match _hbsub : body.val with
      | .Subscript target index (some value) =>
        let diag := if isSeqTy (computeExprType model target).val then
                      [diagnosticFromSource body.source msgSeqDestructiveUpdate]
                    else []
        diag ++ validateStmtExpr model target ++ validateStmtExpr model index ++
          validateStmtExpr model value
      | _ => validateStmtExpr model body
    validateStmtExpr model c ++
    invs.attach.foldl (fun acc ⟨i, _⟩ => acc ++ validateStmtExpr model i) [] ++
    bodyDiags
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
  -- Top-level .Subscript arm (expression position)
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _h; omega))
  -- .Block stmt-position .Subscript (via _hsub)
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_target_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_index_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_value_lt_of_eq _hsub
    simp_all; omega))
  -- IfThenElse then-branch (via _htsub) / else-branch (via _hesub) / While body (via _hbsub)
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _htsub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _htsub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _htsub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _hesub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _hesub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _hesub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _hbsub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _hbsub; simp_all; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _hbsub; simp_all; omega))

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
    dt.constructors.flatMap fun c =>
      c.args.flatMap fun p =>
        let arrayDiag : List DiagnosticModel :=
          if containsTArray p.type.val then
            [diagnosticFromSource p.type.source msgArrayInDatatypeArg]
          else []
        arrayDiag ++ validateHighType p.type
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
