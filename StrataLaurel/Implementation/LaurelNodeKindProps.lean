/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelNodeKind

/-!
# Node Kinds of a Program

`NodeKind` (see `LaurelNodeKind.lean`) is the vocabulary each pass uses to
declare what it `creates`, `requires`, `removes` and lists as `unsupported`.
Those declarations are *claims about programs*, and this module says what the
claims mean: `Contains s e` holds when every node kind occurring anywhere in `e`
is in `s`.

With that, a pass's declarations become a provable specification. For a pass
`P` whose `run` is `f`:

```
Contains s p  →  Contains ((s \ P.removes) ∪ P.creates) (f p)
```

is the statement "`P` removes at least what it says it removes and creates
nothing it does not declare". `EliminateDoWhileProps.lean` proves it for
`eliminateDoWhilePass`.

## The three pieces

The recursion is split so that the definitions stay non-recursive and the
proofs get a structural induction principle for free:

* `NodeKind.ofStmtExpr` — the kinds a *single* node contributes, and nothing
  about its children. This is where the `Owner.field.Leaf` refinements live
  (`StmtExpr.While.postTest.true` for a post-test loop, and so on).
* `stmtExprChildren` / `stmtExprTypes` — a node's immediate `StmtExprMd` and
  `HighTypeMd` children. `stmtExprChildren` deliberately mirrors, arm for arm,
  the recursion of `mapStmtExprUsedM`: that traversal is what every pass rewrites
  through, so a `Contains` proof about a pass is only as good as the agreement
  between these two lists.
* `Contains` / `ContainsType` — one-constructor inductive predicates tying the
  two together.

The vocabulary a pass's proof is expected to reuse: `Contains.mono` /
`ContainsType.mono` (a larger kind set contains no less), `containerKinds`, and
the inversions that read a kind back off a node (`ofStmtExpr_postTest_true`,
`ofStmtExpr_incrDecr`, `ofStmtExpr_compoundAssign`, `ofHighType_mem`,
`ofOperation_mem`).

## Key results

* `KindSet` — a set of node kinds, and `Contains` / `ContainsType` — every kind in
  an expression (or a type) is in the set;
* `Contains.mono` / `ContainsType.mono` — monotonicity in the set;
* `ofStmtExpr_postTest_true` / `ofHighType_mem` — reading a kind back off a node;
* `containerKinds` — the kinds a container carries rather than an expression;
* `Program.Contains` — the whole-program predicate a pass's specification uses,
  built up through `Condition.Contains`, `Body.Contains`, `Procedure.Contains` and
  `TypeDefinition.Contains`.

## Coverage

Only the 58 non-`Pseudo` kinds are decided here; `Pseudo.*` kinds are, by
construction, not readable off an AST (see the `LaurelNodeKind` module docs) and
no `Contains` clause mentions them. A `Pseudo` kind in a pass's `creates` is
therefore invisible to a spec theorem — it can neither be proven nor refuted.

Conversely several `StmtExpr` constructors have no kind of their own
(`LiteralInt`, `ReferenceEquals`, `Quantifier`, `Assigned`, `Fresh`, `ProveBy`,
`ContractOf`, `Abstract`, `All`): they contribute nothing, so `Contains s e`
constrains nothing about them. Adding a kind for one is the way to make it
visible.
-/

namespace Strata.Laurel

public section

/-! ## Sets of node kinds -/

/-- A set of node kinds. `NodeKind → Prop` rather than `Finset NodeKind`, which
    would need Mathlib; the pass declarations are `List NodeKind`, which coerces. -/
abbrev KindSet := NodeKind → Prop

namespace KindSet

/-- The kinds listed in `l`, as a set. -/
@[expose] def ofList (l : List NodeKind) : KindSet := fun k => k ∈ l

/-- Every kind except `k`. Used to say "this subtree has no do-while in it". -/
@[expose] def except (k : NodeKind) : KindSet := fun k' => k' ≠ k

end KindSet

instance : Membership NodeKind KindSet := ⟨fun s k => s k⟩
instance : Union KindSet := ⟨fun a b k => a k ∨ b k⟩
instance : SDiff KindSet := ⟨fun a b k => a k ∧ ¬ b k⟩
instance : Coe (List NodeKind) KindSet := ⟨KindSet.ofList⟩

/-- `s ⊆ t`, spelled out to avoid needing a `HasSubset` instance. -/
@[expose] def KindSet.Subset (s t : KindSet) : Prop := ∀ k, k ∈ s → k ∈ t

/-- Membership in a union is membership in one of the two sets. -/
theorem KindSet.mem_union {a b : KindSet} {k : NodeKind} : k ∈ a ∪ b ↔ k ∈ a ∨ k ∈ b := Iff.rfl

/-- Membership in a difference is membership in the first and not the second. -/
theorem KindSet.mem_sdiff {a b : KindSet} {k : NodeKind} : k ∈ a \ b ↔ k ∈ a ∧ ¬ k ∈ b := Iff.rfl

/-- A listed kind set contains exactly the kinds in the list. -/
theorem KindSet.mem_ofList {l : List NodeKind} {k : NodeKind} :
    k ∈ KindSet.ofList l ↔ k ∈ l := Iff.rfl

/-! ## The kinds of one node -/

/-- The kinds contributed by a single `HighType` node. -/
@[expose] def NodeKind.ofHighType : HighType → List NodeKind
  | .Applied .. => [NodeKind.HighType.Applied]
  | .TVar .. => [NodeKind.HighType.TVar]
  | _ => []

/-- A `HighType`'s immediate component types. -/
@[expose] def highTypeChildren : HighType → List HighTypeMd
  | .TSet e => [e]
  | .TMap k v => [k, v]
  | .Applied base args => base :: args
  | .Intersection tys => tys
  | .MultiValuedExpr tys => tys
  | _ => []

/-- The kinds contributed by a single `Variable` node, which is not itself a
    `StmtExpr`: a field read is `StmtExpr.Var.var.Field`. -/
@[expose] def NodeKind.ofVariable : Variable → List NodeKind
  | .Field .. => [NodeKind.StmtExpr.Var.var.Field]
  | _ => []

/-- The kinds an operator denotes. Only the two short-circuit operators have a kind
    of their own; `Not`, `Add`, … do not. -/
@[expose] def NodeKind.ofOperation : Operation → List NodeKind
  | .AndThen => [NodeKind.Operation.AndThen]
  | .OrElse => [NodeKind.Operation.OrElse]
  | _ => []

/-- The operator kinds a callee name denotes: a primitive operator is a call to its
    built-in wrapper, so `$andThen` counts as `Operation.AndThen`. -/
@[expose] def NodeKind.ofCallee (callee : Identifier) : List NodeKind :=
  match Operation.ofProcName? callee.text with
  | some op => NodeKind.ofOperation op
  | none => []

/-- Whether a node is a bare local-variable read. Used by
    `NodeKind.StmtExpr.Old.value.Var.Local`, the one kind that reads a *child*'s
    constructor rather than the node's own fields. -/
@[expose] def isVarLocal (e : StmtExprMd) : Bool :=
  match e.val with
  | .Var (.Local _) => true
  | _ => false

/-- The kinds contributed by a single `StmtExpr` node: its constructor's own
    kind, plus every `Owner.field.Leaf` refinement its fields satisfy. Says
    nothing about children. -/
@[expose] def NodeKind.ofStmtExpr : StmtExpr → List NodeKind
  | .IfThenElse .. => [NodeKind.StmtExpr.IfThenElse]
  | .Block .. => [NodeKind.StmtExpr.Block]
  | .While _ _ _ _ postTest =>
    [NodeKind.StmtExpr.While]
      ++ (if postTest then [NodeKind.StmtExpr.While.postTest.true] else [])
  | .Exit .. => [NodeKind.StmtExpr.Exit]
  | .Return value =>
    [NodeKind.StmtExpr.Return]
      ++ (if value.isSome then [NodeKind.StmtExpr.Return.value.some] else [])
  | .LiteralBool .. => [NodeKind.StmtExpr.LiteralBool]
  | .Var v => NodeKind.StmtExpr.Var :: NodeKind.ofVariable v
  | .Assign .. => [NodeKind.StmtExpr.Assign]
  | .IncrDecr .. => [NodeKind.StmtExpr.IncrDecr]
  | .CompoundAssign op _ _ =>
    NodeKind.StmtExpr.CompoundAssign :: NodeKind.ofOperation op
  | .PureFieldUpdate .. => [NodeKind.StmtExpr.PureFieldUpdate]
  | .StaticCall callee _ => NodeKind.StmtExpr.StaticCall :: NodeKind.ofCallee callee
  | .New .. => [NodeKind.StmtExpr.New]
  | .This => [NodeKind.StmtExpr.This]
  | .AsType .. => [NodeKind.StmtExpr.AsType]
  | .IsType .. => [NodeKind.StmtExpr.IsType]
  | .InstanceCall .. => [NodeKind.StmtExpr.InstanceCall]
  | .Old value label? =>
    (if label?.isSome then [NodeKind.StmtExpr.Old.label?.some] else [])
      ++ (if isVarLocal value then [NodeKind.StmtExpr.Old.value.Var.Local] else [])
  | .OldGuarantee .. => [NodeKind.StmtExpr.OldGuarantee]
  | .OldRelies .. => [NodeKind.StmtExpr.OldRelies]
  | .Assert .. => [NodeKind.StmtExpr.Assert]
  | .Assume .. => [NodeKind.StmtExpr.Assume]
  | .Throw .. => [NodeKind.StmtExpr.Throw]
  | .Try _ _ finally? =>
    [NodeKind.StmtExpr.Try]
      ++ (if finally?.isSome then [NodeKind.StmtExpr.Try.finally?.some] else [])
  | .Hole deterministic type =>
    (if deterministic then [NodeKind.StmtExpr.Hole.deterministic.true]
     else [NodeKind.StmtExpr.Hole.deterministic.false])
      ++ (if type.isSome then [NodeKind.StmtExpr.Hole.type.some]
          else [NodeKind.StmtExpr.Hole.type.none])
  | .Yield => [NodeKind.StmtExpr.Yield]
  | .Resume .. => [NodeKind.StmtExpr.Resume]
  | .HasNext .. => [NodeKind.StmtExpr.HasNext]
  | .Snapshot .. => [NodeKind.StmtExpr.Snapshot]
  -- Constructors with no kind of their own; see the module documentation.
  | .LiteralInt .. | .LiteralString .. | .LiteralDecimal .. | .LiteralBv ..
  | .ReferenceEquals .. | .Quantifier .. | .Assigned .. | .Fresh ..
  | .ProveBy .. | .ContractOf .. | .Abstract | .All => []

/-! ## A node's children

`stmtExprChildren` must list exactly the `StmtExprMd` positions
`mapStmtExprUsedM` recurses into — the sentinel test at the bottom of
`MapStmtExpr.lean` guards the same agreement from the traversal's side. -/

/-- The `StmtExprMd` a `Variable` holds (only a field read holds one). -/
@[expose] def variableChildren : Variable → List StmtExprMd
  | .Field target _ => [target]
  | .Local _ | .Declare _ => []

/-- The declared type a `Variable` carries (only a `Declare` carries one). -/
@[expose] def variableTypes : Variable → List HighTypeMd
  | .Declare p => p.type.toList
  | .Local _ | .Field .. => []

/-- A node's immediate `StmtExprMd` children. -/
@[expose] def stmtExprChildren : StmtExpr → List StmtExprMd
  | .IfThenElse cond th el => [cond, th] ++ el.toList
  | .Block stmts _ => stmts
  | .While cond invariants decreases body _ =>
    [cond] ++ invariants ++ decreases.toList ++ [body]
  | .Return value => value.toList
  | .Resume target value => [target] ++ value.toList
  | .HasNext target => [target]
  | .Assign targets value => targets.flatMap (fun t => variableChildren t.val) ++ [value]
  | .Var v => variableChildren v
  | .IncrDecr _ _ target => variableChildren target.val
  | .CompoundAssign _ target rhs => variableChildren target.val ++ [rhs]
  | .PureFieldUpdate target _ newValue => [target, newValue]
  | .StaticCall _ arguments => arguments
  | .ReferenceEquals lhs rhs => [lhs, rhs]
  | .AsType target _ => [target]
  | .IsType target _ => [target]
  | .InstanceCall target _ arguments => [target] ++ arguments
  | .Quantifier _ _ trigger body => trigger.toList ++ [body]
  | .Assigned name => [name]
  | .Old value _ => [value]
  | .OldGuarantee value => [value]
  | .OldRelies value => [value]
  | .Fresh value => [value]
  | .Assert condition _ => [condition]
  | .Assume condition => [condition]
  | .Throw value => [value]
  | .Try body catches finally? =>
    [body] ++ catches.flatMap (fun c => c.predicate.toList ++ [c.body]) ++ finally?.toList
  | .ProveBy value proof => [value, proof]
  | .ContractOf _ function => [function]
  -- Leaves.
  | .Exit .. | .LiteralInt .. | .LiteralBool .. | .LiteralString ..
  | .LiteralDecimal .. | .LiteralBv .. | .New .. | .This | .Abstract | .All
  | .Hole .. | .Yield | .Snapshot .. => []

/-- The type annotations a node carries directly. -/
@[expose] def stmtExprTypes : StmtExpr → List HighTypeMd
  | .New _ typeArgs => typeArgs
  | .AsType _ targetType => [targetType]
  | .IsType _ type => [type]
  | .Hole _ type => type.toList
  | .Quantifier _ param _ _ => [param.type]
  | .Var v => variableTypes v
  | .Assign targets _ => targets.flatMap (fun t => variableTypes t.val)
  | .IncrDecr _ _ target => variableTypes target.val
  | .CompoundAssign _ target _ => variableTypes target.val
  | .Try _ catches _ => catches.map (·.bindingType)
  | _ => []

/-- The kinds a *container* carries — every kind not contributed by a `StmtExpr`
    node: the `Owner.field.cons` / `.some` refinements on `Program`, `Procedure`,
    `Body` and `CompositeType`, the `TypeDefinition.*` kinds,
    `Condition.mode.Assume`, and the two `HighType` kinds.

    A pass that rewrites only inside expressions removes none of these, and so
    gets the generic program-level lift (`ProgramLift.lift_program`) for free. One
    that does remove a container kind — `GlobalParameterization` removes
    `Program.staticFields.cons` — has to lift its own. -/
@[expose] def containerKinds : List NodeKind :=
  [ NodeKind.HighType.Applied,
    NodeKind.HighType.TVar,
    NodeKind.TypeDefinition.Composite,
    NodeKind.TypeDefinition.Constrained,
    NodeKind.TypeDefinition.Datatype,
    NodeKind.TypeDefinition.Alias,
    NodeKind.CompositeType.typeArgs.cons,
    NodeKind.CompositeType.instanceProcedures.cons,
    NodeKind.Program.staticProcedures.cons,
    NodeKind.Program.staticFields.cons,
    NodeKind.Procedure.inputs.cons,
    NodeKind.Procedure.contracts.Coroutine,
    NodeKind.Procedure.preconditions.cons,
    NodeKind.Procedure.throwsType.some,
    NodeKind.Procedure.throwsOn.cons,
    NodeKind.Body.postconditions.cons,
    NodeKind.Body.modifies.cons,
    NodeKind.Condition.mode.Assume ]

/-! ## `Contains` -/

/-- Every kind occurring in the type `t` is in `s`. -/
inductive ContainsType (s : KindSet) : HighTypeMd → Prop where
  | node (t : HighTypeMd)
      (head : ∀ k ∈ NodeKind.ofHighType t.val, k ∈ s)
      (kids : ∀ c ∈ highTypeChildren t.val, ContainsType s c)
      : ContainsType s t

/-- Every kind occurring anywhere in the expression `e` — its own, and every
    node and type annotation below it — is in `s`.

    This is the meaning of a pass's `NodeKind` declarations: `creates` bounds the
    kinds the output may have gained, `removes` the kinds it must have lost. -/
inductive Contains (s : KindSet) : StmtExprMd → Prop where
  | node (e : StmtExprMd)
      (head : ∀ k ∈ NodeKind.ofStmtExpr e.val, k ∈ s)
      (types : ∀ t ∈ stmtExprTypes e.val, ContainsType s t)
      (kids : ∀ c ∈ stmtExprChildren e.val, Contains s c)
      : Contains s e

/-- `Contains` under a name that is not shadowed inside the `X.Contains`
    namespaces below (where `Contains` would resolve to `X.Contains` itself). -/
abbrev ContainsExpr (s : KindSet) (e : StmtExprMd) : Prop := Contains s e

/-! ## Reading a kind back off a node -/

/-- A callee's kinds are its operator's kinds. -/
private theorem ofCallee_subset {c : Identifier} {k : NodeKind} (hk : k ∈ NodeKind.ofCallee c) :
    ∃ op, k ∈ NodeKind.ofOperation op := by
  simp only [NodeKind.ofCallee] at hk
  split at hk
  · exact ⟨_, hk⟩
  · simp at hk

/-- An operator contributes only its own two kinds. -/
theorem ofOperation_mem {op : Operation} {k : NodeKind} (hk : k ∈ NodeKind.ofOperation op) :
    k = NodeKind.Operation.AndThen ∨ k = NodeKind.Operation.OrElse := by
  cases op <;> simp [NodeKind.ofOperation] at hk <;> simp [hk]

/-- Only a post-test `While` carries `StmtExpr.While.postTest.true`. -/
theorem ofStmtExpr_postTest_true {v : StmtExpr}
    (h : NodeKind.StmtExpr.While.postTest.true ∈ NodeKind.ofStmtExpr v) :
    ∃ cond invs dec body, v = .While cond invs dec body true := by
  cases v
  case While cond invs dec body postTest =>
    cases postTest
    · simp [NodeKind.ofStmtExpr] at h
    · exact ⟨cond, invs, dec, body, rfl⟩
  case Var var => cases var <;> simp [NodeKind.ofStmtExpr, NodeKind.ofVariable] at h
  case CompoundAssign op target rhs =>
    simp only [NodeKind.ofStmtExpr, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · rcases ofOperation_mem h with h1 | h1 <;> exact absurd h1 (by simp)
  case StaticCall callee args =>
    simp only [NodeKind.ofStmtExpr, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · obtain ⟨op, hop⟩ := ofCallee_subset h
      rcases ofOperation_mem hop with h1 | h1 <;> exact absurd h1 (by simp)
  all_goals
    refine absurd h ?_
    grind [NodeKind.ofStmtExpr, NodeKind.ofVariable, NodeKind.ofCallee,
      NodeKind.ofOperation]

/-- Only an `IncrDecr` carries `StmtExpr.IncrDecr`. -/
theorem ofStmtExpr_incrDecr {v : StmtExpr}
    (h : NodeKind.StmtExpr.IncrDecr ∈ NodeKind.ofStmtExpr v) :
    ∃ mode op target, v = .IncrDecr mode op target := by
  cases v
  case IncrDecr mode op target => exact ⟨mode, op, target, rfl⟩
  case Var var => cases var <;> simp [NodeKind.ofStmtExpr, NodeKind.ofVariable] at h
  case CompoundAssign op target rhs =>
    simp only [NodeKind.ofStmtExpr, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · rcases ofOperation_mem h with h1 | h1 <;> exact absurd h1 (by simp)
  case StaticCall callee args =>
    simp only [NodeKind.ofStmtExpr, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · obtain ⟨op, hop⟩ := ofCallee_subset h
      rcases ofOperation_mem hop with h1 | h1 <;> exact absurd h1 (by simp)
  all_goals
    refine absurd h ?_
    grind [NodeKind.ofStmtExpr, NodeKind.ofVariable, NodeKind.ofCallee,
      NodeKind.ofOperation]

/-- Only a `CompoundAssign` carries `StmtExpr.CompoundAssign`. -/
theorem ofStmtExpr_compoundAssign {v : StmtExpr}
    (h : NodeKind.StmtExpr.CompoundAssign ∈ NodeKind.ofStmtExpr v) :
    ∃ op target rhs, v = .CompoundAssign op target rhs := by
  cases v
  case CompoundAssign op target rhs => exact ⟨op, target, rhs, rfl⟩
  case Var var => cases var <;> simp [NodeKind.ofStmtExpr, NodeKind.ofVariable] at h
  case StaticCall callee args =>
    simp only [NodeKind.ofStmtExpr, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · obtain ⟨op, hop⟩ := ofCallee_subset h
      rcases ofOperation_mem hop with h1 | h1 <;> exact absurd h1 (by simp)
  all_goals
    refine absurd h ?_
    grind [NodeKind.ofStmtExpr, NodeKind.ofVariable, NodeKind.ofCallee,
      NodeKind.ofOperation]

/-- A type contributes only the two `HighType` kinds. -/
theorem ofHighType_mem {v : HighType} {k : NodeKind} (hk : k ∈ NodeKind.ofHighType v) :
    k = NodeKind.HighType.Applied ∨ k = NodeKind.HighType.TVar := by
  cases v <;> simp [NodeKind.ofHighType] at hk <;> simp [hk]

/-! ## Monotonicity -/

/-- `ContainsType` is monotone in the kind set: a type whose kinds are all in `s`
    has them all in any larger `t`. -/
theorem ContainsType.mono {s t : KindSet} {ty : HighTypeMd}
    (h : ContainsType s ty) (hst : KindSet.Subset s t) : ContainsType t ty := by
  induction h with
  | node ty head kids ih =>
    exact .node ty (fun k hk => hst k (head k hk)) (fun c hc => ih c hc)

/-- `Contains` is monotone in the kind set. Note a pass's output set is *not*
    larger than its input (it drops what the pass `removes`), so this applies to
    the parts of a program a pass leaves alone, not to its output. -/
theorem Contains.mono {s t : KindSet} {e : StmtExprMd}
    (h : Contains s e) (hst : KindSet.Subset s t) : Contains t e := by
  induction h with
  | node e head types kids ih =>
    exact .node e (fun k hk => hst k (head k hk))
      (fun ty hty => (types ty hty).mono hst) (fun c hc => ih c hc)

/-! ## Lifting `Contains` to the rest of the AST

These are plain definitions rather than inductives: every one of them bottoms
out in `Contains` / `ContainsType` on the expressions and types it holds. They
mirror the field-by-field walk of `mapProgramStmtExprM`, which reaches every
expression in a program, plus
the structural kinds (`Program.staticProcedures.cons`, `Procedure.inputs.cons`,
`Body.modifies.cons`, …) that no expression walk sees. -/

/-- `k ∈ s` whenever `l` is non-empty: the meaning of an `Owner.field.cons` kind. -/
@[expose] def ConsKind (s : KindSet) (l : List α) (k : NodeKind) : Prop :=
  l ≠ [] → k ∈ s

/-- `k ∈ s` whenever `o` is `some`: the meaning of an `Owner.field.some` kind. -/
@[expose] def SomeKind (s : KindSet) (o : Option α) (k : NodeKind) : Prop :=
  o.isSome → k ∈ s

/-- A parameter contributes only its type annotation. -/
@[expose] def Parameter.Contains (s : KindSet) (p : Parameter) : Prop :=
  ContainsType s p.type

/-- An optionally-annotated parameter contributes its annotation when it has one. -/
@[expose] def Parameter?.Contains (s : KindSet) (p : Parameter?) : Prop :=
  ∀ t ∈ p.type, ContainsType s t

/-- A condition contributes its expression, and `Condition.mode.Assume` when it is
    a `free` condition. -/
@[expose] def Condition.Contains (s : KindSet) (c : Condition) : Prop :=
  ContainsExpr s c.condition
    ∧ (c.mode = ConditionMode.Assume → NodeKind.Condition.mode.Assume ∈ s)

/-- A `modifies` group contributes its targets and its guard. -/
@[expose] def ModifiesGroup.Contains (s : KindSet) (g : ModifiesGroup) : Prop :=
  (∀ e ∈ g.targets, ContainsExpr s e) ∧ (∀ e ∈ g.guard, ContainsExpr s e)

/-- A body contributes its implementation, its postconditions and its frame, plus
    the `Body.*.cons` kinds for the non-empty ones. -/
@[expose] def Body.Contains (s : KindSet) (b : Body) : Prop :=
  match b with
  | .Transparent body => ContainsExpr s body
  | .Opaque postconditions implementation modifies =>
    (∀ c ∈ postconditions, Condition.Contains s c)
      ∧ ConsKind s postconditions NodeKind.Body.postconditions.cons
      ∧ (∀ e ∈ implementation, ContainsExpr s e)
      ∧ (∀ g ∈ modifies, ModifiesGroup.Contains s g)
      ∧ ConsKind s modifies NodeKind.Body.modifies.cons
  | .Abstract postconditions =>
    (∀ c ∈ postconditions, Condition.Contains s c)
      ∧ ConsKind s postconditions NodeKind.Body.postconditions.cons
  | .External => True

/-- A `throwsOn` case contributes its guard, its postconditions and its frame. -/
@[expose] def ThrowsOnBlock.Contains (s : KindSet) (b : ThrowsOnBlock) : Prop :=
  ContainsExpr s b.guard
    ∧ (∀ c ∈ b.postconditions, Condition.Contains s c)
    ∧ (∀ e ∈ b.modifies, ContainsExpr s e)

/-- A coroutine's clauses contribute their conditions and channel-binding types,
    plus `Procedure.contracts.Coroutine` when the procedure is one. -/
@[expose] def CoroutineContracts.Contains (s : KindSet) (c : CoroutineContracts) : Prop :=
  (∀ cond ∈ c.relies, Condition.Contains s cond)
    ∧ (∀ cond ∈ c.guarantees, Condition.Contains s cond)
    ∧ (∀ p ∈ c.yields, Parameter.Contains s p)
    ∧ (∀ p ∈ c.resumes, Parameter.Contains s p)
    ∧ (c.kind = ProcedureKind.Coroutine → NodeKind.Procedure.contracts.Coroutine ∈ s)

/-- A procedure contributes every expression and type it holds — signature,
    specifications, body, exceptional contract and coroutine clauses — plus its
    `Procedure.*` refinement kinds. -/
@[expose] def Procedure.Contains (s : KindSet) (p : Procedure) : Prop :=
  (∀ i ∈ p.inputs, Parameter.Contains s i)
    ∧ ConsKind s p.inputs NodeKind.Procedure.inputs.cons
    ∧ (∀ o ∈ p.outputs, Parameter.Contains s o)
    ∧ (∀ c ∈ p.preconditions, Condition.Contains s c)
    ∧ ConsKind s p.preconditions NodeKind.Procedure.preconditions.cons
    ∧ CoroutineContracts.Contains s p.contracts
    ∧ (∀ e ∈ p.decreases, ContainsExpr s e)
    ∧ Body.Contains s p.body
    ∧ (∀ e ∈ p.invokeOn, ContainsExpr s e)
    ∧ (∀ e ∈ p.axioms, ContainsExpr s e)
    ∧ (∀ t ∈ p.throwsType, ContainsType s t)
    ∧ SomeKind s p.throwsType NodeKind.Procedure.throwsType.some
    ∧ (∀ b ∈ p.throwsOn, ThrowsOnBlock.Contains s b)
    ∧ ConsKind s p.throwsOn NodeKind.Procedure.throwsOn.cons

/-- A field contributes its declared type and its initializer. -/
@[expose] def Field.Contains (s : KindSet) (f : Field) : Prop :=
  ContainsType s f.type ∧ (∀ e ∈ f.initializer, ContainsExpr s e)

/-- A composite contributes its parents' types, its fields and its methods, plus
    the two `CompositeType.*.cons` kinds. There is no kind for having a parent, so
    `extending` shows up only through the types in it. -/
@[expose] def CompositeType.Contains (s : KindSet) (c : CompositeType) : Prop :=
  ConsKind s c.typeArgs NodeKind.CompositeType.typeArgs.cons
    ∧ (∀ t ∈ c.extending, ContainsType s t)
    ∧ (∀ f ∈ c.fields, Field.Contains s f)
    ∧ (∀ p ∈ c.instanceProcedures, Procedure.Contains s p)
    ∧ ConsKind s c.instanceProcedures NodeKind.CompositeType.instanceProcedures.cons

/-- A constrained type contributes its base type, constraint and witness. -/
@[expose] def ConstrainedType.Contains (s : KindSet) (c : ConstrainedType) : Prop :=
  ContainsType s c.base ∧ ContainsExpr s c.constraint ∧ ContainsExpr s c.witness

/-- A datatype contributes its constructors' argument types. -/
@[expose] def DatatypeDefinition.Contains (s : KindSet) (d : DatatypeDefinition) : Prop :=
  ∀ ctor ∈ d.constructors, ∀ arg ∈ ctor.args, Parameter.Contains s arg

/-- A type definition contributes its own `TypeDefinition.*` kind and whatever its
    particular form holds. -/
@[expose] def TypeDefinition.Contains (s : KindSet) (td : TypeDefinition) : Prop :=
  match td with
  | .Composite c => NodeKind.TypeDefinition.Composite ∈ s ∧ CompositeType.Contains s c
  | .Constrained c => NodeKind.TypeDefinition.Constrained ∈ s ∧ ConstrainedType.Contains s c
  | .Datatype d => NodeKind.TypeDefinition.Datatype ∈ s ∧ DatatypeDefinition.Contains s d
  | .Alias a => NodeKind.TypeDefinition.Alias ∈ s ∧ ContainsType s a.target
  | .Opaque _ => True

/-- A constant contributes its declared type and its initializer. -/
@[expose] def Constant.Contains (s : KindSet) (c : Constant) : Prop :=
  ContainsType s c.type ∧ (∀ e ∈ c.initializer, ContainsExpr s e)

/-- The procedures of a program: the static ones and the composites' methods.
    This is exactly what `mapProgramProceduresM` walks. -/
@[expose] def Program.ContainsProcedures (s : KindSet) (p : Program) : Prop :=
  (∀ proc ∈ p.staticProcedures, Procedure.Contains s proc)
    ∧ (∀ td ∈ p.types, ∀ c : CompositeType, td = .Composite c →
        (∀ proc ∈ c.instanceProcedures, Procedure.Contains s proc))

/-- A type definition minus its instance procedures. -/
@[expose] def TypeDefinition.ContainsOutsideProcedures (s : KindSet) (td : TypeDefinition) : Prop :=
  match td with
  | .Composite c =>
    NodeKind.TypeDefinition.Composite ∈ s
      ∧ ConsKind s c.typeArgs NodeKind.CompositeType.typeArgs.cons
      ∧ (∀ t ∈ c.extending, ContainsType s t)
      ∧ (∀ f ∈ c.fields, Field.Contains s f)
      ∧ ConsKind s c.instanceProcedures NodeKind.CompositeType.instanceProcedures.cons
  | other => TypeDefinition.Contains s other

/-- Everything in a program that is *not* inside a procedure: the type
    definitions' own shape, a composite's fields, a constrained type's
    constraint and witness, the constants and the file-scope globals — plus the
    two `Program.*.cons` kinds.

    Kept separate from `ContainsProcedures` because a pass built only on
    `mapProgramProceduresM` never rewrites any of it, so such a pass's
    specification has to assume this part of the input already lies in the output
    set. A pass using the whole-program walk `mapProgramStmtExprM` needs no such
    assumption. -/
@[expose] def Program.ContainsOutsideProcedures (s : KindSet) (p : Program) : Prop :=
  ConsKind s p.staticProcedures NodeKind.Program.staticProcedures.cons
    ∧ (∀ f ∈ p.staticFields, Field.Contains s f)
    ∧ ConsKind s p.staticFields NodeKind.Program.staticFields.cons
    ∧ (∀ td ∈ p.types, TypeDefinition.ContainsOutsideProcedures s td)
    ∧ (∀ c ∈ p.constants, Constant.Contains s c)

/-- Every kind occurring anywhere in the program is in `s`. -/
@[expose] def Program.Contains (s : KindSet) (p : Program) : Prop :=
  Program.ContainsProcedures s p ∧ Program.ContainsOutsideProcedures s p

end -- public section

end Strata.Laurel
