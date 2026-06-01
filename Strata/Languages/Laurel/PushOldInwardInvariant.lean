/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.PushOldInward

/-!
# `pushOldInward` output invariant

`pushOldInward_old_normalized`: every `Old` subterm of `pushOldInward p`'s
output has the form `.Old ⟨.Var (.Local n), _⟩` with `n.text` an inout
parameter of the enclosing procedure.
-/

namespace Strata
namespace Laurel

public section

/-! ## `subOlds`: list every `Old` subterm of an expression -/

/-- All `Old` subterms reachable from `e`, including `e` itself if it is
    an `Old`. -/
def StmtExprMd.subOlds (expr : StmtExprMd) : List StmtExprMd :=
  match _h : expr.val with
    | .IfThenElse cond th el =>
        StmtExprMd.subOlds cond ++ StmtExprMd.subOlds th ++
        (match _h2 : el with | none => [] | some e => StmtExprMd.subOlds e)
    | .Block stmts _ =>
        (stmts.attach.map fun ⟨s, _⟩ => StmtExprMd.subOlds s).flatten
    | .While cond invs dec body =>
        StmtExprMd.subOlds cond ++
        (invs.attach.map fun ⟨i, _⟩ => StmtExprMd.subOlds i).flatten ++
        (match _h2 : dec with | none => [] | some d => StmtExprMd.subOlds d) ++
        StmtExprMd.subOlds body
    | .Return v => match _h2 : v with | none => [] | some e => StmtExprMd.subOlds e
    | .Assign _ value => StmtExprMd.subOlds value
    | .Var (.Field target _) => StmtExprMd.subOlds target
    | .PureFieldUpdate t _ nv => StmtExprMd.subOlds t ++ StmtExprMd.subOlds nv
    | .StaticCall _ args => (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten
    | .PrimitiveOp _ args => (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten
    | .ReferenceEquals lhs rhs => StmtExprMd.subOlds lhs ++ StmtExprMd.subOlds rhs
    | .AsType t _ => StmtExprMd.subOlds t
    | .IsType t _ => StmtExprMd.subOlds t
    | .InstanceCall t _ args =>
        StmtExprMd.subOlds t ++ (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten
    | .Quantifier _ _ trigger body =>
        (match _h2 : trigger with | none => [] | some t => StmtExprMd.subOlds t) ++
        StmtExprMd.subOlds body
    | .Assigned n => StmtExprMd.subOlds n
    | .Old v => expr :: StmtExprMd.subOlds v
    | .Fresh v => StmtExprMd.subOlds v
    | .Assert c => StmtExprMd.subOlds c.condition
    | .Assume c => StmtExprMd.subOlds c
    | .ProveBy v p => StmtExprMd.subOlds v ++ StmtExprMd.subOlds p
    | .ContractOf _ fn => StmtExprMd.subOlds fn
    | _ => []
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- All `StmtExprMd` reachable from a procedure (top-level only —
    `subOlds` then walks each one for nested `Old`s). -/
def Procedure.allStmtExprs (proc : Procedure) : List StmtExprMd :=
  proc.preconditions.map (·.condition) ++
  proc.decreases.toList ++
  (match proc.body with
   | .Transparent b => [b]
   | .Opaque ps impl mods =>
       ps.map (·.condition) ++ impl.toList ++ mods
   | .Abstract ps => ps.map (·.condition)
   | .External => []) ++
  proc.invokeOn.toList

/-! ## Canonical `Old` shape -/

/-- An expression is a "canonical Old" w.r.t. `inoutNames` if it is
    `.Old (.Var (.Local n))` with `n.text ∈ inoutNames`. -/
def IsCanonicalOld (inoutNames : List String) (e : StmtExprMd) : Prop :=
  ∃ (n : Identifier) (src1 src2 : Option FileRange),
    e = ⟨.Old ⟨.Var (.Local n), src1⟩, src2⟩ ∧ n.text ∈ inoutNames

/-- The structural invariant: every `Old` subterm is canonical for the
    given `inoutNames`. -/
def AllSubOldsCanonical (inoutNames : List String) (e : StmtExprMd) : Prop :=
  ∀ subOld ∈ e.subOlds, IsCanonicalOld inoutNames subOld

/-- Concatenation closure: AllSubOldsCanonical is preserved by membership in concat. -/
theorem allSubOldsCanonical_append_of_mem
    {inoutNames : List String} {xs : List StmtExprMd}
    (hAll : ∀ x ∈ xs, AllSubOldsCanonical inoutNames x) :
    ∀ subOld ∈ (xs.map StmtExprMd.subOlds).flatten, IsCanonicalOld inoutNames subOld := by
  intro subOld hMem
  simp [List.mem_flatten, List.mem_map] at hMem
  obtain ⟨_, ⟨x, hx, hEq⟩, hSub⟩ := hMem
  rw [← hEq] at hSub
  exact hAll x hx subOld hSub

/-! ## Subgoal 1: properties of `insideOld` (the inner handler) -/

/-- `insideOld` on a leaf `Var (.Local n)` with `n` inout: returns
    canonical `Old`, sets the changed flag. -/
theorem insideOld_inout_var
    (s : PushOldState) (b : Bool) (n : Identifier) (src : Option FileRange)
    (hIn : n.text ∈ s.inoutNames) :
    ((insideOld ⟨.Var (.Local n), src⟩).run b).run s
      = ((⟨.Old ⟨.Var (.Local n), src⟩, src⟩, true), s) := by
  show ((insideOld _).run b).run s = _
  simp only [insideOld]
  simp [getThe, MonadStateOf.get, set, MonadState.set, StateT.run,
        StateT.bind, bind, pure, StateT.pure, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map, hIn]

/-- `insideOld` on a leaf `Var (.Local n)` with `n` not inout: identity. -/
theorem insideOld_non_inout_var
    (s : PushOldState) (b : Bool) (n : Identifier) (src : Option FileRange)
    (hOut : n.text ∉ s.inoutNames) :
    ((insideOld ⟨.Var (.Local n), src⟩).run b).run s
      = ((⟨.Var (.Local n), src⟩, b), s) := by
  show ((insideOld _).run b).run s = _
  simp only [insideOld]
  simp [getThe, MonadStateOf.get, set, MonadState.set, StateT.run,
        StateT.bind, bind, pure, StateT.pure, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map, hOut]

/-- `insideOld` on a `.Old inner`: drops the wrapper (warning emitted).
    Critically, returns `inner` unchanged (so any canonical structure
    inside `inner` is preserved). -/
theorem insideOld_old
    (s : PushOldState) (b : Bool) (inner : StmtExprMd) (src : Option FileRange) :
    ∃ s', ((insideOld ⟨.Old inner, src⟩).run b).run s = ((inner, b), s') := by
  show ∃ s', ((insideOld _).run b).run s = _
  simp only [insideOld]
  refine ⟨{ s with diagnostics := s.diagnostics ++
                                  [diagnosticFromSource src "nested `old(...)` has no effect" .Warning] }, ?_⟩
  simp [warn, getThe, MonadStateOf.get, set, MonadState.set,
        StateT.run, StateT.bind, bind, pure, StateT.pure, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet]

/-- `insideOld` on anything else (not `Var Local`, not `Old`): identity. -/
theorem insideOld_other
    (s : PushOldState) (b : Bool) (expr : StmtExprMd)
    (hVar : ∀ n, expr.val ≠ .Var (.Local n))
    (hOld : ∀ inner, expr.val ≠ .Old inner) :
    ((insideOld expr).run b).run s = ((expr, b), s) := by
  show ((insideOld _).run b).run s = _
  simp only [insideOld]
  cases h : expr.val
  case Var v =>
    cases v
    case Local n => exact absurd h (hVar n)
    case Field _ _ => simp [StateT.run, StateT.pure, pure]
    case Declare _ => simp [StateT.run, StateT.pure, pure]
  case Old inner => exact absurd h (hOld inner)
  all_goals simp [StateT.run, StateT.pure, pure]

/-! ## Subgoal 2: `subOlds` of leaves -/

/-- An expression with no `StmtExprMd` children has empty `subOlds`. -/
theorem subOlds_literal_int (n : Int) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.LiteralInt n, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

theorem subOlds_literal_bool (b : Bool) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.LiteralBool b, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

theorem subOlds_var_local (n : Identifier) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Var (.Local n), src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- `subOlds` on an `Old`: itself, then `subOlds` of the inner. -/
theorem subOlds_old (inner : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Old inner, src⟩ : StmtExprMd) =
    (⟨.Old inner, src⟩ : StmtExprMd) :: inner.subOlds := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.LiteralString`: empty. -/
theorem subOlds_literal_string (s : String) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.LiteralString s, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.LiteralDecimal`: empty. -/
theorem subOlds_literal_decimal (d : Decimal) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.LiteralDecimal d, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.New ref`: empty. -/
theorem subOlds_new (ref : Identifier) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.New ref, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.This`: empty. -/
theorem subOlds_this (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.This, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.Abstract`: empty. -/
theorem subOlds_abstract (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Abstract, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.All`: empty. -/
theorem subOlds_all (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.All, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.Exit label`: empty. -/
theorem subOlds_exit (label : String) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Exit label, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-! ## Subgoal 3: `mapStmtExprM insideOld` produces canonical `Old`s -/

/-- `AllSubOldsCanonical` holds vacuously when `subOlds` is empty. -/
theorem allSubOldsCanonical_of_subOlds_nil
    {inoutNames : List String} {e : StmtExprMd}
    (h : e.subOlds = []) :
    AllSubOldsCanonical inoutNames e := by
  intro subOld hSub
  rw [h] at hSub
  cases hSub

/-- Helper: `mapStmtExprM insideOld` on a literal int: result = input. -/
private theorem mapStmtExprM_insideOld_literalInt_id
    (s : PushOldState) (b : Bool) (n : Int) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.LiteralInt n, src⟩).run b).run s).fst.fst =
    ⟨.LiteralInt n, src⟩ := by
  -- mapStmtExprM is bottom-up; the leaf case is `pure expr`, then `insideOld`
  -- on a literal returns it unchanged.
  simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure,
        pure, getThe, MonadStateOf.get, set, MonadState.set, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map]

/-- Specialized lemma: `mapStmtExprM insideOld` on a literal-int leaf. -/
private theorem mapStmtExprM_insideOld_canonical_literalInt
    (s : PushOldState) (b : Bool) (n : Int) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.LiteralInt n, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_literalInt_id]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_literal_int n src)

/-- Helper: `mapStmtExprM insideOld` on a literal bool: result = input. -/
private theorem mapStmtExprM_insideOld_literalBool_id
    (s : PushOldState) (b : Bool) (v : Bool) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.LiteralBool v, src⟩).run b).run s).fst.fst =
    ⟨.LiteralBool v, src⟩ := by
  simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure,
        pure, getThe, MonadStateOf.get, set, MonadState.set, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map]

private theorem mapStmtExprM_insideOld_canonical_literalBool
    (s : PushOldState) (b : Bool) (v : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.LiteralBool v, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_literalBool_id]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_literal_bool v src)

/-- The `Var (.Local n)` case for subgoal 3: the result is either
    `⟨.Var (.Local n), src⟩` (n not inout) or `⟨.Old ⟨.Var (.Local n), src⟩, src⟩`
    (n inout). Either way, every Old subterm is canonical. -/
private theorem mapStmtExprM_insideOld_canonical_varLocal
    (s : PushOldState) (b : Bool) (n : Identifier) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Var (.Local n), src⟩).run b).run s).fst.fst := by
  -- mapStmtExprM is bottom-up; on a leaf .Var (.Local n), `pure expr`,
  -- then `insideOld` is applied. Two sub-cases: n inout or not.
  by_cases hIn : n.text ∈ s.inoutNames
  · -- inout: insideOld wraps in .Old
    have hRes : (((mapStmtExprM insideOld ⟨.Var (.Local n), src⟩).run b).run s).fst.fst =
                ⟨.Old ⟨.Var (.Local n), src⟩, src⟩ := by
      simp [mapStmtExprM]
      exact congrArg Prod.fst (congrArg Prod.fst (insideOld_inout_var s b n src hIn))
    rw [hRes]
    -- Now show subOlds = [⟨.Old ⟨.Var (.Local n), src⟩, src⟩] is canonical.
    intro subOld hSub
    rw [subOlds_old, subOlds_var_local] at hSub
    simp at hSub
    -- subOld = ⟨.Old ⟨.Var (.Local n), src⟩, src⟩
    refine ⟨n, src, src, ?_, hIn⟩
    rw [hSub]
  · -- not inout: insideOld leaves it
    have hRes : (((mapStmtExprM insideOld ⟨.Var (.Local n), src⟩).run b).run s).fst.fst =
                ⟨.Var (.Local n), src⟩ := by
      simp [mapStmtExprM]
      exact congrArg Prod.fst (congrArg Prod.fst (insideOld_non_inout_var s b n src hIn))
    rw [hRes]
    exact allSubOldsCanonical_of_subOlds_nil (subOlds_var_local n src)

/-- `mapStmtExprM insideOld` on `.LiteralString`: identity. -/
private theorem mapStmtExprM_insideOld_literalString_id
    (s : PushOldState) (b : Bool) (str : String) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.LiteralString str, src⟩).run b).run s).fst.fst =
    ⟨.LiteralString str, src⟩ := by
  simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
        getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_literalString
    (s : PushOldState) (b : Bool) (str : String) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.LiteralString str, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_literalString_id]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_literal_string str src)

/-- `mapStmtExprM insideOld` on `.LiteralDecimal`: identity. -/
private theorem mapStmtExprM_insideOld_literalDecimal_id
    (s : PushOldState) (b : Bool) (d : Decimal) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.LiteralDecimal d, src⟩).run b).run s).fst.fst =
    ⟨.LiteralDecimal d, src⟩ := by
  simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
        getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_literalDecimal
    (s : PushOldState) (b : Bool) (d : Decimal) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.LiteralDecimal d, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_literalDecimal_id]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_literal_decimal d src)

/-- `mapStmtExprM insideOld` on `.New ref`: identity (leaf, insideOld
    falls through). -/
private theorem mapStmtExprM_insideOld_new_id
    (s : PushOldState) (b : Bool) (ref : Identifier) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.New ref, src⟩).run b).run s).fst.fst =
    ⟨.New ref, src⟩ := by
  simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure,
        pure, getThe, MonadStateOf.get, set, MonadState.set, StateT.set,
        StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift,
        Functor.map, StateT.map]

private theorem mapStmtExprM_insideOld_canonical_new
    (s : PushOldState) (b : Bool) (ref : Identifier) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.New ref, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_new_id]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_new ref src)

/-- Generic leaf-case proof: any leaf with empty subOlds whose
    `mapStmtExprM insideOld` result equals the input is canonical. -/
private theorem mapStmtExprM_insideOld_canonical_this
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.This, src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.This, src⟩).run b).run s).fst.fst =
              ⟨.This, src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_this src)

private theorem mapStmtExprM_insideOld_canonical_abstract
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Abstract, src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.Abstract, src⟩).run b).run s).fst.fst =
              ⟨.Abstract, src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_abstract src)

private theorem mapStmtExprM_insideOld_canonical_all
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.All, src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.All, src⟩).run b).run s).fst.fst =
              ⟨.All, src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_all src)

private theorem mapStmtExprM_insideOld_canonical_exit
    (s : PushOldState) (b : Bool) (label : String) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Exit label, src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.Exit label, src⟩).run b).run s).fst.fst =
              ⟨.Exit label, src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_exit label src)

private theorem mapStmtExprM_insideOld_canonical_varDeclare
    (s : PushOldState) (b : Bool) (p : Parameter) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Var (.Declare p), src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.Var (.Declare p), src⟩).run b).run s).fst.fst =
              ⟨.Var (.Declare p), src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  have : StmtExprMd.subOlds (⟨.Var (.Declare p), src⟩ : StmtExprMd) = [] := by
    rw [StmtExprMd.subOlds]
  exact allSubOldsCanonical_of_subOlds_nil this

/-- subOlds of `.Assigned n` is `n.subOlds`. -/
theorem subOlds_assigned (n : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Assigned n, src⟩ : StmtExprMd) = n.subOlds := by
  rw [StmtExprMd.subOlds]

/-- Reduction for `.Assigned`: rebuilds with the inner rewritten. -/
private theorem mapStmtExprM_insideOld_assigned_run
    (s : PushOldState) (b : Bool) (n : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Assigned n, src⟩).run b).run s).fst.fst =
    ⟨.Assigned (((mapStmtExprM insideOld n).run b).run s).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld n b) s = res
  obtain ⟨⟨n', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

/-- Canonical for `.Assigned n` given canonical for the rewritten inner. -/
private theorem mapStmtExprM_insideOld_canonical_assigned
    (s : PushOldState) (b : Bool) (n : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld n).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Assigned n, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_assigned_run]
  intro subOld hSub
  rw [subOlds_assigned] at hSub
  exact ih subOld hSub

/-- subOlds of `.Fresh v` is `v.subOlds`. -/
theorem subOlds_fresh (v : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Fresh v, src⟩ : StmtExprMd) = v.subOlds := by
  rw [StmtExprMd.subOlds]

/-- Reduction for `.Fresh`: rebuilds with the inner rewritten. -/
private theorem mapStmtExprM_insideOld_fresh_run
    (s : PushOldState) (b : Bool) (v : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Fresh v, src⟩).run b).run s).fst.fst =
    ⟨.Fresh (((mapStmtExprM insideOld v).run b).run s).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld v b) s = res
  obtain ⟨⟨v', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_fresh
    (s : PushOldState) (b : Bool) (v : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld v).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Fresh v, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_fresh_run]
  intro subOld hSub
  rw [subOlds_fresh] at hSub
  exact ih subOld hSub

/-- subOlds of `.Var (.Field target fn)` is `target.subOlds`. -/
theorem subOlds_var_field (target : StmtExprMd) (fn : Identifier) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Var (.Field target fn), src⟩ : StmtExprMd) = target.subOlds := by
  rw [StmtExprMd.subOlds]

/-- Reduction for `.Var (.Field target fn)`: rebuilds with rewritten target. -/
private theorem mapStmtExprM_insideOld_varField_run
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (fn : Identifier) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Var (.Field target fn), src⟩).run b).run s).fst.fst =
    ⟨.Var (.Field (((mapStmtExprM insideOld target).run b).run s).fst.fst fn), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld target b) s = res
  obtain ⟨⟨target', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_varField
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (fn : Identifier) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld target).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Var (.Field target fn), src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_varField_run]
  intro subOld hSub
  rw [subOlds_var_field] at hSub
  exact ih subOld hSub

/-- subOlds of `.AsType target ty` is `target.subOlds`. -/
theorem subOlds_asType (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.AsType target ty, src⟩ : StmtExprMd) = target.subOlds := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_asType_run
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.AsType target ty, src⟩).run b).run s).fst.fst =
    ⟨.AsType (((mapStmtExprM insideOld target).run b).run s).fst.fst ty, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld target b) s = res
  obtain ⟨⟨target', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_asType
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld target).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.AsType target ty, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_asType_run]
  intro subOld hSub
  rw [subOlds_asType] at hSub
  exact ih subOld hSub

/-- subOlds of `.IsType target ty` is `target.subOlds`. -/
theorem subOlds_isType (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.IsType target ty, src⟩ : StmtExprMd) = target.subOlds := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_isType_run
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.IsType target ty, src⟩).run b).run s).fst.fst =
    ⟨.IsType (((mapStmtExprM insideOld target).run b).run s).fst.fst ty, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld target b) s = res
  obtain ⟨⟨target', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_isType
    (s : PushOldState) (b : Bool) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld target).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.IsType target ty, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_isType_run]
  intro subOld hSub
  rw [subOlds_isType] at hSub
  exact ih subOld hSub

/-- subOlds of `.Assume cond` is `cond.subOlds`. -/
theorem subOlds_assume (cond : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Assume cond, src⟩ : StmtExprMd) = cond.subOlds := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_assume_run
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Assume cond, src⟩).run b).run s).fst.fst =
    ⟨.Assume (((mapStmtExprM insideOld cond).run b).run s).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld cond b) s = res
  obtain ⟨⟨cond', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_assume
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld cond).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Assume cond, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_assume_run]
  intro subOld hSub
  rw [subOlds_assume] at hSub
  exact ih subOld hSub

/-- subOlds of `.ContractOf ty fn` is `fn.subOlds`. -/
theorem subOlds_contractOf (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.ContractOf ty fn, src⟩ : StmtExprMd) = fn.subOlds := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_contractOf_run
    (s : PushOldState) (b : Bool) (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.ContractOf ty fn, src⟩).run b).run s).fst.fst =
    ⟨.ContractOf ty (((mapStmtExprM insideOld fn).run b).run s).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld fn b) s = res
  obtain ⟨⟨fn', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_contractOf
    (s : PushOldState) (b : Bool) (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld fn).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.ContractOf ty fn, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_contractOf_run]
  intro subOld hSub
  rw [subOlds_contractOf] at hSub
  exact ih subOld hSub

/-- subOlds of `.ReferenceEquals lhs rhs` is the union of children. -/
theorem subOlds_referenceEquals (lhs rhs : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd) =
    lhs.subOlds ++ rhs.subOlds := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.Assert c` is `c.condition.subOlds`. -/
theorem subOlds_assert (c : Condition) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Assert c, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds c.condition := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.ProveBy v p` is `v.subOlds ++ p.subOlds`. -/
theorem subOlds_proveBy (v p : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.ProveBy v p, src⟩ : StmtExprMd) = v.subOlds ++ p.subOlds := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.PureFieldUpdate t fn nv` is `t.subOlds ++ nv.subOlds`. -/
theorem subOlds_pureFieldUpdate (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd) = t.subOlds ++ nv.subOlds := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.Return none` is empty. -/
theorem subOlds_return_none (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Return none, src⟩ : StmtExprMd) = [] := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.Return (some v)` is `v.subOlds`. -/
theorem subOlds_return_some (v : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Return (some v), src⟩ : StmtExprMd) = v.subOlds := by
  rw [StmtExprMd.subOlds]

/-- Reduction for `.Return none`: returns `.Return none` unchanged. -/
private theorem mapStmtExprM_insideOld_return_none_run
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Return none, src⟩).run b).run s).fst.fst =
    ⟨.Return none, src⟩ := by
  rw [mapStmtExprM]
  simp [StateT.run, StateT.bind, bind, StateT.pure, pure,
        List.attach, List.attachWith, List.mapM_nil,
        Option.attach, Option.attachWith, Option.mapM,
        insideOld, liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_return_none
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Return none, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_return_none_run]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_return_none src)

/-- Reduction for `.Return (some v)`: rebuild with the inner rewritten. -/
private theorem mapStmtExprM_insideOld_return_some_run
    (s : PushOldState) (b : Bool) (v : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Return (some v), src⟩).run b).run s).fst.fst =
    ⟨.Return (some (((mapStmtExprM insideOld v).run b).run s).fst.fst), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hM : (mapStmtExprM insideOld v b) s = res
  obtain ⟨⟨v', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_return_some
    (s : PushOldState) (b : Bool) (v : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld v).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Return (some v), src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_return_some_run]
  intro subOld hSub
  rw [subOlds_return_some] at hSub
  exact ih subOld hSub

-- ReferenceEquals two-child case: structurally similar to one-child cases
-- but the state threading complicates the reduction proof. Deferred.

/-- `insideOld` preserves `inoutNames` (only writes diagnostics or inner Bool). -/
theorem insideOld_preserves_inoutNames
    (s : PushOldState) (b : Bool) (e : StmtExprMd) :
    (((insideOld e).run b).run s).snd.inoutNames = s.inoutNames := by
  unfold insideOld
  cases h : e.val with
  | Var v =>
    cases v with
    | Local nm =>
      by_cases hIn : nm.text ∈ s.inoutNames
      · simp [h, hIn, StateT.run, StateT.bind, bind, StateT.pure, pure,
              getThe, MonadStateOf.get, set, MonadState.set, StateT.set,
              StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
      · simp [h, hIn, StateT.run, StateT.bind, bind, StateT.pure, pure,
              getThe, MonadStateOf.get, StateT.lift, StateT.get,
              liftM, MonadLift.monadLift, monadLift]
    | Field _ _ =>
      simp [h, StateT.run, StateT.pure, pure]
    | Declare _ =>
      simp [h, StateT.run, StateT.pure, pure]
  | Old inner =>
    simp only [h, StateT.run, StateT.bind, bind, StateT.pure, pure,
               warn, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
               liftM, MonadLift.monadLift, monadLift, StateT.lift]
  | _ => simp [h, StateT.run, StateT.pure, pure]

/-- `xs.attach.mapM (fun ⟨e, _⟩ => mapStmtExprM insideOld e) = xs.mapM (mapStmtExprM insideOld)`. -/
private theorem mapStmtExprM_insideOld_attach_mapM_eq (xs : List StmtExprMd) :
    (xs.attach.mapM fun (e : { e // e ∈ xs }) => mapStmtExprM insideOld e.val)
      = xs.mapM (mapStmtExprM insideOld) := by
  rw [List.mapM_subtype (g := fun e => mapStmtExprM insideOld e) (by intros; rfl)]
  rw [List.unattach_attach]

/-- Generic list-preservation helper: if every element of `xs` preserves
    `inoutNames` (per the hypothesis `hPres`), then so does `xs.mapM (mapStmtExprM insideOld)`.
    Useful for compound list-bearing cases inside the strong induction. -/
private theorem listMapM_insideOld_preserves_inoutNames_of
    (xs : List StmtExprMd)
    (hPres : ∀ x ∈ xs, ∀ (s' : PushOldState) (b' : Bool),
              (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames)
    (s : PushOldState) (b : Bool) :
    ((xs.mapM (mapStmtExprM insideOld)).run b s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s b with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapStmtExprM insideOld x b) s = resX
    obtain ⟨⟨x', bX⟩, sX⟩ := resX
    have hPresX := hPres x List.mem_cons_self s b
    have hSX : (((mapStmtExprM insideOld x).run b).run s).snd = sX := by
      show (mapStmtExprM insideOld x b s).snd = sX
      rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM (mapStmtExprM insideOld) bX sX = resRest
    obtain ⟨⟨ys', bRest⟩, sRest⟩ := resRest
    have hRestPres : ((xs.mapM (mapStmtExprM insideOld)).run bX sX).snd.inoutNames = sX.inoutNames := by
      apply ih
      intro y hy s' b'
      exact hPres y (List.mem_cons_of_mem _ hy) s' b'
    have hSR : (xs.mapM (mapStmtExprM insideOld) bX sX).snd = sRest := by rw [hRest]
    have hSR' : ((xs.mapM (mapStmtExprM insideOld)).run bX sX).snd = sRest := hSR
    rw [hSR'] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

/-- The targets-traversal helper for `.Assign`. Forward declaration so that
    the preserves and canonical theorems can reference it. The preservation
    lemma `mapAssignTargets_preserves_inoutNames` is proved later (after the
    main preserves theorem, since it depends on it). -/
@[reducible]
private def mapAssignTargets (targets : List (AstNode Variable)) :
    StateT Bool PushOldM (List (AstNode Variable)) :=
  targets.attach.mapM
    (fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprM insideOld target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v)

/-- Per-target processor (unattached). Equivalent to the lambda inside
    `mapAssignTargets`, but takes a plain `AstNode Variable` arg so we can
    induct on a list without the subtype-membership wrapper. -/
private def mapAssignTargetsAux (v : AstNode Variable) :
    StateT Bool PushOldM (AstNode Variable) := do
  let ⟨vv, vs⟩ := v
  match vv with
  | .Field target fieldName =>
    pure ⟨Variable.Field (← mapStmtExprM insideOld target) fieldName, vs⟩
  | .Local _ | .Declare _ => pure v

/-- The lambda inside `mapAssignTargets` is exactly `mapAssignTargetsAux ∘ Subtype.val`. -/
private theorem mapAssignTargets_eq_unattached (targets : List (AstNode Variable)) :
    mapAssignTargets targets = targets.mapM mapAssignTargetsAux := by
  unfold mapAssignTargets
  rw [List.mapM_subtype (g := mapAssignTargetsAux) (by
    intro v _hMem
    unfold mapAssignTargetsAux
    obtain ⟨vv, vs⟩ := v
    cases vv <;> rfl)]
  rw [List.unattach_attach]

/-- Per-target preservation, parameterized by the input list `xs` so that
    the `Field` case can use the membership hypothesis. -/
private theorem mapAssignTargetsAux_preserves_inoutNames_of
    (xs : List (AstNode Variable))
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ xs →
              ∀ (s' : PushOldState) (b' : Bool),
              (((mapStmtExprM insideOld tgt).run b').run s').snd.inoutNames = s'.inoutNames)
    (v : AstNode Variable) (hMemV : v ∈ xs) (s : PushOldState) (b : Bool) :
    ((mapAssignTargetsAux v).run b s).snd.inoutNames = s.inoutNames := by
  unfold mapAssignTargetsAux
  obtain ⟨vv, vs⟩ := v
  cases vv with
  | Field target fieldName =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hMt : (mapStmtExprM insideOld target b) s = res
    obtain ⟨⟨t', b'⟩, s'⟩ := res
    have hPHead := hPres target fieldName vs hMemV s b
    have : (((mapStmtExprM insideOld target).run b).run s).snd = s' := by
      show (mapStmtExprM insideOld target b s).snd = s'
      rw [hMt]
    rw [this] at hPHead
    exact hPHead
  | Local _ => simp [StateT.run, StateT.pure, pure]
  | Declare _ => simp [StateT.run, StateT.pure, pure]

/-- List-mapM preservation for `mapAssignTargetsAux`, parameterized by the
    enclosing list `xs` so we can index into it for membership hypotheses. -/
private theorem listMapM_mapAssignTargetsAux_preserves_inoutNames_of
    (xs : List (AstNode Variable))
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ xs →
              ∀ (s' : PushOldState) (b' : Bool),
              (((mapStmtExprM insideOld tgt).run b').run s').snd.inoutNames = s'.inoutNames)
    (s : PushOldState) (b : Bool) :
    ((xs.mapM mapAssignTargetsAux).run b s).snd.inoutNames = s.inoutNames := by
  -- Generalize over a sublist `ys ⊆ xs` so the induction works.
  suffices hGen : ∀ (ys : List (AstNode Variable)),
      (∀ y ∈ ys, y ∈ xs) →
      ∀ (s' : PushOldState) (b' : Bool),
      ((ys.mapM mapAssignTargetsAux).run b' s').snd.inoutNames = s'.inoutNames by
    exact hGen xs (fun _ h => h) s b
  intro ys hYsSub
  induction ys with
  | nil =>
    intro s' b'
    simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons y ys ihL =>
    intro s' b'
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapAssignTargetsAux y b') s' = resY
    obtain ⟨⟨y', bY⟩, sY⟩ := resY
    have hPresY := mapAssignTargetsAux_preserves_inoutNames_of xs hPres y
                    (hYsSub y List.mem_cons_self) s' b'
    have hSY : ((mapAssignTargetsAux y).run b' s').snd = sY := by
      show (mapAssignTargetsAux y b' s').snd = sY
      rw [hM]
    rw [hSY] at hPresY
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : ys.mapM mapAssignTargetsAux bY sY = resRest
    obtain ⟨⟨ys', bRest⟩, sRest⟩ := resRest
    have hYsSubTail : ∀ z ∈ ys, z ∈ xs :=
      fun z hz => hYsSub z (List.mem_cons_of_mem _ hz)
    have hTailRes := ihL hYsSubTail sY bY
    have hSR' : ((ys.mapM mapAssignTargetsAux).run bY sY).snd = sRest := by
      show (ys.mapM mapAssignTargetsAux bY sY).snd = sRest
      rw [hRest]
    rw [hSR'] at hTailRes
    show sRest.inoutNames = s'.inoutNames
    exact hTailRes.trans hPresY

/-- `mapAssignTargets` preservation parameterized by a per-target preservation
    hypothesis. The `ih` from the strong-induction wrapper supplies the
    per-element preservation. -/
private theorem mapAssignTargets_preserves_inoutNames_ofIH
    (targets : List (AstNode Variable)) (s : PushOldState) (b : Bool)
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ targets →
              ∀ (s' : PushOldState) (b' : Bool),
              (((mapStmtExprM insideOld tgt).run b').run s').snd.inoutNames = s'.inoutNames) :
    (mapAssignTargets targets b s).snd.inoutNames = s.inoutNames := by
  rw [mapAssignTargets_eq_unattached]
  exact listMapM_mapAssignTargetsAux_preserves_inoutNames_of targets hPres s b

/-- The result of `mapStmtExprM insideOld ⟨.Assign t v, src⟩` reduces (by `rfl`)
    to an explicit shape using `mapAssignTargets`. This is the bridge that
    converts the dependent-match elaboration of the inline lambda into a
    `mapAssignTargets` reference. -/
private theorem mapStmtExprM_assign_run_eq
    (s : PushOldState) (b : Bool) (targets : List (AstNode Variable))
    (value : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Assign targets value, src⟩).run b).run s) =
    (((⟨.Assign (mapAssignTargets targets b s).fst.fst
                (((mapStmtExprM insideOld value).run
                    (mapAssignTargets targets b s).fst.snd).run
                  (mapAssignTargets targets b s).snd).fst.fst, src⟩ : StmtExprMd),
        (((mapStmtExprM insideOld value).run
            (mapAssignTargets targets b s).fst.snd).run
          (mapAssignTargets targets b s).snd).fst.snd),
      (((mapStmtExprM insideOld value).run
          (mapAssignTargets targets b s).fst.snd).run
        (mapAssignTargets targets b s).snd).snd) := by
  show (mapStmtExprM insideOld ⟨.Assign targets value, src⟩ b s) = _
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  rfl

/-- `mapStmtExprM insideOld` preserves `inoutNames` in the threaded state.
    Proved by strong induction with case-bash. -/
theorem mapStmtExprM_insideOld_preserves_inoutNames
    (s : PushOldState) (b : Bool) (e : StmtExprMd) :
    (((mapStmtExprM insideOld e).run b).run s).snd.inoutNames = s.inoutNames := by
  induction h_sz : sizeOf e using Nat.strongRecOn generalizing e s b with
  | ind n ih =>
    cases hVal : e.val with
    | LiteralInt v =>
      have he : e = ⟨.LiteralInt v, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | LiteralBool v =>
      have he : e = ⟨.LiteralBool v, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | LiteralString str =>
      have he : e = ⟨.LiteralString str, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | LiteralDecimal d =>
      have he : e = ⟨.LiteralDecimal d, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | New ref =>
      have he : e = ⟨.New ref, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | This =>
      have he : e = ⟨.This, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | Abstract =>
      have he : e = ⟨.Abstract, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | All =>
      have he : e = ⟨.All, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | Exit label =>
      have he : e = ⟨.Exit label, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | Hole det ty =>
      have he : e = ⟨.Hole det ty, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
            getThe, MonadStateOf.get, StateT.lift, StateT.get,
            liftM, MonadLift.monadLift, monadLift]
    | Var v =>
      cases v with
      | Local nm =>
        have he : e = ⟨.Var (.Local nm), e.source⟩ := by cases e; simp_all
        rw [he]
        rw [mapStmtExprM]
        by_cases hIn : nm.text ∈ s.inoutNames
        · simp [insideOld, hIn, StateT.run, StateT.bind, bind, StateT.pure, pure,
                getThe, MonadStateOf.get, set, MonadState.set, StateT.set,
                StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
        · simp [insideOld, hIn, StateT.run, StateT.bind, bind, StateT.pure, pure,
                getThe, MonadStateOf.get, StateT.lift, StateT.get,
                liftM, MonadLift.monadLift, monadLift]
      | Declare p =>
        have he : e = ⟨.Var (.Declare p), e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
              getThe, MonadStateOf.get, StateT.lift, StateT.get,
              liftM, MonadLift.monadLift, monadLift]
      | Field target fn =>
        have he : e = ⟨.Var (.Field target fn), e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSize : sizeOf target < n := by
          have hVal_size : sizeOf e.val = 1 + (1 + sizeOf target + sizeOf fn) := by
            rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hPres := ih (sizeOf target) hSize s b target rfl
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
        generalize hM : (mapStmtExprM insideOld target b) s = res
        obtain ⟨⟨target', b'⟩, s'⟩ := res
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        have : (((mapStmtExprM insideOld target).run b).run s).snd = s' := by
          show (mapStmtExprM insideOld target b s).snd = s'
          rw [hM]
        rw [this] at hPres
        exact hPres
    | Assigned m =>
      have he : e = ⟨.Assigned m, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf m < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf m := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf m) hSize s b m rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld m b) s = res
      obtain ⟨⟨m', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld m).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld m b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | Fresh v =>
      have he : e = ⟨.Fresh v, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf v < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf v := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf v) hSize s b v rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld v b) s = res
      obtain ⟨⟨v', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld v).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld v b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | AsType target ty =>
      have he : e = ⟨.AsType target ty, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf target < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf target) hSize s b target rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld target b) s = res
      obtain ⟨⟨t', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld target).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld target b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | IsType target ty =>
      have he : e = ⟨.IsType target ty, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf target < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf target) hSize s b target rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld target b) s = res
      obtain ⟨⟨t', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld target).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld target b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | Assume cond =>
      have he : e = ⟨.Assume cond, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf cond < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf cond := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf cond) hSize s b cond rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld cond b) s = res
      obtain ⟨⟨c', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld cond).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld cond b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | ContractOf ty fn =>
      have he : e = ⟨.ContractOf ty fn, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf fn < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf ty + sizeOf fn := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf fn) hSize s b fn rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld fn b) s = res
      obtain ⟨⟨f', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld fn).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld fn b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | Old inner =>
      have he : e = ⟨.Old inner, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf inner < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf inner := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hPres := ih (sizeOf inner) hSize s b inner rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld inner b) s = res
      obtain ⟨⟨inner', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift, warn,
                 modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
      have : (((mapStmtExprM insideOld inner).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld inner b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | Return v =>
      cases v with
      | none =>
        have he : e = ⟨.Return none, e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        simp [insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
              Option.attach, Option.attachWith, Option.mapM,
              getThe, MonadStateOf.get, StateT.lift, StateT.get,
              liftM, MonadLift.monadLift, monadLift]
      | some r =>
        have he : e = ⟨.Return (some r), e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSize : sizeOf r < n := by
          have hVal_size : sizeOf e.val = 1 + (1 + sizeOf r) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hPres := ih (sizeOf r) hSize s b r rfl
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Option.attach, Option.attachWith, Option.mapM,
                   Functor.map, StateT.map]
        generalize hM : (mapStmtExprM insideOld r b) s = res
        obtain ⟨⟨r', b'⟩, s'⟩ := res
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        have : (((mapStmtExprM insideOld r).run b).run s).snd = s' := by
          show (mapStmtExprM insideOld r b s).snd = s'
          rw [hM]
        rw [this] at hPres
        exact hPres
    | Assert c =>
      have he : e = ⟨.Assert c, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSize : sizeOf c.condition < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf c := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        have := Condition.sizeOf_condition_lt c
        omega
      have hPres := ih (sizeOf c.condition) hSize s b c.condition rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hM : (mapStmtExprM insideOld c.condition b) s = res
      obtain ⟨⟨c', b'⟩, s'⟩ := res
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      have : (((mapStmtExprM insideOld c.condition).run b).run s).snd = s' := by
        show (mapStmtExprM insideOld c.condition b s).snd = s'
        rw [hM]
      rw [this] at hPres
      exact hPres
    | ProveBy v p =>
      have he : e = ⟨.ProveBy v p, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSizeV : sizeOf v < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf v + sizeOf p := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hSizeP : sizeOf p < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf v + sizeOf p := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hMv : (mapStmtExprM insideOld v b) s = resV
      obtain ⟨⟨v', bV⟩, sV⟩ := resV
      have hPresV := ih (sizeOf v) hSizeV s b v rfl
      have hSV : (((mapStmtExprM insideOld v).run b).run s).snd = sV := by
        show (mapStmtExprM insideOld v b s).snd = sV
        rw [hMv]
      rw [hSV] at hPresV
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hMp : (mapStmtExprM insideOld p bV) sV = resP
      obtain ⟨⟨p', bP⟩, sP⟩ := resP
      have hPresP := ih (sizeOf p) hSizeP sV bV p rfl
      have hSP : (((mapStmtExprM insideOld p).run bV).run sV).snd = sP := by
        show (mapStmtExprM insideOld p bV sV).snd = sP
        rw [hMp]
      rw [hSP] at hPresP
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      exact hPresP.trans hPresV
    | ReferenceEquals lhs rhs =>
      have he : e = ⟨.ReferenceEquals lhs rhs, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSizeL : sizeOf lhs < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf lhs + sizeOf rhs := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hSizeR : sizeOf rhs < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf lhs + sizeOf rhs := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hML : (mapStmtExprM insideOld lhs b) s = resL
      obtain ⟨⟨lhs', bL⟩, sL⟩ := resL
      have hPresL := ih (sizeOf lhs) hSizeL s b lhs rfl
      have hSL : (((mapStmtExprM insideOld lhs).run b).run s).snd = sL := by
        show (mapStmtExprM insideOld lhs b s).snd = sL
        rw [hML]
      rw [hSL] at hPresL
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hMR : (mapStmtExprM insideOld rhs bL) sL = resR
      obtain ⟨⟨rhs', bR⟩, sR⟩ := resR
      have hPresR := ih (sizeOf rhs) hSizeR sL bL rhs rfl
      have hSR : (((mapStmtExprM insideOld rhs).run bL).run sL).snd = sR := by
        show (mapStmtExprM insideOld rhs bL sL).snd = sR
        rw [hMR]
      rw [hSR] at hPresR
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      exact hPresR.trans hPresL
    | IfThenElse cond th el =>
      cases el with
      | none =>
        have he : e = ⟨.IfThenElse cond th none, e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSizeC : sizeOf cond < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf cond + sizeOf th + sizeOf (none : Option StmtExprMd) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hSizeT : sizeOf th < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf cond + sizeOf th + sizeOf (none : Option StmtExprMd) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Option.attach, Option.attachWith, Option.mapM, Functor.map, StateT.map]
        generalize hMc : (mapStmtExprM insideOld cond b) s = resC
        obtain ⟨⟨cond', bC⟩, sC⟩ := resC
        have hPresC := ih (sizeOf cond) hSizeC s b cond rfl
        have hSC : (((mapStmtExprM insideOld cond).run b).run s).snd = sC := by
          show (mapStmtExprM insideOld cond b s).snd = sC
          rw [hMc]
        rw [hSC] at hPresC
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
        generalize hMt : (mapStmtExprM insideOld th bC) sC = resT
        obtain ⟨⟨th', bT⟩, sT⟩ := resT
        have hPresT := ih (sizeOf th) hSizeT sC bC th rfl
        have hST : (((mapStmtExprM insideOld th).run bC).run sC).snd = sT := by
          show (mapStmtExprM insideOld th bC sC).snd = sT
          rw [hMt]
        rw [hST] at hPresT
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        exact hPresT.trans hPresC
      | some elE =>
        have he : e = ⟨.IfThenElse cond th (some elE), e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSizeC : sizeOf cond < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hSizeT : sizeOf th < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hSizeE : sizeOf elE < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          have : sizeOf (some elE) = 1 + sizeOf elE := rfl
          omega
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Option.attach, Option.attachWith, Option.mapM, Functor.map, StateT.map]
        generalize hMc : (mapStmtExprM insideOld cond b) s = resC
        obtain ⟨⟨cond', bC⟩, sC⟩ := resC
        have hPresC := ih (sizeOf cond) hSizeC s b cond rfl
        have hSC : (((mapStmtExprM insideOld cond).run b).run s).snd = sC := by
          show (mapStmtExprM insideOld cond b s).snd = sC
          rw [hMc]
        rw [hSC] at hPresC
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
        generalize hMt : (mapStmtExprM insideOld th bC) sC = resT
        obtain ⟨⟨th', bT⟩, sT⟩ := resT
        have hPresT := ih (sizeOf th) hSizeT sC bC th rfl
        have hST : (((mapStmtExprM insideOld th).run bC).run sC).snd = sT := by
          show (mapStmtExprM insideOld th bC sC).snd = sT
          rw [hMt]
        rw [hST] at hPresT
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Functor.map, StateT.map]
        generalize hMe : (mapStmtExprM insideOld elE bT) sT = resE
        obtain ⟨⟨elE', bE⟩, sE⟩ := resE
        have hPresE := ih (sizeOf elE) hSizeE sT bT elE rfl
        have hSE : (((mapStmtExprM insideOld elE).run bT).run sT).snd = sE := by
          show (mapStmtExprM insideOld elE bT sT).snd = sE
          rw [hMe]
        rw [hSE] at hPresE
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        exact (hPresE.trans hPresT).trans hPresC
    | Quantifier mode param trigger body =>
      cases trigger with
      | none =>
        have he : e = ⟨.Quantifier mode param none body, e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSize : sizeOf body < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf mode + sizeOf param +
                           sizeOf (none : Option StmtExprMd) + sizeOf body := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        have hPres := ih (sizeOf body) hSize s b body rfl
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Option.attach, Option.attachWith, Option.mapM,
                   Functor.map, StateT.map]
        generalize hM : (mapStmtExprM insideOld body b) s = res
        obtain ⟨⟨body', b'⟩, s'⟩ := res
        have hSS : (((mapStmtExprM insideOld body).run b).run s).snd = s' := by
          show (mapStmtExprM insideOld body b s).snd = s'
          rw [hM]
        rw [hSS] at hPres
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        exact hPres
      | some tr =>
        have he : e = ⟨.Quantifier mode param (some tr) body, e.source⟩ := by cases e; simp_all
        rw [he, mapStmtExprM]
        have hSizeT : sizeOf tr < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf mode + sizeOf param +
                           sizeOf (some tr) + sizeOf body := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          have : sizeOf (some tr) = 1 + sizeOf tr := rfl
          omega
        have hSizeB : sizeOf body < n := by
          have hVal_size : sizeOf e.val = 1 + sizeOf mode + sizeOf param +
                           sizeOf (some tr) + sizeOf body := by rw [hVal]; rfl
          have := AstNode.sizeOf_val_lt e
          omega
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   Option.attach, Option.attachWith, Option.mapM,
                   Functor.map, StateT.map]
        generalize hMt : (mapStmtExprM insideOld tr b) s = resT
        obtain ⟨⟨tr', bT⟩, sT⟩ := resT
        have hPresT := ih (sizeOf tr) hSizeT s b tr rfl
        have hST : (((mapStmtExprM insideOld tr).run b).run s).snd = sT := by
          show (mapStmtExprM insideOld tr b s).snd = sT
          rw [hMt]
        rw [hST] at hPresT
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
        generalize hMb : (mapStmtExprM insideOld body bT) sT = resB
        obtain ⟨⟨body', bB⟩, sB⟩ := resB
        have hPresB := ih (sizeOf body) hSizeB sT bT body rfl
        have hSB : (((mapStmtExprM insideOld body).run bT).run sT).snd = sB := by
          show (mapStmtExprM insideOld body bT sT).snd = sB
          rw [hMb]
        rw [hSB] at hPresB
        unfold insideOld
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                   liftM, MonadLift.monadLift, monadLift]
        exact hPresB.trans hPresT
    | PureFieldUpdate t fn nv =>
      have he : e = ⟨.PureFieldUpdate t fn nv, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hSizeT : sizeOf t < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf t + sizeOf fn + sizeOf nv := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      have hSizeNv : sizeOf nv < n := by
        have hVal_size : sizeOf e.val = 1 + sizeOf t + sizeOf fn + sizeOf nv := by rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hMt : (mapStmtExprM insideOld t b) s = resT
      obtain ⟨⟨t', bT⟩, sT⟩ := resT
      have hPresT := ih (sizeOf t) hSizeT s b t rfl
      have hST : (((mapStmtExprM insideOld t).run b).run s).snd = sT := by
        show (mapStmtExprM insideOld t b s).snd = sT
        rw [hMt]
      rw [hST] at hPresT
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
      generalize hMnv : (mapStmtExprM insideOld nv bT) sT = resNv
      obtain ⟨⟨nv', bNv⟩, sNv⟩ := resNv
      have hPresNv := ih (sizeOf nv) hSizeNv sT bT nv rfl
      have hSNv : (((mapStmtExprM insideOld nv).run bT).run sT).snd = sNv := by
        show (mapStmtExprM insideOld nv bT sT).snd = sNv
        rw [hMnv]
      rw [hSNv] at hPresNv
      unfold insideOld
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
                 liftM, MonadLift.monadLift, monadLift]
      exact hPresNv.trans hPresT
    | Block stmts label =>
      have he : e = ⟨.Block stmts label, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
      rw [mapStmtExprM_insideOld_attach_mapM_eq]
      have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec := StmtExpr.Block.sizeOf_spec stmts label
      have hPres : ∀ x ∈ stmts, ∀ (s' : PushOldState) (b' : Bool),
          (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames := by
        intro x hx s' b'
        have hxLt : sizeOf x < sizeOf stmts := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        exact ih (sizeOf x) hxSize s' b' x rfl
      have hList := listMapM_insideOld_preserves_inoutNames_of stmts hPres s b
      generalize hM : (stmts.mapM (mapStmtExprM insideOld) b s) = res
      obtain ⟨⟨ys, bY⟩, sY⟩ := res
      have hSnd : ((stmts.mapM (mapStmtExprM insideOld)).run b s).snd = sY := by
        show (stmts.mapM (mapStmtExprM insideOld) b s).snd = sY
        rw [hM]
      rw [hSnd] at hList
      exact hList
    | While cond invs dec body =>
      have he : e = ⟨.While cond invs dec body, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec := StmtExpr.While.sizeOf_spec cond invs dec body
      have hCSz : sizeOf cond < n := by omega
      have hBSz : sizeOf body < n := by omega
      have hInvsPres : ∀ x ∈ invs, ∀ (s' : PushOldState) (b' : Bool),
          (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames := by
        intro x hx s' b'
        have hxLt : sizeOf x < sizeOf invs := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        exact ih (sizeOf x) hxSize s' b' x rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld,
                 Option.attach, Option.attachWith, Option.mapM,
                 Functor.map, StateT.map]
      rw [mapStmtExprM_insideOld_attach_mapM_eq]
      generalize hC : (mapStmtExprM insideOld cond b) s = resC
      obtain ⟨⟨cond', bC⟩, sC⟩ := resC
      have hPresC := ih (sizeOf cond) hCSz s b cond rfl
      have hSC : (((mapStmtExprM insideOld cond).run b).run s).snd = sC := by
        show (mapStmtExprM insideOld cond b s).snd = sC
        rw [hC]
      rw [hSC] at hPresC
      simp only []
      generalize hI : (invs.mapM (mapStmtExprM insideOld) bC) sC = resI
      obtain ⟨⟨invs', bI⟩, sI⟩ := resI
      have hPresI : ((invs.mapM (mapStmtExprM insideOld)).run bC sC).snd.inoutNames = sC.inoutNames :=
        listMapM_insideOld_preserves_inoutNames_of invs hInvsPres sC bC
      have hSI : (invs.mapM (mapStmtExprM insideOld) bC sC).snd = sI := by rw [hI]
      have hSI' : ((invs.mapM (mapStmtExprM insideOld)).run bC sC).snd = sI := hSI
      rw [hSI'] at hPresI
      cases dec with
      | none =>
        simp only [Option.attach, Option.attachWith, Option.mapM, StateT.pure, pure]
        generalize hBd : (mapStmtExprM insideOld body bI) sI = resBd
        obtain ⟨⟨body', bBd⟩, sBd⟩ := resBd
        have hPresBd := ih (sizeOf body) hBSz sI bI body rfl
        have hSBd : (((mapStmtExprM insideOld body).run bI).run sI).snd = sBd := by
          show (mapStmtExprM insideOld body bI sI).snd = sBd
          rw [hBd]
        rw [hSBd] at hPresBd
        exact (hPresBd.trans hPresI).trans hPresC
      | some d =>
        have hDecSpec : sizeOf (some d) = 1 + sizeOf d := rfl
        have hDSz : sizeOf d < n := by omega
        simp only [Option.attach, Option.attachWith, Option.mapM, StateT.pure, pure,
                   Functor.map, StateT.map, StateT.bind, bind]
        generalize hD : (mapStmtExprM insideOld d bI) sI = resD
        obtain ⟨⟨d', bD⟩, sD⟩ := resD
        have hPresD := ih (sizeOf d) hDSz sI bI d rfl
        have hSD : (((mapStmtExprM insideOld d).run bI).run sI).snd = sD := by
          show (mapStmtExprM insideOld d bI sI).snd = sD
          rw [hD]
        rw [hSD] at hPresD
        simp only []
        generalize hBd : (mapStmtExprM insideOld body bD) sD = resBd
        obtain ⟨⟨body', bBd⟩, sBd⟩ := resBd
        have hPresBd := ih (sizeOf body) hBSz sD bD body rfl
        have hSBd : (((mapStmtExprM insideOld body).run bD).run sD).snd = sBd := by
          show (mapStmtExprM insideOld body bD sD).snd = sBd
          rw [hBd]
        rw [hSBd] at hPresBd
        exact ((hPresBd.trans hPresD).trans hPresI).trans hPresC
    | StaticCall callee args =>
      have he : e = ⟨.StaticCall callee args, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
      rw [mapStmtExprM_insideOld_attach_mapM_eq]
      have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec := StmtExpr.StaticCall.sizeOf_spec callee args
      have hPres : ∀ x ∈ args, ∀ (s' : PushOldState) (b' : Bool),
          (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames := by
        intro x hx s' b'
        have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        exact ih (sizeOf x) hxSize s' b' x rfl
      have hList := listMapM_insideOld_preserves_inoutNames_of args hPres s b
      generalize hM : (args.mapM (mapStmtExprM insideOld) b s) = res
      obtain ⟨⟨ys, bY⟩, sY⟩ := res
      have hSnd : ((args.mapM (mapStmtExprM insideOld)).run b s).snd = sY := by
        show (args.mapM (mapStmtExprM insideOld) b s).snd = sY
        rw [hM]
      rw [hSnd] at hList
      exact hList
    | PrimitiveOp op args =>
      have he : e = ⟨.PrimitiveOp op args, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
      rw [mapStmtExprM_insideOld_attach_mapM_eq]
      have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec := StmtExpr.PrimitiveOp.sizeOf_spec op args
      have hPres : ∀ x ∈ args, ∀ (s' : PushOldState) (b' : Bool),
          (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames := by
        intro x hx s' b'
        have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        exact ih (sizeOf x) hxSize s' b' x rfl
      have hList := listMapM_insideOld_preserves_inoutNames_of args hPres s b
      generalize hM : (args.mapM (mapStmtExprM insideOld) b s) = res
      obtain ⟨⟨ys, bY⟩, sY⟩ := res
      have hSnd : ((args.mapM (mapStmtExprM insideOld)).run b s).snd = sY := by
        show (args.mapM (mapStmtExprM insideOld) b s).snd = sY
        rw [hM]
      rw [hSnd] at hList
      exact hList
    | InstanceCall t callee args =>
      have he : e = ⟨.InstanceCall t callee args, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM]
      have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec := StmtExpr.InstanceCall.sizeOf_spec t callee args
      have hTSz : sizeOf t < n := by omega
      have hPres : ∀ x ∈ args, ∀ (s' : PushOldState) (b' : Bool),
          (((mapStmtExprM insideOld x).run b').run s').snd.inoutNames = s'.inoutNames := by
        intro x hx s' b'
        have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        exact ih (sizeOf x) hxSize s' b' x rfl
      simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
      rw [mapStmtExprM_insideOld_attach_mapM_eq]
      generalize hT : (mapStmtExprM insideOld t b) s = resT
      obtain ⟨⟨t', bT⟩, sT⟩ := resT
      have hPresT := ih (sizeOf t) hTSz s b t rfl
      have hST : (((mapStmtExprM insideOld t).run b).run s).snd = sT := by
        show (mapStmtExprM insideOld t b s).snd = sT
        rw [hT]
      rw [hST] at hPresT
      simp only []
      generalize hA : (args.mapM (mapStmtExprM insideOld) bT) sT = resA
      obtain ⟨⟨args', bA⟩, sA⟩ := resA
      have hPresA : ((args.mapM (mapStmtExprM insideOld)).run bT sT).snd.inoutNames = sT.inoutNames :=
        listMapM_insideOld_preserves_inoutNames_of args hPres sT bT
      have hSA : (args.mapM (mapStmtExprM insideOld) bT sT).snd = sA := by rw [hA]
      have hSA' : ((args.mapM (mapStmtExprM insideOld)).run bT sT).snd = sA := hSA
      rw [hSA'] at hPresA
      exact hPresA.trans hPresT
    | Assign targets value =>
      have he : e = ⟨.Assign targets value, e.source⟩ := by cases e; simp_all
      rw [he, mapStmtExprM_assign_run_eq]
      have hValLt := AstNode.sizeOf_val_lt e
      rw [hVal] at hValLt
      have hSpec : sizeOf (StmtExpr.Assign targets value) = 1 + sizeOf targets + sizeOf value :=
        StmtExpr.Assign.sizeOf_spec targets value
      have hVSz : sizeOf value < n := by omega
      simp only [Prod.fst, Prod.snd]
      have ihV := ih (sizeOf value) hVSz (mapAssignTargets targets b s).snd
                     (mapAssignTargets targets b s).fst.snd value rfl
      -- Need: (mapAssignTargets targets b s).snd.inoutNames = s.inoutNames.
      -- Use the parameterized preservation lemma.
      have hPresT : (mapAssignTargets targets b s).snd.inoutNames = s.inoutNames := by
        apply mapAssignTargets_preserves_inoutNames_ofIH
        intro tgt fn vs hMem s' b'
        have hxLt : sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable) < sizeOf targets :=
          List.sizeOf_lt_of_mem hMem
        have hTgtLt : sizeOf tgt < sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable) := by
          have h1 := AstNode.sizeOf_val_lt (⟨.Field tgt fn, vs⟩ : AstNode Variable)
          have h2 := Variable.Field.sizeOf_spec tgt fn
          show sizeOf tgt < sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable)
          simp only at h1
          omega
        have hTgtSz : sizeOf tgt < n := by omega
        exact ih (sizeOf tgt) hTgtSz s' b' tgt rfl
      exact ihV.trans hPresT

/-- Generic helper: if `((mapStmtExprM insideOld e).run b).run s).fst.fst` has
    canonical `subOlds`, and another value `e' = (...).fst.fst` (i.e. equals
    that thing under StateT.run), then `e'` is canonical. -/
private theorem allSubOldsCanonical_via_eq
    (s : PushOldState) (b : Bool) (e : StmtExprMd) (e' : StmtExprMd)
    (hEq : e' = (((mapStmtExprM insideOld e).run b).run s).fst.fst)
    (hCan : AllSubOldsCanonical s.inoutNames
              (((mapStmtExprM insideOld e).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames e' := by
  rw [hEq]; exact hCan

/-- Reduction for `.Quantifier mode param none body`: rebuild with body rewritten. -/
private theorem mapStmtExprM_insideOld_quantifier_no_trigger_run
    (s : PushOldState) (b : Bool) (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Quantifier mode param none body, src⟩).run b).run s).fst.fst =
    ⟨.Quantifier mode param none (((mapStmtExprM insideOld body).run b).run s).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map,
             insideOld, liftM, MonadLift.monadLift, monadLift]
  generalize hM : (mapStmtExprM insideOld body b) s = res
  obtain ⟨⟨body', b'⟩, s'⟩ := res
  rfl

/-- subOlds of `.Quantifier mode param none body` is `body.subOlds`. -/
theorem subOlds_quantifier_no_trigger (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Quantifier mode param none body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]
  simp

private theorem mapStmtExprM_insideOld_canonical_quantifier_no_trigger
    (s : PushOldState) (b : Bool) (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld body).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Quantifier mode param none body, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_quantifier_no_trigger_run]
  intro subOld hSub
  rw [subOlds_quantifier_no_trigger] at hSub
  exact ih subOld hSub

/-- Reduction for `.IfThenElse cond th none` — 2-child reduction (no else). -/
private theorem mapStmtExprM_insideOld_ifThenElse_none_run
    (s : PushOldState) (b : Bool) (cond th : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.IfThenElse cond th none, src⟩).run b).run s).fst.fst =
    ⟨.IfThenElse
      (((mapStmtExprM insideOld cond).run b).run s).fst.fst
      (((mapStmtExprM insideOld th).run
          (((mapStmtExprM insideOld cond).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld cond).run b).run s).snd).fst.fst
      none, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map,
             insideOld, liftM, MonadLift.monadLift, monadLift]
  generalize hC : (mapStmtExprM insideOld cond b) s = resC
  obtain ⟨⟨cond', bC⟩, sC⟩ := resC
  simp only []
  generalize hT : (mapStmtExprM insideOld th bC) sC = resT
  obtain ⟨⟨th', bT⟩, sT⟩ := resT
  rfl

/-- subOlds of `.IfThenElse cond th none` is `cond.subOlds ++ th.subOlds`. -/
theorem subOlds_ifThenElse_none (cond th : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.IfThenElse cond th none, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++ StmtExprMd.subOlds th := by
  rw [StmtExprMd.subOlds]
  simp

private theorem mapStmtExprM_insideOld_canonical_ifThenElse_none
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (cond th : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.IfThenElse cond th none, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.IfThenElse cond th none, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_ifThenElse_none_run]
  intro subOld hSub
  rw [subOlds_ifThenElse_none] at hSub
  rw [List.mem_append] at hSub
  have hCSz : sizeOf cond < n := by
    rw [← hSize]
    have : sizeOf (⟨.IfThenElse cond th none, src⟩ : StmtExprMd) =
           1 + (1 + sizeOf cond + sizeOf th + sizeOf (none : Option StmtExprMd)) + sizeOf src := rfl
    omega
  have hTSz : sizeOf th < n := by
    rw [← hSize]
    have : sizeOf (⟨.IfThenElse cond th none, src⟩ : StmtExprMd) =
           1 + (1 + sizeOf cond + sizeOf th + sizeOf (none : Option StmtExprMd)) + sizeOf src := rfl
    omega
  cases hSub with
  | inl h => exact ih (sizeOf cond) hCSz s b cond rfl subOld h
  | inr h =>
    have hPres := mapStmtExprM_insideOld_preserves_inoutNames s b cond
    let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
    let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
    have hCan := ih (sizeOf th) hTSz sC bC th rfl
    have hSame : sC.inoutNames = s.inoutNames := hPres
    rw [hSame] at hCan
    exact hCan subOld h

-- ReferenceEquals two-child case deferred — type-mismatch issue with
-- `generalize` on `mapStmtExprM insideOld lhs b s` after `rw [mapStmtExprM]`.


/-- Reduction for `.Assert c`: rebuilds with condition rewritten. -/
private theorem mapStmtExprM_insideOld_assert_run
    (s : PushOldState) (b : Bool) (c : Condition) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Assert c, src⟩).run b).run s).fst.fst =
    ⟨.Assert { c with condition := (((mapStmtExprM insideOld c.condition).run b).run s).fst.fst }, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld c.condition b) s = res
  obtain ⟨⟨cond', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             liftM, MonadLift.monadLift, monadLift]

private theorem mapStmtExprM_insideOld_canonical_assert
    (s : PushOldState) (b : Bool) (c : Condition) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld c.condition).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Assert c, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_assert_run]
  intro subOld hSub
  rw [subOlds_assert] at hSub
  exact ih subOld hSub

-- (Canonical for `.ReferenceEquals` deferred — two-child state threading.)

/-- Reduction: `mapStmtExprM insideOld ⟨.Old inner, src⟩` produces the
    same fst-result as `mapStmtExprM insideOld inner`. -/
private theorem mapStmtExprM_insideOld_old_run
    (s : PushOldState) (b : Bool) (inner : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Old inner, src⟩).run b).run s).fst.fst =
    (((mapStmtExprM insideOld inner).run b).run s).fst.fst := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld inner b) s = res
  obtain ⟨⟨inner', b'⟩, s'⟩ := res
  unfold insideOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, warn,
             modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
             liftM, MonadLift.monadLift, monadLift]
  rfl

private theorem mapStmtExprM_insideOld_canonical_old
    (s : PushOldState) (b : Bool) (inner : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld inner).run b).run s).fst.fst) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Old inner, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_old_run]
  exact ih

private theorem mapStmtExprM_insideOld_canonical_hole
    (s : PushOldState) (b : Bool) (det : Bool) (ty : Option (AstNode HighType)) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Hole det ty, src⟩).run b).run s).fst.fst := by
  have hRes : (((mapStmtExprM insideOld ⟨.Hole det ty, src⟩).run b).run s).fst.fst =
              ⟨.Hole det ty, src⟩ := by
    simp [mapStmtExprM, insideOld, StateT.run, StateT.bind, bind, StateT.pure, pure,
          getThe, MonadStateOf.get, StateT.lift, StateT.get, liftM, MonadLift.monadLift, monadLift]
  rw [hRes]
  have : StmtExprMd.subOlds (⟨.Hole det ty, src⟩ : StmtExprMd) = [] := by
    rw [StmtExprMd.subOlds]
  exact allSubOldsCanonical_of_subOlds_nil this

/-- Helper: `AllSubOldsCanonical` is preserved when subterms are individually
    canonical and combined via `++`. -/
theorem allSubOldsCanonical_append
    {inoutNames : List String} {l1 l2 : List StmtExprMd}
    (h1 : ∀ x ∈ l1, IsCanonicalOld inoutNames x)
    (h2 : ∀ x ∈ l2, IsCanonicalOld inoutNames x) :
    ∀ x ∈ (l1 ++ l2), IsCanonicalOld inoutNames x := by
  intro x hx
  rw [List.mem_append] at hx
  cases hx with
  | inl h => exact h1 x h
  | inr h => exact h2 x h


/-! ### Compound cases for subgoal 3

The remaining 12 compound cases (Old, IfThenElse, Block, While, Return,
Assign, PureFieldUpdate, Var-Field, StaticCall, PrimitiveOp,
ReferenceEquals, AsType, IsType, InstanceCall, Quantifier, Assigned,
Fresh, Assert, Assume, ProveBy, ContractOf) all follow the same
template:

1. Show `mapStmtExprM insideOld` rebuilds the constructor with
   recursively-rewritten children, then `insideOld` falls through
   (no-op for non-Var/non-Old).
2. The result's `subOlds` is the (possibly nested) concatenation of
   the children's `subOlds`.
3. Each child's `subOlds` is canonical by the strong induction
   hypothesis (children have strictly smaller `sizeOf`).

For `Old inner`: `insideOld` drops the wrapper, returning the
recursively-rewritten `inner`. By IH on `inner` (which is smaller
than `e = ⟨.Old inner, src⟩`), the result is canonical.

The proof of each compound case is mechanical but voluminous,
requiring monadic-bind reductions and concatenation reasoning.
-/

/-! #### List-induction helpers for compound cases -/

/-- `inoutNames` is preserved through `xs.mapM (mapStmtExprM insideOld)`. -/
private theorem mapStmtExprM_insideOld_listMapM_preserves_inoutNames
    (xs : List StmtExprMd) (s : PushOldState) (b : Bool) :
    ((xs.mapM (mapStmtExprM insideOld)).run b s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s b with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapStmtExprM insideOld x b) s = resX
    obtain ⟨⟨x', bX⟩, sX⟩ := resX
    have hPresX := mapStmtExprM_insideOld_preserves_inoutNames s b x
    have hSX : (((mapStmtExprM insideOld x).run b).run s).snd = sX := by
      show (mapStmtExprM insideOld x b s).snd = sX
      rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM (mapStmtExprM insideOld) bX sX = resRest
    obtain ⟨⟨ys', bRest⟩, sRest⟩ := resRest
    have hRestPres := ih sX bX
    have hSR : (xs.mapM (mapStmtExprM insideOld) bX sX).snd = sRest := by rw [hRest]
    have hSR' : ((xs.mapM (mapStmtExprM insideOld)).run bX sX).snd = sRest := hSR
    rw [hSR'] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

/-- Each output of `xs.mapM (mapStmtExprM insideOld)` is canonical w.r.t. `target`,
    given that each input element is canonical for any starting state with
    `inoutNames = target`. -/
private theorem mapStmtExprM_insideOld_listMapM_canonical
    (xs : List StmtExprMd) (s : PushOldState) (b : Bool)
    (target : List String)
    (hSame : s.inoutNames = target)
    (hAll : ∀ x ∈ xs, ∀ (s' : PushOldState) (b' : Bool),
              s'.inoutNames = target →
              AllSubOldsCanonical target
                (((mapStmtExprM insideOld x).run b').run s').fst.fst) :
    ∀ y ∈ ((xs.mapM (mapStmtExprM insideOld)).run b s).fst.fst,
      AllSubOldsCanonical target y := by
  induction xs generalizing s b with
  | nil =>
    intro y hy
    simp [List.mapM_nil, StateT.run, StateT.pure, pure] at hy
  | cons x xs ih =>
    intro y hy
    rw [List.mapM_cons] at hy
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hy
    generalize hM : (mapStmtExprM insideOld x b) s = resX at hy
    obtain ⟨⟨x', bX⟩, sX⟩ := resX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hy
    generalize hRest : xs.mapM (mapStmtExprM insideOld) bX sX = resRest at hy
    obtain ⟨⟨ys', bRest⟩, sRest⟩ := resRest
    simp at hy
    have hPresX := mapStmtExprM_insideOld_preserves_inoutNames s b x
    have hSXsnd : (((mapStmtExprM insideOld x).run b).run s).snd = sX := by
      show (mapStmtExprM insideOld x b s).snd = sX
      rw [hM]
    rw [hSXsnd] at hPresX
    have hSXTarget : sX.inoutNames = target := hPresX.trans hSame
    cases hy with
    | inl h =>
      have hCanX := hAll x List.mem_cons_self s b hSame
      have hSXfst : (((mapStmtExprM insideOld x).run b).run s).fst.fst = x' := by
        show (mapStmtExprM insideOld x b s).fst.fst = x'
        rw [hM]
      rw [hSXfst] at hCanX
      rw [h]
      exact hCanX
    | inr h =>
      have hAll' : ∀ y ∈ xs, ∀ (s' : PushOldState) (b' : Bool),
            s'.inoutNames = target →
            AllSubOldsCanonical target
              (((mapStmtExprM insideOld y).run b').run s').fst.fst :=
        fun y hy s' b' hh => hAll y (List.mem_cons_of_mem _ hy) s' b' hh
      have ih' := ih sX bX hSXTarget hAll'
      have hRestEq : ((xs.mapM (mapStmtExprM insideOld)).run bX sX).fst.fst = ys' := by
        show (xs.mapM (mapStmtExprM insideOld) bX sX).fst.fst = ys'
        rw [hRest]
      apply ih' y
      rw [hRestEq]
      exact h

/-! #### Compound case reduction lemmas -/

/-- Reduction for `.IfThenElse cond th (some elE)`. -/
private theorem mapStmtExprM_insideOld_ifThenElse_some_run
    (s : PushOldState) (b : Bool) (cond th elE : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.IfThenElse cond th (some elE), src⟩).run b).run s).fst.fst =
    ⟨.IfThenElse
      (((mapStmtExprM insideOld cond).run b).run s).fst.fst
      (((mapStmtExprM insideOld th).run
          (((mapStmtExprM insideOld cond).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld cond).run b).run s).snd).fst.fst
      (some
        (((mapStmtExprM insideOld elE).run
            (((mapStmtExprM insideOld th).run
              (((mapStmtExprM insideOld cond).run b).run s).fst.snd).run
              (((mapStmtExprM insideOld cond).run b).run s).snd).fst.snd).run
          (((mapStmtExprM insideOld th).run
              (((mapStmtExprM insideOld cond).run b).run s).fst.snd).run
              (((mapStmtExprM insideOld cond).run b).run s).snd).snd).fst.fst), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map, insideOld]
  generalize hC : (mapStmtExprM insideOld cond b) s = resC
  obtain ⟨⟨cond', bC⟩, sC⟩ := resC
  simp only []
  generalize hT : (mapStmtExprM insideOld th bC) sC = resT
  obtain ⟨⟨th', bT⟩, sT⟩ := resT
  simp only []
  generalize hE : (mapStmtExprM insideOld elE bT) sT = resE
  obtain ⟨⟨elE', bE⟩, sE⟩ := resE
  rfl

/-- subOlds of `.IfThenElse cond th (some elE)`. -/
theorem subOlds_ifThenElse_some (cond th elE : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++ StmtExprMd.subOlds th ++ StmtExprMd.subOlds elE := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_ifThenElse_some
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (cond th elE : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.IfThenElse cond th (some elE), src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_ifThenElse_some_run]
  intro subOld hSub
  rw [subOlds_ifThenElse_some] at hSub
  rw [List.mem_append] at hSub
  have hCSz : sizeOf cond < n := by
    rw [← hSize]
    have hVal_size : sizeOf (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd).val
                     = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := rfl
    have := AstNode.sizeOf_val_lt (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd)
    have hSE : sizeOf (some elE) = 1 + sizeOf elE := rfl
    omega
  have hTSz : sizeOf th < n := by
    rw [← hSize]
    have hVal_size : sizeOf (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd).val
                     = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := rfl
    have := AstNode.sizeOf_val_lt (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd)
    have hSE : sizeOf (some elE) = 1 + sizeOf elE := rfl
    omega
  have hESz : sizeOf elE < n := by
    rw [← hSize]
    have hVal_size : sizeOf (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd).val
                     = 1 + sizeOf cond + sizeOf th + sizeOf (some elE) := rfl
    have := AstNode.sizeOf_val_lt (⟨.IfThenElse cond th (some elE), src⟩ : StmtExprMd)
    have hSE : sizeOf (some elE) = 1 + sizeOf elE := rfl
    omega
  cases hSub with
  | inl h =>
    rw [List.mem_append] at h
    cases h with
    | inl h => exact ih (sizeOf cond) hCSz s b cond rfl subOld h
    | inr h =>
      have hPres := mapStmtExprM_insideOld_preserves_inoutNames s b cond
      let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
      let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
      have hCan := ih (sizeOf th) hTSz sC bC th rfl
      have hSame : sC.inoutNames = s.inoutNames := hPres
      rw [hSame] at hCan
      exact hCan subOld h
  | inr h =>
    have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
    let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
    let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
    have hPresT := mapStmtExprM_insideOld_preserves_inoutNames sC bC th
    let sT := (((mapStmtExprM insideOld th).run bC).run sC).snd
    let bT := (((mapStmtExprM insideOld th).run bC).run sC).fst.snd
    have hCan := ih (sizeOf elE) hESz sT bT elE rfl
    have hSame : sT.inoutNames = s.inoutNames := hPresT.trans hPresC
    rw [hSame] at hCan
    exact hCan subOld h

/-- Reduction for `.Quantifier mode param (some tr) body`. -/
private theorem mapStmtExprM_insideOld_quantifier_some_run
    (s : PushOldState) (b : Bool) (mode : QuantifierMode) (param : Parameter)
    (tr body : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Quantifier mode param (some tr) body, src⟩).run b).run s).fst.fst =
    ⟨.Quantifier mode param
      (some (((mapStmtExprM insideOld tr).run b).run s).fst.fst)
      (((mapStmtExprM insideOld body).run
          (((mapStmtExprM insideOld tr).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld tr).run b).run s).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map, insideOld]
  generalize hT : (mapStmtExprM insideOld tr b) s = resT
  obtain ⟨⟨tr', bT⟩, sT⟩ := resT
  simp only []
  generalize hB : (mapStmtExprM insideOld body bT) sT = resB
  obtain ⟨⟨body', bB⟩, sB⟩ := resB
  rfl

/-- subOlds of `.Quantifier mode param (some tr) body`. -/
theorem subOlds_quantifier_some (mode : QuantifierMode) (param : Parameter)
    (tr body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds tr ++ StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_quantifier_some
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (mode : QuantifierMode) (param : Parameter)
    (tr body : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Quantifier mode param (some tr) body, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_quantifier_some_run]
  intro subOld hSub
  rw [subOlds_quantifier_some] at hSub
  rw [List.mem_append] at hSub
  have hTSz : sizeOf tr < n := by
    rw [← hSize]
    have hVal_size : sizeOf (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd).val
                     = 1 + sizeOf mode + sizeOf param + sizeOf (some tr) + sizeOf body := rfl
    have := AstNode.sizeOf_val_lt (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd)
    have hSTr : sizeOf (some tr) = 1 + sizeOf tr := rfl
    omega
  have hBSz : sizeOf body < n := by
    rw [← hSize]
    have hVal_size : sizeOf (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd).val
                     = 1 + sizeOf mode + sizeOf param + sizeOf (some tr) + sizeOf body := rfl
    have := AstNode.sizeOf_val_lt (⟨.Quantifier mode param (some tr) body, src⟩ : StmtExprMd)
    have hSTr : sizeOf (some tr) = 1 + sizeOf tr := rfl
    omega
  cases hSub with
  | inl h => exact ih (sizeOf tr) hTSz s b tr rfl subOld h
  | inr h =>
    have hPresT := mapStmtExprM_insideOld_preserves_inoutNames s b tr
    let sT := (((mapStmtExprM insideOld tr).run b).run s).snd
    let bT := (((mapStmtExprM insideOld tr).run b).run s).fst.snd
    have hCan := ih (sizeOf body) hBSz sT bT body rfl
    have hSame : sT.inoutNames = s.inoutNames := hPresT
    rw [hSame] at hCan
    exact hCan subOld h

/-- Reduction for `.Block stmts label`. -/
private theorem mapStmtExprM_insideOld_block_run
    (s : PushOldState) (b : Bool) (stmts : List StmtExprMd) (label : Option String) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.Block stmts label, src⟩).run b).run s).fst.fst =
    ⟨.Block ((stmts.mapM (mapStmtExprM insideOld) b s).fst.fst) label, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hM : (stmts.mapM (mapStmtExprM insideOld) b) s = res
  obtain ⟨⟨ys', bRest⟩, sRest⟩ := res
  rfl

/-- subOlds of `.Block stmts label`. -/
theorem subOlds_block (stmts : List StmtExprMd) (label : Option String) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Block stmts label, src⟩ : StmtExprMd) =
    (stmts.attach.map fun ⟨s, _⟩ => StmtExprMd.subOlds s).flatten := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_block
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (stmts : List StmtExprMd)
    (label : Option String) (src : Option FileRange)
    (hSize : sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Block stmts label, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_block_run]
  intro subOld hSub
  rw [subOlds_block] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, _hy⟩, _, hYsEq⟩, hSubOlds⟩ := hSub
  have hYAttach : y ∈ (stmts.mapM (mapStmtExprM insideOld) b s).fst.fst := _hy
  have hCan := mapStmtExprM_insideOld_listMapM_canonical stmts s b s.inoutNames rfl
    (fun x hx s' b' hh => by
      have hxSize : sizeOf x < n := by
        rw [← hSize]
        have hLt : sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd).val
                   < sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd) :=
          AstNode.sizeOf_val_lt _
        have hValEq : (⟨.Block stmts label, src⟩ : StmtExprMd).val = .Block stmts label := rfl
        rw [hValEq] at hLt
        have hxLt : sizeOf x < sizeOf (StmtExpr.Block stmts label) := by term_by_mem
        omega
      have ih' := ih (sizeOf x) hxSize s' b' x rfl
      rw [hh] at ih'
      exact ih')
    y hYAttach
  rw [← hYsEq] at hSubOlds
  exact hCan subOld hSubOlds

/-- Reduction for `.While cond invs dec body`. The decreases is none case. -/
private theorem mapStmtExprM_insideOld_while_none_run
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (invs : List StmtExprMd)
    (body : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.While cond invs none body, src⟩).run b).run s).fst.fst =
    ⟨.While
      (((mapStmtExprM insideOld cond).run b).run s).fst.fst
      ((invs.mapM (mapStmtExprM insideOld)
          (((mapStmtExprM insideOld cond).run b).run s).fst.snd
          (((mapStmtExprM insideOld cond).run b).run s).snd).fst.fst)
      none
      (((mapStmtExprM insideOld body).run
          (invs.mapM (mapStmtExprM insideOld)
            (((mapStmtExprM insideOld cond).run b).run s).fst.snd
            (((mapStmtExprM insideOld cond).run b).run s).snd).fst.snd).run
        (invs.mapM (mapStmtExprM insideOld)
          (((mapStmtExprM insideOld cond).run b).run s).fst.snd
          (((mapStmtExprM insideOld cond).run b).run s).snd).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hC : (mapStmtExprM insideOld cond b) s = resC
  obtain ⟨⟨cond', bC⟩, sC⟩ := resC
  simp only []
  generalize hI : (invs.mapM (mapStmtExprM insideOld) bC) sC = resI
  obtain ⟨⟨invs', bI⟩, sI⟩ := resI
  simp only []
  generalize hBd : (mapStmtExprM insideOld body bI) sI = resBd
  obtain ⟨⟨body', bBd⟩, sBd⟩ := resBd
  rfl

/-- Reduction for `.While cond invs (some dec) body`. -/
private theorem mapStmtExprM_insideOld_while_some_run
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (invs : List StmtExprMd)
    (dec body : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.While cond invs (some dec) body, src⟩).run b).run s).fst.fst =
    ⟨.While
      (((mapStmtExprM insideOld cond).run b).run s).fst.fst
      ((invs.mapM (mapStmtExprM insideOld)
          (((mapStmtExprM insideOld cond).run b).run s).fst.snd
          (((mapStmtExprM insideOld cond).run b).run s).snd).fst.fst)
      (some
        (((mapStmtExprM insideOld dec).run
            (invs.mapM (mapStmtExprM insideOld)
              (((mapStmtExprM insideOld cond).run b).run s).fst.snd
              (((mapStmtExprM insideOld cond).run b).run s).snd).fst.snd).run
          (invs.mapM (mapStmtExprM insideOld)
            (((mapStmtExprM insideOld cond).run b).run s).fst.snd
            (((mapStmtExprM insideOld cond).run b).run s).snd).snd).fst.fst)
      (((mapStmtExprM insideOld body).run
          (((mapStmtExprM insideOld dec).run
              (invs.mapM (mapStmtExprM insideOld)
                (((mapStmtExprM insideOld cond).run b).run s).fst.snd
                (((mapStmtExprM insideOld cond).run b).run s).snd).fst.snd).run
            (invs.mapM (mapStmtExprM insideOld)
              (((mapStmtExprM insideOld cond).run b).run s).fst.snd
              (((mapStmtExprM insideOld cond).run b).run s).snd).snd).fst.snd).run
        (((mapStmtExprM insideOld dec).run
            (invs.mapM (mapStmtExprM insideOld)
              (((mapStmtExprM insideOld cond).run b).run s).fst.snd
              (((mapStmtExprM insideOld cond).run b).run s).snd).fst.snd).run
          (invs.mapM (mapStmtExprM insideOld)
            (((mapStmtExprM insideOld cond).run b).run s).fst.snd
            (((mapStmtExprM insideOld cond).run b).run s).snd).snd).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hC : (mapStmtExprM insideOld cond b) s = resC
  obtain ⟨⟨cond', bC⟩, sC⟩ := resC
  simp only []
  generalize hI : (invs.mapM (mapStmtExprM insideOld) bC) sC = resI
  obtain ⟨⟨invs', bI⟩, sI⟩ := resI
  simp only []
  generalize hD : (mapStmtExprM insideOld dec bI) sI = resD
  obtain ⟨⟨dec', bD⟩, sD⟩ := resD
  simp only []
  generalize hBd : (mapStmtExprM insideOld body bD) sD = resBd
  obtain ⟨⟨body', bBd⟩, sBd⟩ := resBd
  rfl

/-- subOlds of `.While cond invs none body`. -/
theorem subOlds_while_none (cond : StmtExprMd) (invs : List StmtExprMd) (body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.While cond invs none body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++
    (invs.attach.map fun ⟨i, _⟩ => StmtExprMd.subOlds i).flatten ++
    [] ++
    StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]

/-- subOlds of `.While cond invs (some d) body`. -/
theorem subOlds_while_some (cond : StmtExprMd) (invs : List StmtExprMd) (d body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++
    (invs.attach.map fun ⟨i, _⟩ => StmtExprMd.subOlds i).flatten ++
    StmtExprMd.subOlds d ++
    StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_while_none
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (invs : List StmtExprMd)
    (body : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.While cond invs none body, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_while_none_run]
  intro subOld hSub
  rw [subOlds_while_none] at hSub
  -- Bounds for cond, body, invs members via term_by_mem
  have hCSz : sizeOf cond < n := by
    rw [← hSize]
    have hLt : sizeOf cond < sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) := by
      have := AstNode.sizeOf_val_lt (⟨.While cond invs none body, src⟩ : StmtExprMd)
      have hValEq : (⟨.While cond invs none body, src⟩ : StmtExprMd).val = .While cond invs none body := rfl
      rw [hValEq] at this
      have : sizeOf cond < sizeOf (StmtExpr.While cond invs none body) := by term_by_mem
      omega
    omega
  have hBSz : sizeOf body < n := by
    rw [← hSize]
    have hLt : sizeOf body < sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) := by
      have := AstNode.sizeOf_val_lt (⟨.While cond invs none body, src⟩ : StmtExprMd)
      have hValEq : (⟨.While cond invs none body, src⟩ : StmtExprMd).val = .While cond invs none body := rfl
      rw [hValEq] at this
      have : sizeOf body < sizeOf (StmtExpr.While cond invs none body) := by term_by_mem
      omega
    omega
  rw [List.mem_append, List.mem_append, List.mem_append] at hSub
  cases hSub with
  | inl hLeft =>
    cases hLeft with
    | inl hLL =>
      cases hLL with
      | inl hCond =>
        exact ih (sizeOf cond) hCSz s b cond rfl subOld hCond
      | inr hInvs =>
        simp only [List.mem_flatten, List.mem_map] at hInvs
        obtain ⟨ys, ⟨⟨y, hyMem⟩, _, hYsEq⟩, hSubInY⟩ := hInvs
        have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
        let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
        let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
        have hCanInvs : ∀ y' ∈ ((invs.mapM (mapStmtExprM insideOld)).run bC sC).fst.fst,
              AllSubOldsCanonical s.inoutNames y' := by
          apply mapStmtExprM_insideOld_listMapM_canonical invs sC bC s.inoutNames hPresC
          intro x hx s' b' hh
          have hxSize : sizeOf x < n := by
            rw [← hSize]
            have hValEq : (⟨.While cond invs none body, src⟩ : StmtExprMd).val = .While cond invs none body := rfl
            have hLt : sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd).val
                       < sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) :=
              AstNode.sizeOf_val_lt _
            rw [hValEq] at hLt
            have hxLt : sizeOf x < sizeOf (StmtExpr.While cond invs none body) := by term_by_mem
            omega
          have ih' := ih (sizeOf x) hxSize s' b' x rfl
          rw [hh] at ih'
          exact ih'
        rw [← hYsEq] at hSubInY
        apply hCanInvs y _ subOld hSubInY
        show y ∈ (invs.mapM (mapStmtExprM insideOld) bC sC).fst.fst
        exact hyMem
    | inr hEmpty =>
      cases hEmpty
  | inr hBody =>
    have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
    let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
    let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
    have hPresI := mapStmtExprM_insideOld_listMapM_preserves_inoutNames invs sC bC
    let sI := (invs.mapM (mapStmtExprM insideOld) bC sC).snd
    let bI := (invs.mapM (mapStmtExprM insideOld) bC sC).fst.snd
    have hCan := ih (sizeOf body) hBSz sI bI body rfl
    have hSame : sI.inoutNames = s.inoutNames :=
      hPresI.trans hPresC
    rw [hSame] at hCan
    exact hCan subOld hBody

private theorem mapStmtExprM_insideOld_canonical_while_some
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (cond : StmtExprMd) (invs : List StmtExprMd)
    (d body : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.While cond invs (some d) body, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_while_some_run]
  intro subOld hSub
  rw [subOlds_while_some] at hSub
  have hCSz : sizeOf cond < n := by
    rw [← hSize]
    have hValEq : (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val = .While cond invs (some d) body := rfl
    have h1 : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val
              < sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf cond < sizeOf (StmtExpr.While cond invs (some d) body) := by term_by_mem
    omega
  have hDSz : sizeOf d < n := by
    rw [← hSize]
    have hValEq : (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val = .While cond invs (some d) body := rfl
    have h1 : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val
              < sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf d < sizeOf (StmtExpr.While cond invs (some d) body) := by term_by_mem
    omega
  have hBSz : sizeOf body < n := by
    rw [← hSize]
    have hValEq : (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val = .While cond invs (some d) body := rfl
    have h1 : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val
              < sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf body < sizeOf (StmtExpr.While cond invs (some d) body) := by term_by_mem
    omega
  rw [List.mem_append, List.mem_append, List.mem_append] at hSub
  cases hSub with
  | inl hLeft =>
    cases hLeft with
    | inl hLL =>
      cases hLL with
      | inl hCond =>
        exact ih (sizeOf cond) hCSz s b cond rfl subOld hCond
      | inr hInvs =>
        simp only [List.mem_flatten, List.mem_map] at hInvs
        obtain ⟨ys, ⟨⟨y, hyMem⟩, _, hYsEq⟩, hSubInY⟩ := hInvs
        have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
        let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
        let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
        have hCanInvs : ∀ y' ∈ ((invs.mapM (mapStmtExprM insideOld)).run bC sC).fst.fst,
              AllSubOldsCanonical s.inoutNames y' := by
          apply mapStmtExprM_insideOld_listMapM_canonical invs sC bC s.inoutNames hPresC
          intro x hx s' b' hh
          have hxSize : sizeOf x < n := by
            rw [← hSize]
            have hValEq : (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val = .While cond invs (some d) body := rfl
            have hLt : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val
                       < sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) :=
              AstNode.sizeOf_val_lt _
            rw [hValEq] at hLt
            have hxLt : sizeOf x < sizeOf (StmtExpr.While cond invs (some d) body) := by term_by_mem
            omega
          have ih' := ih (sizeOf x) hxSize s' b' x rfl
          rw [hh] at ih'
          exact ih'
        rw [← hYsEq] at hSubInY
        apply hCanInvs y _ subOld hSubInY
        show y ∈ (invs.mapM (mapStmtExprM insideOld) bC sC).fst.fst
        exact hyMem
    | inr hDec =>
      have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
      let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
      let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
      have hPresI := mapStmtExprM_insideOld_listMapM_preserves_inoutNames invs sC bC
      let sI := (invs.mapM (mapStmtExprM insideOld) bC sC).snd
      let bI := (invs.mapM (mapStmtExprM insideOld) bC sC).fst.snd
      have hCan := ih (sizeOf d) hDSz sI bI d rfl
      have hSame : sI.inoutNames = s.inoutNames := hPresI.trans hPresC
      rw [hSame] at hCan
      exact hCan subOld hDec
  | inr hBody =>
    have hPresC := mapStmtExprM_insideOld_preserves_inoutNames s b cond
    let sC := (((mapStmtExprM insideOld cond).run b).run s).snd
    let bC := (((mapStmtExprM insideOld cond).run b).run s).fst.snd
    have hPresI := mapStmtExprM_insideOld_listMapM_preserves_inoutNames invs sC bC
    let sI := (invs.mapM (mapStmtExprM insideOld) bC sC).snd
    let bI := (invs.mapM (mapStmtExprM insideOld) bC sC).fst.snd
    have hPresD := mapStmtExprM_insideOld_preserves_inoutNames sI bI d
    let sD := (((mapStmtExprM insideOld d).run bI).run sI).snd
    let bD := (((mapStmtExprM insideOld d).run bI).run sI).fst.snd
    have hCan := ih (sizeOf body) hBSz sD bD body rfl
    have hSame : sD.inoutNames = s.inoutNames := (hPresD.trans hPresI).trans hPresC
    rw [hSame] at hCan
    exact hCan subOld hBody

/-- Reduction for `.StaticCall callee args`. -/
private theorem mapStmtExprM_insideOld_staticCall_run
    (s : PushOldState) (b : Bool) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.StaticCall callee args, src⟩).run b).run s).fst.fst =
    ⟨.StaticCall callee ((args.mapM (mapStmtExprM insideOld) b s).fst.fst), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hM : (args.mapM (mapStmtExprM insideOld) b) s = res
  obtain ⟨⟨ys', bRest⟩, sRest⟩ := res
  rfl

/-- subOlds of `.StaticCall callee args`. -/
theorem subOlds_staticCall (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.StaticCall callee args, src⟩ : StmtExprMd) =
    (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_staticCall
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.StaticCall callee args, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_staticCall_run]
  intro subOld hSub
  rw [subOlds_staticCall] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, _hy⟩, _, hYsEq⟩, hSubOlds⟩ := hSub
  have hYAttach : y ∈ (args.mapM (mapStmtExprM insideOld) b s).fst.fst := _hy
  have hCan := mapStmtExprM_insideOld_listMapM_canonical args s b s.inoutNames rfl
    (fun x hx s' b' hh => by
      have hxSize : sizeOf x < n := by
        rw [← hSize]
        have hLt : sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd).val
                   < sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd) :=
          AstNode.sizeOf_val_lt _
        have hValEq : (⟨.StaticCall callee args, src⟩ : StmtExprMd).val = .StaticCall callee args := rfl
        rw [hValEq] at hLt
        have hxLt : sizeOf x < sizeOf (StmtExpr.StaticCall callee args) := by term_by_mem
        omega
      have ih' := ih (sizeOf x) hxSize s' b' x rfl
      rw [hh] at ih'
      exact ih')
    y hYAttach
  rw [← hYsEq] at hSubOlds
  exact hCan subOld hSubOlds

/-- Reduction for `.PrimitiveOp op args`. -/
private theorem mapStmtExprM_insideOld_primitiveOp_run
    (s : PushOldState) (b : Bool) (op : Operation) (args : List StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.PrimitiveOp op args, src⟩).run b).run s).fst.fst =
    ⟨.PrimitiveOp op ((args.mapM (mapStmtExprM insideOld) b s).fst.fst), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hM : (args.mapM (mapStmtExprM insideOld) b) s = res
  obtain ⟨⟨ys', bRest⟩, sRest⟩ := res
  rfl

/-- subOlds of `.PrimitiveOp op args`. -/
theorem subOlds_primitiveOp (op : Operation) (args : List StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.PrimitiveOp op args, src⟩ : StmtExprMd) =
    (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_primitiveOp
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (op : Operation) (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.PrimitiveOp op args, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_primitiveOp_run]
  intro subOld hSub
  rw [subOlds_primitiveOp] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, _hy⟩, _, hYsEq⟩, hSubOlds⟩ := hSub
  have hYAttach : y ∈ (args.mapM (mapStmtExprM insideOld) b s).fst.fst := _hy
  have hCan := mapStmtExprM_insideOld_listMapM_canonical args s b s.inoutNames rfl
    (fun x hx s' b' hh => by
      have hxSize : sizeOf x < n := by
        rw [← hSize]
        have hLt : sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd).val
                   < sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd) :=
          AstNode.sizeOf_val_lt _
        have hValEq : (⟨.PrimitiveOp op args, src⟩ : StmtExprMd).val = .PrimitiveOp op args := rfl
        rw [hValEq] at hLt
        have hxLt : sizeOf x < sizeOf (StmtExpr.PrimitiveOp op args) := by term_by_mem
        omega
      have ih' := ih (sizeOf x) hxSize s' b' x rfl
      rw [hh] at ih'
      exact ih')
    y hYAttach
  rw [← hYsEq] at hSubOlds
  exact hCan subOld hSubOlds

/-- Reduction for `.ReferenceEquals lhs rhs`. -/
private theorem mapStmtExprM_insideOld_referenceEquals_run
    (s : PushOldState) (b : Bool) (lhs rhs : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.ReferenceEquals lhs rhs, src⟩).run b).run s).fst.fst =
    ⟨.ReferenceEquals
      (((mapStmtExprM insideOld lhs).run b).run s).fst.fst
      (((mapStmtExprM insideOld rhs).run
          (((mapStmtExprM insideOld lhs).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld lhs).run b).run s).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  generalize hL : (mapStmtExprM insideOld lhs b) s = resL
  obtain ⟨⟨lhs', bL⟩, sL⟩ := resL
  simp only []
  generalize hR : (mapStmtExprM insideOld rhs bL) sL = resR
  obtain ⟨⟨rhs', bR⟩, sR⟩ := resR
  rfl

private theorem mapStmtExprM_insideOld_canonical_referenceEquals
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (lhs rhs : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.ReferenceEquals lhs rhs, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_referenceEquals_run]
  intro subOld hSub
  rw [subOlds_referenceEquals] at hSub
  rw [List.mem_append] at hSub
  have hLSz : sizeOf lhs < n := by
    rw [← hSize]
    have hValEq : (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd).val = .ReferenceEquals lhs rhs := rfl
    have h1 : sizeOf (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd).val
              < sizeOf (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf lhs < sizeOf (StmtExpr.ReferenceEquals lhs rhs) := by term_by_mem
    omega
  have hRSz : sizeOf rhs < n := by
    rw [← hSize]
    have hValEq : (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd).val = .ReferenceEquals lhs rhs := rfl
    have h1 : sizeOf (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd).val
              < sizeOf (⟨.ReferenceEquals lhs rhs, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf rhs < sizeOf (StmtExpr.ReferenceEquals lhs rhs) := by term_by_mem
    omega
  cases hSub with
  | inl h => exact ih (sizeOf lhs) hLSz s b lhs rfl subOld h
  | inr h =>
    have hPresL := mapStmtExprM_insideOld_preserves_inoutNames s b lhs
    let sL := (((mapStmtExprM insideOld lhs).run b).run s).snd
    let bL := (((mapStmtExprM insideOld lhs).run b).run s).fst.snd
    have hCan := ih (sizeOf rhs) hRSz sL bL rhs rfl
    have hSame : sL.inoutNames = s.inoutNames := hPresL
    rw [hSame] at hCan
    exact hCan subOld h

/-- Reduction for `.InstanceCall t callee args`. -/
private theorem mapStmtExprM_insideOld_instanceCall_run
    (s : PushOldState) (b : Bool) (t : StmtExprMd) (callee : Identifier)
    (args : List StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.InstanceCall t callee args, src⟩).run b).run s).fst.fst =
    ⟨.InstanceCall
      (((mapStmtExprM insideOld t).run b).run s).fst.fst callee
      ((args.mapM (mapStmtExprM insideOld)
          (((mapStmtExprM insideOld t).run b).run s).fst.snd
          (((mapStmtExprM insideOld t).run b).run s).snd).fst.fst), src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  rw [mapStmtExprM_insideOld_attach_mapM_eq]
  generalize hT : (mapStmtExprM insideOld t b) s = resT
  obtain ⟨⟨t', bT⟩, sT⟩ := resT
  simp only []
  generalize hA : (args.mapM (mapStmtExprM insideOld) bT) sT = resA
  obtain ⟨⟨args', bA⟩, sA⟩ := resA
  rfl

/-- subOlds of `.InstanceCall t callee args`. -/
theorem subOlds_instanceCall (t : StmtExprMd) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds t ++ (args.attach.map fun ⟨a, _⟩ => StmtExprMd.subOlds a).flatten := by
  rw [StmtExprMd.subOlds]

private theorem mapStmtExprM_insideOld_canonical_instanceCall
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (t : StmtExprMd) (callee : Identifier)
    (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.InstanceCall t callee args, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_instanceCall_run]
  intro subOld hSub
  rw [subOlds_instanceCall] at hSub
  rw [List.mem_append] at hSub
  have hTSz : sizeOf t < n := by
    rw [← hSize]
    have hValEq : (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val = .InstanceCall t callee args := rfl
    have h1 : sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val
              < sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf t < sizeOf (StmtExpr.InstanceCall t callee args) := by term_by_mem
    omega
  cases hSub with
  | inl h => exact ih (sizeOf t) hTSz s b t rfl subOld h
  | inr h =>
    simp only [List.mem_flatten, List.mem_map] at h
    obtain ⟨ys, ⟨⟨y, hyMem⟩, _, hYsEq⟩, hSubInY⟩ := h
    have hPresT := mapStmtExprM_insideOld_preserves_inoutNames s b t
    let sT := (((mapStmtExprM insideOld t).run b).run s).snd
    let bT := (((mapStmtExprM insideOld t).run b).run s).fst.snd
    have hCanArgs : ∀ y' ∈ ((args.mapM (mapStmtExprM insideOld)).run bT sT).fst.fst,
          AllSubOldsCanonical s.inoutNames y' := by
      apply mapStmtExprM_insideOld_listMapM_canonical args sT bT s.inoutNames hPresT
      intro x hx s' b' hh
      have hxSize : sizeOf x < n := by
        rw [← hSize]
        have hValEq : (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val = .InstanceCall t callee args := rfl
        have h1 : sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val
                  < sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) :=
          AstNode.sizeOf_val_lt _
        rw [hValEq] at h1
        have hxLt : sizeOf x < sizeOf (StmtExpr.InstanceCall t callee args) := by term_by_mem
        omega
      have ih' := ih (sizeOf x) hxSize s' b' x rfl
      rw [hh] at ih'
      exact ih'
    rw [← hYsEq] at hSubInY
    apply hCanArgs y _ subOld hSubInY
    show y ∈ (args.mapM (mapStmtExprM insideOld) bT sT).fst.fst
    exact hyMem

/-- Reduction for `.PureFieldUpdate t fn nv`. -/
private theorem mapStmtExprM_insideOld_pureFieldUpdate_run
    (s : PushOldState) (b : Bool) (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.PureFieldUpdate t fn nv, src⟩).run b).run s).fst.fst =
    ⟨.PureFieldUpdate
      (((mapStmtExprM insideOld t).run b).run s).fst.fst fn
      (((mapStmtExprM insideOld nv).run
          (((mapStmtExprM insideOld t).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld t).run b).run s).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  generalize hT : (mapStmtExprM insideOld t b) s = resT
  obtain ⟨⟨t', bT⟩, sT⟩ := resT
  simp only []
  generalize hN : (mapStmtExprM insideOld nv bT) sT = resN
  obtain ⟨⟨nv', bN⟩, sN⟩ := resN
  rfl

private theorem mapStmtExprM_insideOld_canonical_pureFieldUpdate
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.PureFieldUpdate t fn nv, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_pureFieldUpdate_run]
  intro subOld hSub
  rw [subOlds_pureFieldUpdate] at hSub
  rw [List.mem_append] at hSub
  have hTSz : sizeOf t < n := by
    rw [← hSize]
    have hValEq : (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd).val = .PureFieldUpdate t fn nv := rfl
    have h1 : sizeOf (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd).val
              < sizeOf (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf t < sizeOf (StmtExpr.PureFieldUpdate t fn nv) := by term_by_mem
    omega
  have hNSz : sizeOf nv < n := by
    rw [← hSize]
    have hValEq : (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd).val = .PureFieldUpdate t fn nv := rfl
    have h1 : sizeOf (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd).val
              < sizeOf (⟨.PureFieldUpdate t fn nv, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf nv < sizeOf (StmtExpr.PureFieldUpdate t fn nv) := by term_by_mem
    omega
  cases hSub with
  | inl h => exact ih (sizeOf t) hTSz s b t rfl subOld h
  | inr h =>
    have hPresT := mapStmtExprM_insideOld_preserves_inoutNames s b t
    let sT := (((mapStmtExprM insideOld t).run b).run s).snd
    let bT := (((mapStmtExprM insideOld t).run b).run s).fst.snd
    have hCan := ih (sizeOf nv) hNSz sT bT nv rfl
    have hSame : sT.inoutNames = s.inoutNames := hPresT
    rw [hSame] at hCan
    exact hCan subOld h

/-- Reduction for `.ProveBy v p`. -/
private theorem mapStmtExprM_insideOld_proveBy_run
    (s : PushOldState) (b : Bool) (v p : StmtExprMd) (src : Option FileRange) :
    (((mapStmtExprM insideOld ⟨.ProveBy v p, src⟩).run b).run s).fst.fst =
    ⟨.ProveBy
      (((mapStmtExprM insideOld v).run b).run s).fst.fst
      (((mapStmtExprM insideOld p).run
          (((mapStmtExprM insideOld v).run b).run s).fst.snd).run
        (((mapStmtExprM insideOld v).run b).run s).snd).fst.fst, src⟩ := by
  rw [mapStmtExprM]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
  generalize hV : (mapStmtExprM insideOld v b) s = resV
  obtain ⟨⟨v', bV⟩, sV⟩ := resV
  simp only []
  generalize hP : (mapStmtExprM insideOld p bV) sV = resP
  obtain ⟨⟨p', bP⟩, sP⟩ := resP
  rfl

private theorem mapStmtExprM_insideOld_canonical_proveBy
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (v p : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.ProveBy v p, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.ProveBy v p, src⟩).run b).run s).fst.fst := by
  rw [mapStmtExprM_insideOld_proveBy_run]
  intro subOld hSub
  rw [subOlds_proveBy] at hSub
  rw [List.mem_append] at hSub
  have hVSz : sizeOf v < n := by
    rw [← hSize]
    have hValEq : (⟨.ProveBy v p, src⟩ : StmtExprMd).val = .ProveBy v p := rfl
    have h1 : sizeOf (⟨.ProveBy v p, src⟩ : StmtExprMd).val
              < sizeOf (⟨.ProveBy v p, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf v < sizeOf (StmtExpr.ProveBy v p) := by term_by_mem
    omega
  have hPSz : sizeOf p < n := by
    rw [← hSize]
    have hValEq : (⟨.ProveBy v p, src⟩ : StmtExprMd).val = .ProveBy v p := rfl
    have h1 : sizeOf (⟨.ProveBy v p, src⟩ : StmtExprMd).val
              < sizeOf (⟨.ProveBy v p, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    rw [hValEq] at h1
    have : sizeOf p < sizeOf (StmtExpr.ProveBy v p) := by term_by_mem
    omega
  cases hSub with
  | inl h => exact ih (sizeOf v) hVSz s b v rfl subOld h
  | inr h =>
    have hPresV := mapStmtExprM_insideOld_preserves_inoutNames s b v
    let sV := (((mapStmtExprM insideOld v).run b).run s).snd
    let bV := (((mapStmtExprM insideOld v).run b).run s).fst.snd
    have hCan := ih (sizeOf p) hPSz sV bV p rfl
    have hSame : sV.inoutNames = s.inoutNames := hPresV
    rw [hSame] at hCan
    exact hCan subOld h

/-- Per-target processing as an unattached function. Pulled out so we can
    rewrite the attach-form into a plain `mapM` for induction. -/
@[reducible]
private def mapAssignTargetOne (v : AstNode Variable) :
    StateT Bool PushOldM (AstNode Variable) := do
  let ⟨vv, vs⟩ := v
  match vv with
  | .Field target fieldName =>
    pure ⟨Variable.Field (← mapStmtExprM insideOld target) fieldName, vs⟩
  | .Local _ | .Declare _ => pure v

private theorem mapAssignTargets_eq_mapM (targets : List (AstNode Variable)) :
    mapAssignTargets targets = targets.mapM mapAssignTargetOne := by
  unfold mapAssignTargets
  rw [List.mapM_subtype (g := mapAssignTargetOne) (by
    intro v _hMem
    unfold mapAssignTargetOne
    obtain ⟨vv, vs⟩ := v
    cases vv <;> rfl)]
  rw [List.unattach_attach]

/-- Per-target preservation: `mapAssignTargetOne v` preserves `inoutNames`. -/
private theorem mapAssignTargetOne_preserves_inoutNames
    (v : AstNode Variable) (s : PushOldState) (b : Bool) :
    ((mapAssignTargetOne v).run b s).snd.inoutNames = s.inoutNames := by
  unfold mapAssignTargetOne
  obtain ⟨vv, vs⟩ := v
  match vv with
  | .Field target fieldName =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapStmtExprM insideOld target b) s = res
    obtain ⟨⟨t', b'⟩, s'⟩ := res
    have hPres := mapStmtExprM_insideOld_preserves_inoutNames s b target
    have hSnd : (((mapStmtExprM insideOld target).run b).run s).snd = s' := by
      show (mapStmtExprM insideOld target b s).snd = s'
      rw [hM]
    rw [hSnd] at hPres
    exact hPres
  | .Local _ => simp [StateT.run, StateT.pure, pure]
  | .Declare _ => simp [StateT.run, StateT.pure, pure]

/-- List-preservation for `mapAssignTargetOne`. -/
private theorem listMapM_mapAssignTargetOne_preserves_inoutNames
    (xs : List (AstNode Variable)) (s : PushOldState) (b : Bool) :
    ((xs.mapM mapAssignTargetOne).run b s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s b with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapAssignTargetOne x b) s = resX
    obtain ⟨⟨x', bX⟩, sX⟩ := resX
    have hPresX := mapAssignTargetOne_preserves_inoutNames x s b
    have hSX : ((mapAssignTargetOne x).run b s).snd = sX := by
      show (mapAssignTargetOne x b s).snd = sX
      rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM mapAssignTargetOne bX sX = resRest
    obtain ⟨⟨ys', bRest⟩, sRest⟩ := resRest
    have hRestPres := ih sX bX
    have hSR : (xs.mapM mapAssignTargetOne bX sX).snd = sRest := by rw [hRest]
    have hSR' : ((xs.mapM mapAssignTargetOne).run bX sX).snd = sRest := hSR
    rw [hSR'] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

/-- The targets-traversal preserves `inoutNames`. -/
private theorem mapAssignTargets_preserves_inoutNames
    (targets : List (AstNode Variable)) (s : PushOldState) (b : Bool) :
    (mapAssignTargets targets b s).snd.inoutNames = s.inoutNames := by
  rw [mapAssignTargets_eq_mapM]
  exact listMapM_mapAssignTargetOne_preserves_inoutNames targets s b

/-- subOlds of `.Assign targets value`. -/
theorem subOlds_assign (targets : List (AstNode Variable)) (value : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.Assign targets value, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds value := by
  rw [StmtExprMd.subOlds]

/-- Inline targets-traversal canonical: the value-field of `mapStmtExprM`'s
    `.Assign` result is canonical w.r.t. the threaded `inoutNames`. -/
private theorem mapStmtExprM_insideOld_canonical_assign
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (b' : Bool) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames
            (((mapStmtExprM insideOld e').run b').run s').fst.fst)
    (s : PushOldState) (b : Bool) (targets : List (AstNode Variable))
    (value : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.Assign targets value, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      (((mapStmtExprM insideOld ⟨.Assign targets value, src⟩).run b).run s).fst.fst := by
  have hValEq : (⟨.Assign targets value, src⟩ : StmtExprMd).val = .Assign targets value := rfl
  have hValLt := AstNode.sizeOf_val_lt (⟨.Assign targets value, src⟩ : StmtExprMd)
  rw [hValEq] at hValLt
  have hSpec : sizeOf (StmtExpr.Assign targets value) = 1 + sizeOf targets + sizeOf value :=
    StmtExpr.Assign.sizeOf_spec targets value
  have hVSz : sizeOf value < n := by omega
  intro subOld hSub
  rw [mapStmtExprM] at hSub
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld] at hSub
  generalize hRun :
    (((mapStmtExprM insideOld ⟨.Assign targets value, src⟩).run b).run s) = run0
  have hSub_named : subOld ∈ run0.fst.fst.subOlds := by
    rw [← hRun]
    show subOld ∈ (mapStmtExprM insideOld ⟨.Assign targets value, src⟩ b s).fst.fst.subOlds
    rw [mapStmtExprM]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
    exact hSub
  obtain ⟨⟨result, bRes⟩, sRes⟩ := run0
  simp only [Prod.fst, Prod.snd] at hSub_named
  have hResShape :
      ∃ (ts' : List (AstNode Variable)) (val' : StmtExprMd) (bT : Bool) (sT : PushOldState),
        result = ⟨.Assign ts' val', src⟩ ∧
        sT.inoutNames = s.inoutNames ∧
        val' = (((mapStmtExprM insideOld value).run bT).run sT).fst.fst := by
    refine ⟨(mapAssignTargets targets b s).fst.fst,
            (((mapStmtExprM insideOld value).run (mapAssignTargets targets b s).fst.snd).run
              (mapAssignTargets targets b s).snd).fst.fst,
            (mapAssignTargets targets b s).fst.snd,
            (mapAssignTargets targets b s).snd, ?_, ?_, ?_⟩
    · have : (((mapStmtExprM insideOld ⟨.Assign targets value, src⟩).run b).run s) =
             (((⟨.Assign (mapAssignTargets targets b s).fst.fst
                       (((mapStmtExprM insideOld value).run
                           (mapAssignTargets targets b s).fst.snd).run
                         (mapAssignTargets targets b s).snd).fst.fst, src⟩ : StmtExprMd),
                (((mapStmtExprM insideOld value).run
                    (mapAssignTargets targets b s).fst.snd).run
                  (mapAssignTargets targets b s).snd).fst.snd),
              (((mapStmtExprM insideOld value).run
                  (mapAssignTargets targets b s).fst.snd).run
                (mapAssignTargets targets b s).snd).snd) := by
        show (mapStmtExprM insideOld ⟨.Assign targets value, src⟩ b s) = _
        rw [mapStmtExprM]
        simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, insideOld]
        rfl
      rw [this] at hRun
      injection hRun with hOuter _
      injection hOuter with hRes _
      exact hRes.symm
    · exact mapAssignTargets_preserves_inoutNames targets s b
    · rfl
  obtain ⟨ts', val', bT, sT, hShape, hPresT, hValEq'⟩ := hResShape
  rw [hShape] at hSub_named
  rw [subOlds_assign] at hSub_named
  have ihV := ih (sizeOf value) hVSz sT bT value rfl
  rw [hPresT] at ihV
  rw [← hValEq'] at ihV
  exact ihV subOld hSub_named

/-- Every `Old` subterm of `mapStmtExprM insideOld e`'s output is canonical
    for `s.inoutNames`. -/
theorem mapStmtExprM_insideOld_canonical
    (s : PushOldState) (b : Bool) (e : StmtExprMd) :
    AllSubOldsCanonical s.inoutNames (((mapStmtExprM insideOld e).run b).run s).fst.fst := by
  induction h_sz : sizeOf e using Nat.strongRecOn generalizing e s b with
  | ind n ih =>
    -- Dispatch on e.val. Use existing per-case lemmas where available.
    cases hVal : e.val with
    | LiteralInt v =>
      have he : e = ⟨.LiteralInt v, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_literalInt s b v e.source
    | LiteralBool v =>
      have he : e = ⟨.LiteralBool v, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_literalBool s b v e.source
    | LiteralString str =>
      have he : e = ⟨.LiteralString str, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_literalString s b str e.source
    | LiteralDecimal d =>
      have he : e = ⟨.LiteralDecimal d, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_literalDecimal s b d e.source
    | New ref =>
      have he : e = ⟨.New ref, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_new s b ref e.source
    | This =>
      have he : e = ⟨.This, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_this s b e.source
    | Abstract =>
      have he : e = ⟨.Abstract, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_abstract s b e.source
    | All =>
      have he : e = ⟨.All, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_all s b e.source
    | Exit label =>
      have he : e = ⟨.Exit label, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_exit s b label e.source
    | Var v =>
      cases v with
      | Local nm =>
        have he : e = ⟨.Var (.Local nm), e.source⟩ := by cases e; simp_all
        rw [he]
        exact mapStmtExprM_insideOld_canonical_varLocal s b nm e.source
      | Declare p =>
        have he : e = ⟨.Var (.Declare p), e.source⟩ := by cases e; simp_all
        rw [he]
        exact mapStmtExprM_insideOld_canonical_varDeclare s b p e.source
      | Field target fn =>
        have he : e = ⟨.Var (.Field target fn), e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_varField s b target fn e.source
        apply ih (sizeOf target) _ s b target rfl
        have hVal_size : sizeOf e.val = 1 + (1 + sizeOf target + sizeOf fn) := by
          rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
    | Hole det ty =>
      have he : e = ⟨.Hole det ty, e.source⟩ := by cases e; simp_all
      rw [he]
      exact mapStmtExprM_insideOld_canonical_hole s b det ty e.source
    | Old inner =>
      have he : e = ⟨.Old inner, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_old s b inner e.source
      apply ih (sizeOf inner) _ s b inner rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf inner := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | Assigned m =>
      have he : e = ⟨.Assigned m, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_assigned s b m e.source
      apply ih (sizeOf m) _ s b m rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf m := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | Fresh v =>
      have he : e = ⟨.Fresh v, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_fresh s b v e.source
      apply ih (sizeOf v) _ s b v rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf v := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | AsType target ty =>
      have he : e = ⟨.AsType target ty, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_asType s b target ty e.source
      apply ih (sizeOf target) _ s b target rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | IsType target ty =>
      have he : e = ⟨.IsType target ty, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_isType s b target ty e.source
      apply ih (sizeOf target) _ s b target rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | Assume cond =>
      have he : e = ⟨.Assume cond, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_assume s b cond e.source
      apply ih (sizeOf cond) _ s b cond rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf cond := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | ContractOf ty fn =>
      have he : e = ⟨.ContractOf ty fn, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_contractOf s b ty fn e.source
      apply ih (sizeOf fn) _ s b fn rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf ty + sizeOf fn := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
    | Assert c =>
      have he : e = ⟨.Assert c, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_assert s b c e.source
      apply ih (sizeOf c.condition) _ s b c.condition rfl
      have hVal_size : sizeOf e.val = 1 + sizeOf c := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      have := Condition.sizeOf_condition_lt c
      omega
    | Return v =>
      cases v with
      | none =>
        have he : e = ⟨.Return none, e.source⟩ := by cases e; simp_all
        rw [he]
        exact mapStmtExprM_insideOld_canonical_return_none s b e.source
      | some r =>
        have he : e = ⟨.Return (some r), e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_return_some s b r e.source
        apply ih (sizeOf r) _ s b r rfl
        have hVal_size : sizeOf e.val = 1 + (1 + sizeOf r) := by
          rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
    | Quantifier mode param trigger body =>
      cases trigger with
      | none =>
        have he : e = ⟨.Quantifier mode param none body, e.source⟩ := by
          cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_quantifier_no_trigger s b mode param body e.source
        apply ih (sizeOf body) _ s b body rfl
        have hVal_size : sizeOf e.val = 1 + sizeOf mode + sizeOf param +
                         sizeOf (none : Option StmtExprMd) + sizeOf body := by
          rw [hVal]; rfl
        have := AstNode.sizeOf_val_lt e
        omega
      | some tr =>
        have he : e = ⟨.Quantifier mode param (some tr) body, e.source⟩ := by
          cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_quantifier_some ih s b mode param tr body e.source
        rw [← he, h_sz]
    | IfThenElse cond th el =>
      cases el with
      | none =>
        have he : e = ⟨.IfThenElse cond th none, e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_ifThenElse_none ih s b cond th e.source
        rw [← he, h_sz]
      | some elE =>
        have he : e = ⟨.IfThenElse cond th (some elE), e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_ifThenElse_some ih s b cond th elE e.source
        rw [← he, h_sz]
    | Block stmts label =>
      have he : e = ⟨.Block stmts label, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_block ih s b stmts label e.source
      rw [← he, h_sz]
    | While cond invs dec body =>
      cases dec with
      | none =>
        have he : e = ⟨.While cond invs none body, e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_while_none ih s b cond invs body e.source
        rw [← he, h_sz]
      | some d =>
        have he : e = ⟨.While cond invs (some d) body, e.source⟩ := by cases e; simp_all
        rw [he]
        apply mapStmtExprM_insideOld_canonical_while_some ih s b cond invs d body e.source
        rw [← he, h_sz]
    | StaticCall callee args =>
      have he : e = ⟨.StaticCall callee args, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_staticCall ih s b callee args e.source
      rw [← he, h_sz]
    | PrimitiveOp op args =>
      have he : e = ⟨.PrimitiveOp op args, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_primitiveOp ih s b op args e.source
      rw [← he, h_sz]
    | ReferenceEquals lhs rhs =>
      have he : e = ⟨.ReferenceEquals lhs rhs, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_referenceEquals ih s b lhs rhs e.source
      rw [← he, h_sz]
    | InstanceCall t callee args =>
      have he : e = ⟨.InstanceCall t callee args, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_instanceCall ih s b t callee args e.source
      rw [← he, h_sz]
    | Assign targets value =>
      have he : e = ⟨.Assign targets value, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_assign ih s b targets value e.source
      rw [← he, h_sz]
    | PureFieldUpdate t fn nv =>
      have he : e = ⟨.PureFieldUpdate t fn nv, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_pureFieldUpdate ih s b t fn nv e.source
      rw [← he, h_sz]
    | ProveBy v p =>
      have he : e = ⟨.ProveBy v p, e.source⟩ := by cases e; simp_all
      rw [he]
      apply mapStmtExprM_insideOld_canonical_proveBy ih s b v p e.source
      rw [← he, h_sz]

/-! ## Subgoal 4: `mapStmtExprPrePostM visitOld pure` produces canonical `Old`s -/

/-- For a leaf `e` whose `pushOldInwardExpr` result is identical and whose
    `subOlds` is empty, the canonical property holds trivially. -/
private theorem pushOldInwardExpr_leaf_canonical
    (s : PushOldState) (e : StmtExprMd)
    (hRes : ((pushOldInwardExpr e).run s).fst = e)
    (hLeaf : e.subOlds = []) :
    AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr e).run s).fst := by
  rw [hRes]
  exact allSubOldsCanonical_of_subOlds_nil hLeaf

private theorem pushOldInwardExpr_canonical_literalInt
    (s : PushOldState) (n : Int) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.LiteralInt n, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_literal_int n src)

private theorem pushOldInwardExpr_canonical_literalBool
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.LiteralBool b, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_literal_bool b src)

private theorem pushOldInwardExpr_canonical_varLocal
    (s : PushOldState) (n : Identifier) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Var (.Local n), src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_var_local n src)

private theorem pushOldInwardExpr_canonical_literalString
    (s : PushOldState) (str : String) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.LiteralString str, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_literal_string str src)

private theorem pushOldInwardExpr_canonical_literalDecimal
    (s : PushOldState) (d : Decimal) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.LiteralDecimal d, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_literal_decimal d src)

private theorem pushOldInwardExpr_canonical_new
    (s : PushOldState) (ref : Identifier) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.New ref, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_new ref src)

private theorem pushOldInwardExpr_canonical_this
    (s : PushOldState) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.This, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_this src)

private theorem pushOldInwardExpr_canonical_abstract
    (s : PushOldState) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Abstract, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_abstract src)

private theorem pushOldInwardExpr_canonical_all
    (s : PushOldState) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.All, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_all src)

private theorem pushOldInwardExpr_canonical_exit
    (s : PushOldState) (label : String) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Exit label, src⟩).run s).fst :=
  pushOldInwardExpr_leaf_canonical s _
    (by simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
              StateT.run, StateT.bind, bind, StateT.pure, pure])
    (subOlds_exit label src)

private theorem pushOldInwardExpr_canonical_hole
    (s : PushOldState) (det : Bool) (ty : Option (AstNode HighType)) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Hole det ty, src⟩).run s).fst := by
  apply pushOldInwardExpr_leaf_canonical
  · simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
          StateT.run, StateT.bind, bind, StateT.pure, pure]
  · rw [StmtExprMd.subOlds]

private theorem pushOldInwardExpr_canonical_varDeclare
    (s : PushOldState) (p : Parameter) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Var (.Declare p), src⟩).run s).fst := by
  apply pushOldInwardExpr_leaf_canonical
  · simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
          StateT.run, StateT.bind, bind, StateT.pure, pure]
  · rw [StmtExprMd.subOlds]



/-- For non-Old constructors, `visitOld` returns `none` and we drop to
    the recursive `match expr.val` arm. Used to step through reductions. -/
private theorem visitOld_non_old (s : PushOldState) (e : StmtExprMd)
    (hNotOld : ∀ inner, e.val ≠ .Old inner) :
    (visitOld e).run s = (none, s) := by
  unfold visitOld
  cases h : e.val
  case Old inner => exact absurd h (hNotOld inner)
  all_goals simp [StateT.run, StateT.pure, pure]

/-- `warn` preserves `inoutNames`. -/
private theorem warn_preserves_inoutNames (src : Option FileRange) (msg : String) (s : PushOldState) :
    ((warn src msg).run s).snd.inoutNames = s.inoutNames := by
  simp [warn, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        pure]

/-- `visitOld` preserves `inoutNames`. -/
private theorem visitOld_preserves_inoutNames (s : PushOldState) (e : StmtExprMd) :
    ((visitOld e).run s).snd.inoutNames = s.inoutNames := by
  unfold visitOld
  cases h : e.val with
  | Old inner =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (mapStmtExprM insideOld inner false) s = res
    obtain ⟨⟨inner', changed⟩, s'⟩ := res
    have hPres := mapStmtExprM_insideOld_preserves_inoutNames s false inner
    have : (((mapStmtExprM insideOld inner).run false).run s).snd = s' := by
      show (mapStmtExprM insideOld inner false s).snd = s'
      rw [hM]
    rw [this] at hPres
    by_cases hc : changed
    · simp [hc]
      exact hPres
    · simp [hc, warn, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            StateT.bind, StateT.pure, bind, pure]
      exact hPres
  | _ => simp [h, StateT.run, StateT.pure, pure]


/-- Generic list-preservation helper for `pushOldInwardExpr`. -/
private theorem listMapM_pushOldInwardExpr_preserves_inoutNames_of
    (xs : List StmtExprMd)
    (hPres : ∀ x ∈ xs, ∀ (s' : PushOldState),
              ((pushOldInwardExpr x).run s').snd.inoutNames = s'.inoutNames)
    (s : PushOldState) :
    ((xs.mapM pushOldInwardExpr).run s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (pushOldInwardExpr x) s = resX
    obtain ⟨x', sX⟩ := resX
    have hPresX := hPres x List.mem_cons_self s
    have hSX : ((pushOldInwardExpr x).run s).snd = sX := by
      show (pushOldInwardExpr x s).snd = sX
      rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM pushOldInwardExpr sX = resRest
    obtain ⟨ys', sRest⟩ := resRest
    have hRestPres : ((xs.mapM pushOldInwardExpr).run sX).snd.inoutNames = sX.inoutNames := by
      apply ih
      intro y hy s'
      exact hPres y (List.mem_cons_of_mem _ hy) s'
    have hSR : (xs.mapM pushOldInwardExpr sX).snd = sRest := by rw [hRest]
    have hSR' : ((xs.mapM pushOldInwardExpr).run sX).snd = sRest := hSR
    rw [hSR'] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

/-! ### Per-case preservation lemmas for `pushOldInwardExpr`. -/

private theorem pushOldInwardExpr_leaf_preserves
    (s : PushOldState) (e : StmtExprMd)
    (hRes : ((pushOldInwardExpr e).run s).snd = s) :
    ((pushOldInwardExpr e).run s).snd.inoutNames = s.inoutNames := by
  rw [hRes]

private theorem pushOldInwardExpr_literalInt_preserves
    (s : PushOldState) (n : Int) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.LiteralInt n, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_literalBool_preserves
    (s : PushOldState) (b : Bool) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.LiteralBool b, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_literalString_preserves
    (s : PushOldState) (str : String) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.LiteralString str, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_literalDecimal_preserves
    (s : PushOldState) (d : Decimal) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.LiteralDecimal d, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_new_preserves
    (s : PushOldState) (ref : Identifier) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.New ref, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_this_preserves
    (s : PushOldState) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.This, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_abstract_preserves
    (s : PushOldState) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Abstract, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_all_preserves
    (s : PushOldState) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.All, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_exit_preserves
    (s : PushOldState) (lbl : String) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Exit lbl, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_hole_preserves
    (s : PushOldState) (det : Bool) (ty : Option (AstNode HighType)) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Hole det ty, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_varLocal_preserves
    (s : PushOldState) (n : Identifier) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Var (.Local n), src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

private theorem pushOldInwardExpr_varDeclare_preserves
    (s : PushOldState) (p : Parameter) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Var (.Declare p), src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  simp [pushOldInwardExpr, mapStmtExprPrePostM, visitOld,
        StateT.run, StateT.bind, bind, StateT.pure, pure]

/-- Single-child case template: `pushOldInwardExpr ⟨.X child, src⟩` threads
    its state to running `pushOldInwardExpr child`. -/
private theorem pushOldInwardExpr_assigned_preserves
    (s : PushOldState) (n : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assigned n, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr n).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assigned n, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure n).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure n) s = res
  obtain ⟨n', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_fresh_preserves
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Fresh v, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr v).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Fresh v, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure v).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure v) s = res
  obtain ⟨v', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_varField_preserves
    (s : PushOldState) (target : StmtExprMd) (fn : Identifier) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Var (.Field target fn), src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr target).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Var (.Field target fn), src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure target).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_asType_preserves
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.AsType target ty, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr target).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.AsType target ty, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure target).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_isType_preserves
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IsType target ty, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr target).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IsType target ty, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure target).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_assume_preserves
    (s : PushOldState) (cond : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assume cond, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr cond).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assume cond, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure cond).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure cond) s = res
  obtain ⟨c', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_contractOf_preserves
    (s : PushOldState) (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ContractOf ty fn, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr fn).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ContractOf ty fn, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure fn).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure fn) s = res
  obtain ⟨f', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_assert_preserves
    (s : PushOldState) (c : Condition) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assert c, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr c.condition).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assert c, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure c.condition).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure c.condition) s = res
  obtain ⟨c', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_return_none_preserves
    (s : PushOldState) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Return none, src⟩).run s).snd.inoutNames = s.inoutNames := by
  apply pushOldInwardExpr_leaf_preserves
  show ((mapStmtExprPrePostM visitOld pure ⟨.Return none, src⟩).run s).snd = s
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp [StateT.run, StateT.bind, bind, StateT.pure, pure,
        Option.attach, Option.attachWith, Option.mapM]

private theorem pushOldInwardExpr_return_some_preserves
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Return (some v), src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr v).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Return (some v), src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure v).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hM : (mapStmtExprPrePostM visitOld pure v) s = res
  obtain ⟨v', s'⟩ := res
  rfl

/-- 2-child preservation: `.ReferenceEquals lhs rhs` threads state lhs → rhs. -/
private theorem pushOldInwardExpr_referenceEquals_preserves
    (s : PushOldState) (lhs rhs : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ReferenceEquals lhs rhs, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr rhs).run ((pushOldInwardExpr lhs).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ReferenceEquals lhs rhs, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure rhs).run
         ((mapStmtExprPrePostM visitOld pure lhs).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hL : (mapStmtExprPrePostM visitOld pure lhs) s = resL
  obtain ⟨lhs', sL⟩ := resL
  generalize hR : (mapStmtExprPrePostM visitOld pure rhs sL) = resR
  obtain ⟨rhs', sR⟩ := resR
  rfl

private theorem pushOldInwardExpr_pureFieldUpdate_preserves
    (s : PushOldState) (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.PureFieldUpdate t fn nv, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr nv).run ((pushOldInwardExpr t).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.PureFieldUpdate t fn nv, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure nv).run
         ((mapStmtExprPrePostM visitOld pure t).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hT : (mapStmtExprPrePostM visitOld pure t) s = resT
  obtain ⟨t', sT⟩ := resT
  generalize hN : (mapStmtExprPrePostM visitOld pure nv sT) = resN
  obtain ⟨nv', sN⟩ := resN
  rfl

private theorem pushOldInwardExpr_proveBy_preserves
    (s : PushOldState) (v p : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ProveBy v p, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr p).run ((pushOldInwardExpr v).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ProveBy v p, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure p).run
         ((mapStmtExprPrePostM visitOld pure v).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hV : (mapStmtExprPrePostM visitOld pure v) s = resV
  obtain ⟨v', sV⟩ := resV
  generalize hP : (mapStmtExprPrePostM visitOld pure p sV) = resP
  obtain ⟨p', sP⟩ := resP
  rfl

private theorem pushOldInwardExpr_ifThenElse_none_preserves
    (s : PushOldState) (cond th : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IfThenElse cond th none, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr th).run ((pushOldInwardExpr cond).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IfThenElse cond th none, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure th).run
         ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  generalize hT : (mapStmtExprPrePostM visitOld pure th sC) = resT
  obtain ⟨th', sT⟩ := resT
  rfl

private theorem pushOldInwardExpr_ifThenElse_some_preserves
    (s : PushOldState) (cond th elE : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IfThenElse cond th (some elE), src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr elE).run
      ((pushOldInwardExpr th).run ((pushOldInwardExpr cond).run s).snd).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IfThenElse cond th (some elE), src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure elE).run
         ((mapStmtExprPrePostM visitOld pure th).run
           ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  generalize hT : (mapStmtExprPrePostM visitOld pure th sC) = resT
  obtain ⟨th', sT⟩ := resT
  generalize hE : (mapStmtExprPrePostM visitOld pure elE sT) = resE
  obtain ⟨elE', sE⟩ := resE
  rfl

private theorem pushOldInwardExpr_quantifier_none_preserves
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Quantifier mode param none body, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr body).run s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Quantifier mode param none body, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure body).run s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hB : (mapStmtExprPrePostM visitOld pure body) s = resB
  obtain ⟨body', sB⟩ := resB
  rfl

private theorem pushOldInwardExpr_quantifier_some_preserves
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (tr body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Quantifier mode param (some tr) body, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr body).run ((pushOldInwardExpr tr).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Quantifier mode param (some tr) body, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure body).run
         ((mapStmtExprPrePostM visitOld pure tr).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hT : (mapStmtExprPrePostM visitOld pure tr) s = resT
  obtain ⟨tr', sT⟩ := resT
  generalize hB : (mapStmtExprPrePostM visitOld pure body sT) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

/-- `xs.attach.mapM (fun ⟨e, _⟩ => mapStmtExprPrePostM visitOld StateT.pure e) = xs.mapM pushOldInwardExpr`. -/
private theorem pushOldInwardExpr_attach_mapM_eq (xs : List StmtExprMd) :
    (xs.attach.mapM fun (e : { e // e ∈ xs }) => mapStmtExprPrePostM visitOld StateT.pure e.val)
      = xs.mapM pushOldInwardExpr := by
  rw [List.mapM_subtype (g := pushOldInwardExpr) (by intros; rfl)]
  rw [List.unattach_attach]

/-- List-preservation helper for `pushOldInwardExpr`. -/
private theorem listMapM_pushOldInwardExpr_preserves
    (xs : List StmtExprMd) (s : PushOldState)
    (hPres : ∀ x ∈ xs, ∀ (s' : PushOldState),
              ((pushOldInwardExpr x).run s').snd.inoutNames = s'.inoutNames) :
    ((xs.mapM pushOldInwardExpr) s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (pushOldInwardExpr x) s = resX
    obtain ⟨x', sX⟩ := resX
    have hPresX := hPres x List.mem_cons_self s
    have hSX : ((pushOldInwardExpr x).run s).snd = sX := by
      show (pushOldInwardExpr x s).snd = sX
      rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM pushOldInwardExpr sX = resRest
    obtain ⟨ys', sRest⟩ := resRest
    have hRestPres : ((xs.mapM pushOldInwardExpr) sX).snd.inoutNames = sX.inoutNames := by
      apply ih
      intro y hy s'
      exact hPres y (List.mem_cons_of_mem _ hy) s'
    have hSR' : (xs.mapM pushOldInwardExpr sX).snd = sRest := by rw [hRest]
    rw [hSR'] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

private theorem pushOldInwardExpr_block_preserves
    (s : PushOldState) (stmts : List StmtExprMd) (label : Option String) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Block stmts label, src⟩).run s).snd.inoutNames =
    ((stmts.mapM pushOldInwardExpr) s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Block stmts label, src⟩).run s).snd.inoutNames =
       ((stmts.mapM pushOldInwardExpr) s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.Block stmts label, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hM : (stmts.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_staticCall_preserves
    (s : PushOldState) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.StaticCall callee args, src⟩).run s).snd.inoutNames =
    ((args.mapM pushOldInwardExpr) s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.StaticCall callee args, src⟩).run s).snd.inoutNames =
       ((args.mapM pushOldInwardExpr) s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.StaticCall callee args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hM : (args.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_primitiveOp_preserves
    (s : PushOldState) (op : Operation) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.PrimitiveOp op args, src⟩).run s).snd.inoutNames =
    ((args.mapM pushOldInwardExpr) s).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.PrimitiveOp op args, src⟩).run s).snd.inoutNames =
       ((args.mapM pushOldInwardExpr) s).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.PrimitiveOp op args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hM : (args.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_instanceCall_preserves
    (s : PushOldState) (t : StmtExprMd) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.InstanceCall t callee args, src⟩).run s).snd.inoutNames =
    ((args.mapM pushOldInwardExpr) ((pushOldInwardExpr t).run s).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.InstanceCall t callee args, src⟩).run s).snd.inoutNames =
       ((args.mapM pushOldInwardExpr) ((mapStmtExprPrePostM visitOld pure t).run s).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.InstanceCall t callee args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hT : (mapStmtExprPrePostM visitOld pure t) s = resT
  obtain ⟨t', sT⟩ := resT
  simp only [Prod.snd]
  generalize hA : (args.mapM pushOldInwardExpr sT) = resA
  obtain ⟨ys, sR⟩ := resA
  rfl

private theorem pushOldInwardExpr_while_none_preserves
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.While cond invs none body, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr body).run
      ((invs.mapM pushOldInwardExpr) ((pushOldInwardExpr cond).run s).snd).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.While cond invs none body, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure body).run
         ((invs.mapM pushOldInwardExpr) ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.While cond invs none body, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  simp only [Prod.snd]
  generalize hI : (invs.mapM pushOldInwardExpr sC) = resI
  obtain ⟨invs', sI⟩ := resI
  simp only [Prod.snd]
  generalize hB : (mapStmtExprPrePostM visitOld pure body sI) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

private theorem pushOldInwardExpr_while_some_preserves
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (d body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.While cond invs (some d) body, src⟩).run s).snd.inoutNames =
    ((pushOldInwardExpr body).run
      ((pushOldInwardExpr d).run
        ((invs.mapM pushOldInwardExpr) ((pushOldInwardExpr cond).run s).snd).snd).snd).snd.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.While cond invs (some d) body, src⟩).run s).snd.inoutNames =
       ((mapStmtExprPrePostM visitOld pure body).run
         ((mapStmtExprPrePostM visitOld pure d).run
           ((invs.mapM pushOldInwardExpr) ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd).snd).snd.inoutNames
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.While cond invs (some d) body, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [pushOldInwardExpr_attach_mapM_eq]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  simp only [Prod.snd]
  generalize hI : (invs.mapM pushOldInwardExpr sC) = resI
  obtain ⟨invs', sI⟩ := resI
  simp only [Prod.snd]
  generalize hD : (mapStmtExprPrePostM visitOld pure d sI) = resD
  obtain ⟨d', sD⟩ := resD
  simp only [Prod.snd]
  generalize hB : (mapStmtExprPrePostM visitOld pure body sD) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

/-- Preservation for `.Old`: only `mapStmtExprM insideOld` runs on `inner`,
    which preserves `inoutNames`; `warn` may modify diagnostics but not inouts. -/
private theorem pushOldInwardExpr_old_preserves
    (s : PushOldState) (inner : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Old inner, src⟩).run s).snd.inoutNames = s.inoutNames := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Old inner, src⟩).run s).snd.inoutNames = s.inoutNames
  unfold mapStmtExprPrePostM visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld inner false) s = res
  obtain ⟨⟨inner', changed⟩, s'⟩ := res
  have hPres := mapStmtExprM_insideOld_preserves_inoutNames s false inner
  have hSEq : (((mapStmtExprM insideOld inner).run false).run s).snd = s' := by
    show (mapStmtExprM insideOld inner false s).snd = s'
    rw [hM]
  rw [hSEq] at hPres
  by_cases hc : changed
  · simp [hc]
    exact hPres
  · simp [hc, warn, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          StateT.bind, StateT.pure, bind, pure]
    exact hPres


/-- Reduction for `pushOldInwardExpr` on `.Assigned n`. -/
private theorem pushOldInwardExpr_assigned_run
    (s : PushOldState) (n : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assigned n, src⟩).run s).fst =
    ⟨.Assigned ((pushOldInwardExpr n).run s).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assigned n, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure n) s = res
  obtain ⟨n', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_assigned
    (s : PushOldState) (n : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr n).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Assigned n, src⟩).run s).fst := by
  rw [pushOldInwardExpr_assigned_run]
  intro subOld hSub
  rw [subOlds_assigned] at hSub
  exact ih subOld hSub

/-- Reduction for `pushOldInwardExpr` on `.Fresh v`. -/
private theorem pushOldInwardExpr_fresh_run
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Fresh v, src⟩).run s).fst =
    ⟨.Fresh ((pushOldInwardExpr v).run s).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Fresh v, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure v) s = res
  obtain ⟨v', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_fresh
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr v).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Fresh v, src⟩).run s).fst := by
  rw [pushOldInwardExpr_fresh_run]
  intro subOld hSub
  rw [subOlds_fresh] at hSub
  exact ih subOld hSub

/-- Reduction for `.Var (.Field target fn)`. -/
private theorem pushOldInwardExpr_varField_run
    (s : PushOldState) (target : StmtExprMd) (fn : Identifier) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Var (.Field target fn), src⟩).run s).fst =
    ⟨.Var (.Field ((pushOldInwardExpr target).run s).fst fn), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Var (.Field target fn), src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_varField
    (s : PushOldState) (target : StmtExprMd) (fn : Identifier) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr target).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Var (.Field target fn), src⟩).run s).fst := by
  rw [pushOldInwardExpr_varField_run]
  intro subOld hSub
  rw [subOlds_var_field] at hSub
  exact ih subOld hSub

/-- Reduction for `.AsType target ty`. -/
private theorem pushOldInwardExpr_asType_run
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.AsType target ty, src⟩).run s).fst =
    ⟨.AsType ((pushOldInwardExpr target).run s).fst ty, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.AsType target ty, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_asType
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr target).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.AsType target ty, src⟩).run s).fst := by
  rw [pushOldInwardExpr_asType_run]
  intro subOld hSub
  rw [subOlds_asType] at hSub
  exact ih subOld hSub

/-- Reduction for `.IsType target ty`. -/
private theorem pushOldInwardExpr_isType_run
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IsType target ty, src⟩).run s).fst =
    ⟨.IsType ((pushOldInwardExpr target).run s).fst ty, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IsType target ty, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure target) s = res
  obtain ⟨target', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_isType
    (s : PushOldState) (target : StmtExprMd) (ty : AstNode HighType) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr target).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.IsType target ty, src⟩).run s).fst := by
  rw [pushOldInwardExpr_isType_run]
  intro subOld hSub
  rw [subOlds_isType] at hSub
  exact ih subOld hSub

/-- Reduction for `.Assume cond`. -/
private theorem pushOldInwardExpr_assume_run
    (s : PushOldState) (cond : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assume cond, src⟩).run s).fst =
    ⟨.Assume ((pushOldInwardExpr cond).run s).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assume cond, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure cond) s = res
  obtain ⟨c', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_assume
    (s : PushOldState) (cond : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr cond).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Assume cond, src⟩).run s).fst := by
  rw [pushOldInwardExpr_assume_run]
  intro subOld hSub
  rw [subOlds_assume] at hSub
  exact ih subOld hSub

/-- Reduction for `.ContractOf ty fn`. -/
private theorem pushOldInwardExpr_contractOf_run
    (s : PushOldState) (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ContractOf ty fn, src⟩).run s).fst =
    ⟨.ContractOf ty ((pushOldInwardExpr fn).run s).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ContractOf ty fn, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure fn) s = res
  obtain ⟨f', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_contractOf
    (s : PushOldState) (ty : ContractType) (fn : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr fn).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.ContractOf ty fn, src⟩).run s).fst := by
  rw [pushOldInwardExpr_contractOf_run]
  intro subOld hSub
  rw [subOlds_contractOf] at hSub
  exact ih subOld hSub

/-- Reduction for `.Assert c`. -/
private theorem pushOldInwardExpr_assert_run
    (s : PushOldState) (c : Condition) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assert c, src⟩).run s).fst =
    ⟨.Assert { c with condition := ((pushOldInwardExpr c.condition).run s).fst }, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Assert c, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprPrePostM visitOld pure c.condition) s = res
  obtain ⟨c', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_assert
    (s : PushOldState) (c : Condition) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr c.condition).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Assert c, src⟩).run s).fst := by
  rw [pushOldInwardExpr_assert_run]
  intro subOld hSub
  rw [subOlds_assert] at hSub
  exact ih subOld hSub

/-- Reduction for `.Return none`. -/
private theorem pushOldInwardExpr_return_none_run
    (s : PushOldState) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Return none, src⟩).run s).fst =
    ⟨.Return none, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Return none, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp [StateT.run, StateT.bind, bind, StateT.pure, pure,
        Option.attach, Option.attachWith, Option.mapM]

private theorem pushOldInwardExpr_canonical_return_none
    (s : PushOldState) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Return none, src⟩).run s).fst := by
  rw [pushOldInwardExpr_return_none_run]
  exact allSubOldsCanonical_of_subOlds_nil (subOlds_return_none src)

/-- Reduction for `.Return (some v)`. -/
private theorem pushOldInwardExpr_return_some_run
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Return (some v), src⟩).run s).fst =
    ⟨.Return (some ((pushOldInwardExpr v).run s).fst), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Return (some v), src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hM : (mapStmtExprPrePostM visitOld pure v) s = res
  obtain ⟨v', s'⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_return_some
    (s : PushOldState) (v : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr v).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Return (some v), src⟩).run s).fst := by
  rw [pushOldInwardExpr_return_some_run]
  intro subOld hSub
  rw [subOlds_return_some] at hSub
  exact ih subOld hSub

/-- Reduction lemma: `pushOldInwardExpr ⟨.Old inner, src⟩` evaluates to
    the result of `mapStmtExprM insideOld inner` (in the underlying state). -/
private theorem pushOldInwardExpr_old_run
    (s : PushOldState) (inner : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Old inner, src⟩).run s).fst =
    (((mapStmtExprM insideOld inner).run false).run s).fst.fst := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Old inner, src⟩).run s).fst =
    (((mapStmtExprM insideOld inner).run false).run s).fst.fst
  unfold mapStmtExprPrePostM visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hM : (mapStmtExprM insideOld inner false) s = res
  obtain ⟨⟨inner', changed⟩, s'⟩ := res
  by_cases h : changed
  all_goals (simp [h, warn, modify, modifyGet, MonadStateOf.modifyGet,
                   StateT.modifyGet, StateT.bind, StateT.pure, bind, pure])

private theorem pushOldInwardExpr_canonical_old
    (s : PushOldState) (inner : StmtExprMd) (src : Option FileRange) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Old inner, src⟩).run s).fst := by
  rw [pushOldInwardExpr_old_run]
  exact mapStmtExprM_insideOld_canonical s false inner

/-- The targets-traversal helper for `.Assign` in `pushOldInwardExpr`.
    Analogous to `mapAssignTargets` but for `mapStmtExprPrePostM`. -/
@[reducible]
private def pushAssignTargets (targets : List (AstNode Variable)) :
    PushOldM (List (AstNode Variable)) :=
  targets.attach.mapM
    (fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← pushOldInwardExpr target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v)

/-- The result of `pushOldInwardExpr ⟨.Assign t v, src⟩` reduces (by `rfl`)
    to an explicit shape using `pushAssignTargets`. -/
private theorem pushOldInwardExpr_assign_run_eq
    (s : PushOldState) (targets : List (AstNode Variable))
    (value : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Assign targets value, src⟩).run s) =
    (((⟨.Assign (pushAssignTargets targets s).fst
                ((pushOldInwardExpr value).run
                  (pushAssignTargets targets s).snd).fst, src⟩ : StmtExprMd)),
      ((pushOldInwardExpr value).run
        (pushAssignTargets targets s).snd).snd) := by
  show (mapStmtExprPrePostM visitOld pure ⟨.Assign targets value, src⟩ s) = _
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.Assign targets value, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rfl

/-- Per-target unattached processor for `pushOldInwardExpr`'s targets traversal. -/
private def pushAssignTargetsAux (v : AstNode Variable) :
    PushOldM (AstNode Variable) := do
  let ⟨vv, vs⟩ := v
  match vv with
  | .Field target fieldName =>
    pure ⟨Variable.Field (← pushOldInwardExpr target) fieldName, vs⟩
  | .Local _ | .Declare _ => pure v

private theorem pushAssignTargets_eq_unattached (targets : List (AstNode Variable)) :
    pushAssignTargets targets = targets.mapM pushAssignTargetsAux := by
  unfold pushAssignTargets
  rw [List.mapM_subtype (g := pushAssignTargetsAux) (by
    intro v _hMem
    unfold pushAssignTargetsAux
    obtain ⟨vv, vs⟩ := v
    cases vv <;> rfl)]
  rw [List.unattach_attach]

private theorem pushAssignTargetsAux_preserves_inoutNames_of
    (xs : List (AstNode Variable))
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ xs →
              ∀ (s' : PushOldState),
              ((pushOldInwardExpr tgt).run s').snd.inoutNames = s'.inoutNames)
    (v : AstNode Variable) (hMemV : v ∈ xs) (s : PushOldState) :
    ((pushAssignTargetsAux v).run s).snd.inoutNames = s.inoutNames := by
  unfold pushAssignTargetsAux
  obtain ⟨vv, vs⟩ := v
  cases vv with
  | Field target fieldName =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hMt : (pushOldInwardExpr target) s = res
    obtain ⟨t', s'⟩ := res
    have hPHead := hPres target fieldName vs hMemV s
    have : ((pushOldInwardExpr target).run s).snd = s' := by
      show (pushOldInwardExpr target s).snd = s'
      rw [hMt]
    rw [this] at hPHead
    exact hPHead
  | Local _ => simp [StateT.run, StateT.pure, pure]
  | Declare _ => simp [StateT.run, StateT.pure, pure]

private theorem listMapM_pushAssignTargetsAux_preserves_inoutNames_of
    (xs : List (AstNode Variable))
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ xs →
              ∀ (s' : PushOldState),
              ((pushOldInwardExpr tgt).run s').snd.inoutNames = s'.inoutNames)
    (s : PushOldState) :
    ((xs.mapM pushAssignTargetsAux).run s).snd.inoutNames = s.inoutNames := by
  suffices hGen : ∀ (ys : List (AstNode Variable)),
      (∀ y ∈ ys, y ∈ xs) →
      ∀ (s' : PushOldState),
      ((ys.mapM pushAssignTargetsAux).run s').snd.inoutNames = s'.inoutNames by
    exact hGen xs (fun _ h => h) s
  intro ys hYsSub
  induction ys with
  | nil =>
    intro s'
    simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons y ys ihL =>
    intro s'
    rw [List.mapM_cons]
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (pushAssignTargetsAux y) s' = resY
    obtain ⟨y', sY⟩ := resY
    have hPresY := pushAssignTargetsAux_preserves_inoutNames_of xs hPres y
                    (hYsSub y List.mem_cons_self) s'
    have hSY : ((pushAssignTargetsAux y).run s').snd = sY := by
      show (pushAssignTargetsAux y s').snd = sY
      rw [hM]
    rw [hSY] at hPresY
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : ys.mapM pushAssignTargetsAux sY = resRest
    obtain ⟨ys', sRest⟩ := resRest
    have hYsSubTail : ∀ z ∈ ys, z ∈ xs :=
      fun z hz => hYsSub z (List.mem_cons_of_mem _ hz)
    have hTailRes := ihL hYsSubTail sY
    have hSR' : ((ys.mapM pushAssignTargetsAux).run sY).snd = sRest := by
      show (ys.mapM pushAssignTargetsAux sY).snd = sRest
      rw [hRest]
    rw [hSR'] at hTailRes
    show sRest.inoutNames = s'.inoutNames
    exact hTailRes.trans hPresY

private theorem pushAssignTargets_preserves_inoutNames_ofIH
    (targets : List (AstNode Variable)) (s : PushOldState)
    (hPres : ∀ tgt fn vs, (⟨.Field tgt fn, vs⟩ : AstNode Variable) ∈ targets →
              ∀ (s' : PushOldState),
              ((pushOldInwardExpr tgt).run s').snd.inoutNames = s'.inoutNames) :
    (pushAssignTargets targets s).snd.inoutNames = s.inoutNames := by
  rw [pushAssignTargets_eq_unattached]
  exact listMapM_pushAssignTargetsAux_preserves_inoutNames_of targets hPres s

/-- `pushOldInwardExpr` preserves `inoutNames`. -/
theorem pushOldInwardExpr_preserves_inoutNames
    (s : PushOldState) (e : StmtExprMd) :
    ((pushOldInwardExpr e).run s).snd.inoutNames = s.inoutNames := by
  induction h_sz : sizeOf e using Nat.strongRecOn generalizing e s with
  | ind n ih =>
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    cases hVal : e.val with
    | LiteralInt v =>
      have he : e = ⟨.LiteralInt v, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_literalInt_preserves s v e.source
    | LiteralBool v =>
      have he : e = ⟨.LiteralBool v, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_literalBool_preserves s v e.source
    | LiteralString str =>
      have he : e = ⟨.LiteralString str, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_literalString_preserves s str e.source
    | LiteralDecimal d =>
      have he : e = ⟨.LiteralDecimal d, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_literalDecimal_preserves s d e.source
    | New ref =>
      have he : e = ⟨.New ref, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_new_preserves s ref e.source
    | This =>
      have he : e = ⟨.This, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_this_preserves s e.source
    | Abstract =>
      have he : e = ⟨.Abstract, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_abstract_preserves s e.source
    | All =>
      have he : e = ⟨.All, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_all_preserves s e.source
    | Exit lbl =>
      have he : e = ⟨.Exit lbl, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_exit_preserves s lbl e.source
    | Hole det ty =>
      have he : e = ⟨.Hole det ty, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_hole_preserves s det ty e.source
    | Var v =>
      cases v with
      | Local nm =>
        have he : e = ⟨.Var (.Local nm), e.source⟩ := by cases e; simp_all
        rw [he]; exact pushOldInwardExpr_varLocal_preserves s nm e.source
      | Declare p =>
        have he : e = ⟨.Var (.Declare p), e.source⟩ := by cases e; simp_all
        rw [he]; exact pushOldInwardExpr_varDeclare_preserves s p e.source
      | Field target fn =>
        have he : e = ⟨.Var (.Field target fn), e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_varField_preserves]
        have hSpec := StmtExpr.Var.sizeOf_spec (Variable.Field target fn)
        have hSpecVar := Variable.Field.sizeOf_spec target fn
        rw [hVal] at hValLt
        exact ih (sizeOf target) (by omega) s target rfl
    | Old inner =>
      have he : e = ⟨.Old inner, e.source⟩ := by cases e; simp_all
      rw [he]; exact pushOldInwardExpr_old_preserves s inner e.source
    | Assigned m =>
      have he : e = ⟨.Assigned m, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_assigned_preserves]
      have hSpec := StmtExpr.Assigned.sizeOf_spec m
      rw [hVal] at hValLt
      exact ih (sizeOf m) (by omega) s m rfl
    | Fresh v =>
      have he : e = ⟨.Fresh v, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_fresh_preserves]
      have hSpec := StmtExpr.Fresh.sizeOf_spec v
      rw [hVal] at hValLt
      exact ih (sizeOf v) (by omega) s v rfl
    | AsType target ty =>
      have he : e = ⟨.AsType target ty, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_asType_preserves]
      have hSpec := StmtExpr.AsType.sizeOf_spec target ty
      rw [hVal] at hValLt
      exact ih (sizeOf target) (by omega) s target rfl
    | IsType target ty =>
      have he : e = ⟨.IsType target ty, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_isType_preserves]
      have hSpec := StmtExpr.IsType.sizeOf_spec target ty
      rw [hVal] at hValLt
      exact ih (sizeOf target) (by omega) s target rfl
    | Assume cond =>
      have he : e = ⟨.Assume cond, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_assume_preserves]
      have hSpec := StmtExpr.Assume.sizeOf_spec cond
      rw [hVal] at hValLt
      exact ih (sizeOf cond) (by omega) s cond rfl
    | ContractOf ty fn =>
      have he : e = ⟨.ContractOf ty fn, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_contractOf_preserves]
      have hSpec := StmtExpr.ContractOf.sizeOf_spec ty fn
      rw [hVal] at hValLt
      exact ih (sizeOf fn) (by omega) s fn rfl
    | Assert c =>
      have he : e = ⟨.Assert c, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_assert_preserves]
      have hSpec := StmtExpr.Assert.sizeOf_spec c
      have hCondSpec := Condition.sizeOf_condition_lt c
      rw [hVal] at hValLt
      exact ih (sizeOf c.condition) (by omega) s c.condition rfl
    | Return v =>
      cases v with
      | none =>
        have he : e = ⟨.Return none, e.source⟩ := by cases e; simp_all
        rw [he]; exact pushOldInwardExpr_return_none_preserves s e.source
      | some r =>
        have he : e = ⟨.Return (some r), e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_return_some_preserves]
        have hSpec := StmtExpr.Return.sizeOf_spec (some r)
        have hOptSpec : sizeOf (some r) = 1 + sizeOf r := rfl
        rw [hVal] at hValLt
        exact ih (sizeOf r) (by omega) s r rfl
    | ReferenceEquals lhs rhs =>
      have he : e = ⟨.ReferenceEquals lhs rhs, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_referenceEquals_preserves]
      have hSpec := StmtExpr.ReferenceEquals.sizeOf_spec lhs rhs
      rw [hVal] at hValLt
      have hLSz : sizeOf lhs < n := by omega
      have hRSz : sizeOf rhs < n := by omega
      exact (ih (sizeOf rhs) hRSz _ rhs rfl).trans (ih (sizeOf lhs) hLSz s lhs rfl)
    | PureFieldUpdate t fn nv =>
      have he : e = ⟨.PureFieldUpdate t fn nv, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_pureFieldUpdate_preserves]
      have hSpec := StmtExpr.PureFieldUpdate.sizeOf_spec t fn nv
      rw [hVal] at hValLt
      have hTSz : sizeOf t < n := by omega
      have hNSz : sizeOf nv < n := by omega
      exact (ih (sizeOf nv) hNSz _ nv rfl).trans (ih (sizeOf t) hTSz s t rfl)
    | ProveBy v p =>
      have he : e = ⟨.ProveBy v p, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_proveBy_preserves]
      have hSpec := StmtExpr.ProveBy.sizeOf_spec v p
      rw [hVal] at hValLt
      have hVSz : sizeOf v < n := by omega
      have hPSz : sizeOf p < n := by omega
      exact (ih (sizeOf p) hPSz _ p rfl).trans (ih (sizeOf v) hVSz s v rfl)
    | IfThenElse cond th el =>
      cases el with
      | none =>
        have he : e = ⟨.IfThenElse cond th none, e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_ifThenElse_none_preserves]
        have hSpec := StmtExpr.IfThenElse.sizeOf_spec cond th none
        rw [hVal] at hValLt
        have hCSz : sizeOf cond < n := by omega
        have hTSz : sizeOf th < n := by omega
        exact (ih (sizeOf th) hTSz _ th rfl).trans (ih (sizeOf cond) hCSz s cond rfl)
      | some elE =>
        have he : e = ⟨.IfThenElse cond th (some elE), e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_ifThenElse_some_preserves]
        have hSpec := StmtExpr.IfThenElse.sizeOf_spec cond th (some elE)
        have hOptSpec : sizeOf (some elE) = 1 + sizeOf elE := rfl
        rw [hVal] at hValLt
        have hCSz : sizeOf cond < n := by omega
        have hTSz : sizeOf th < n := by omega
        have hESz : sizeOf elE < n := by omega
        exact ((ih (sizeOf elE) hESz _ elE rfl).trans
                (ih (sizeOf th) hTSz _ th rfl)).trans
                (ih (sizeOf cond) hCSz s cond rfl)
    | Quantifier mode param trigger body =>
      cases trigger with
      | none =>
        have he : e = ⟨.Quantifier mode param none body, e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_quantifier_none_preserves]
        have hSpec := StmtExpr.Quantifier.sizeOf_spec mode param none body
        rw [hVal] at hValLt
        exact ih (sizeOf body) (by omega) s body rfl
      | some tr =>
        have he : e = ⟨.Quantifier mode param (some tr) body, e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_quantifier_some_preserves]
        have hSpec := StmtExpr.Quantifier.sizeOf_spec mode param (some tr) body
        have hOptSpec : sizeOf (some tr) = 1 + sizeOf tr := rfl
        rw [hVal] at hValLt
        have hTSz : sizeOf tr < n := by omega
        have hBSz : sizeOf body < n := by omega
        exact (ih (sizeOf body) hBSz _ body rfl).trans (ih (sizeOf tr) hTSz s tr rfl)
    | Block stmts label =>
      have he : e = ⟨.Block stmts label, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_block_preserves]
      have hSpec := StmtExpr.Block.sizeOf_spec stmts label
      rw [hVal] at hValLt
      apply listMapM_pushOldInwardExpr_preserves
      intro x hx s'
      have hxLt : sizeOf x < sizeOf stmts := List.sizeOf_lt_of_mem hx
      exact ih (sizeOf x) (by omega) s' x rfl
    | StaticCall callee args =>
      have he : e = ⟨.StaticCall callee args, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_staticCall_preserves]
      have hSpec := StmtExpr.StaticCall.sizeOf_spec callee args
      rw [hVal] at hValLt
      apply listMapM_pushOldInwardExpr_preserves
      intro x hx s'
      have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
      exact ih (sizeOf x) (by omega) s' x rfl
    | PrimitiveOp op args =>
      have he : e = ⟨.PrimitiveOp op args, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_primitiveOp_preserves]
      have hSpec := StmtExpr.PrimitiveOp.sizeOf_spec op args
      rw [hVal] at hValLt
      apply listMapM_pushOldInwardExpr_preserves
      intro x hx s'
      have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
      exact ih (sizeOf x) (by omega) s' x rfl
    | InstanceCall t callee args =>
      have he : e = ⟨.InstanceCall t callee args, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_instanceCall_preserves]
      have hSpec := StmtExpr.InstanceCall.sizeOf_spec t callee args
      rw [hVal] at hValLt
      have hTSz : sizeOf t < n := by omega
      have hPresArgs : ((args.mapM pushOldInwardExpr) ((pushOldInwardExpr t).run s).snd).snd.inoutNames
                       = ((pushOldInwardExpr t).run s).snd.inoutNames := by
        apply listMapM_pushOldInwardExpr_preserves
        intro x hx s'
        have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
        exact ih (sizeOf x) (by omega) s' x rfl
      exact hPresArgs.trans (ih (sizeOf t) hTSz s t rfl)
    | While cond invs dec body =>
      cases dec with
      | none =>
        have he : e = ⟨.While cond invs none body, e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_while_none_preserves]
        have hSpec := StmtExpr.While.sizeOf_spec cond invs none body
        rw [hVal] at hValLt
        have hCSz : sizeOf cond < n := by omega
        have hBSz : sizeOf body < n := by omega
        have hPresInvs : ((invs.mapM pushOldInwardExpr) ((pushOldInwardExpr cond).run s).snd).snd.inoutNames
                         = ((pushOldInwardExpr cond).run s).snd.inoutNames := by
          apply listMapM_pushOldInwardExpr_preserves
          intro x hx s'
          have hxLt : sizeOf x < sizeOf invs := List.sizeOf_lt_of_mem hx
          exact ih (sizeOf x) (by omega) s' x rfl
        exact ((ih (sizeOf body) hBSz _ body rfl).trans hPresInvs).trans
              (ih (sizeOf cond) hCSz s cond rfl)
      | some d =>
        have he : e = ⟨.While cond invs (some d) body, e.source⟩ := by cases e; simp_all
        rw [he, pushOldInwardExpr_while_some_preserves]
        have hSpec := StmtExpr.While.sizeOf_spec cond invs (some d) body
        have hOptSpec : sizeOf (some d) = 1 + sizeOf d := rfl
        rw [hVal] at hValLt
        have hCSz : sizeOf cond < n := by omega
        have hDSz : sizeOf d < n := by omega
        have hBSz : sizeOf body < n := by omega
        have hPresInvs : ((invs.mapM pushOldInwardExpr) ((pushOldInwardExpr cond).run s).snd).snd.inoutNames
                         = ((pushOldInwardExpr cond).run s).snd.inoutNames := by
          apply listMapM_pushOldInwardExpr_preserves
          intro x hx s'
          have hxLt : sizeOf x < sizeOf invs := List.sizeOf_lt_of_mem hx
          exact ih (sizeOf x) (by omega) s' x rfl
        exact (((ih (sizeOf body) hBSz _ body rfl).trans (ih (sizeOf d) hDSz _ d rfl)).trans
                hPresInvs).trans (ih (sizeOf cond) hCSz s cond rfl)
    | Assign targets value =>
      have he : e = ⟨.Assign targets value, e.source⟩ := by cases e; simp_all
      rw [he, pushOldInwardExpr_assign_run_eq]
      have hSpec : sizeOf (StmtExpr.Assign targets value) = 1 + sizeOf targets + sizeOf value :=
        StmtExpr.Assign.sizeOf_spec targets value
      rw [hVal] at hValLt
      have hVSz : sizeOf value < n := by omega
      simp only [Prod.fst, Prod.snd]
      have ihV := ih (sizeOf value) hVSz (pushAssignTargets targets s).snd value rfl
      have hPresT : (pushAssignTargets targets s).snd.inoutNames = s.inoutNames := by
        apply pushAssignTargets_preserves_inoutNames_ofIH
        intro tgt fn vs hMem s'
        have hxLt : sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable) < sizeOf targets :=
          List.sizeOf_lt_of_mem hMem
        have hTgtLt : sizeOf tgt < sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable) := by
          have h1 := AstNode.sizeOf_val_lt (⟨.Field tgt fn, vs⟩ : AstNode Variable)
          have h2 := Variable.Field.sizeOf_spec tgt fn
          show sizeOf tgt < sizeOf (⟨.Field tgt fn, vs⟩ : AstNode Variable)
          simp only at h1
          omega
        have hTgtSz : sizeOf tgt < n := by omega
        exact ih (sizeOf tgt) hTgtSz s' tgt rfl
      exact ihV.trans hPresT

/-- Reduction for `.ReferenceEquals lhs rhs`. -/
private theorem pushOldInwardExpr_referenceEquals_run
    (s : PushOldState) (lhs rhs : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ReferenceEquals lhs rhs, src⟩).run s).fst =
    ⟨.ReferenceEquals
      ((pushOldInwardExpr lhs).run s).fst
      ((pushOldInwardExpr rhs).run ((pushOldInwardExpr lhs).run s).snd).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ReferenceEquals lhs rhs, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hL : (mapStmtExprPrePostM visitOld pure lhs) s = resL
  obtain ⟨lhs', sL⟩ := resL
  generalize hR : (mapStmtExprPrePostM visitOld pure rhs sL) = resR
  obtain ⟨rhs', sR⟩ := resR
  rfl

/-- Subgoal-4 canonical for `.ReferenceEquals`. -/
private theorem pushOldInwardExpr_canonical_referenceEquals
    (s : PushOldState) (lhs rhs : StmtExprMd) (src : Option FileRange)
    (ihL : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr lhs).run s).fst)
    (ihR : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr rhs).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.ReferenceEquals lhs rhs, src⟩).run s).fst := by
  rw [pushOldInwardExpr_referenceEquals_run]
  intro subOld hSub
  rw [subOlds_referenceEquals] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h => exact ihL subOld h
  | inr h =>
    have hPresL := pushOldInwardExpr_preserves_inoutNames s lhs
    exact ihR _ hPresL subOld h

/-- Reduction for `.PureFieldUpdate t fn nv`. -/
private theorem pushOldInwardExpr_pureFieldUpdate_run
    (s : PushOldState) (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.PureFieldUpdate t fn nv, src⟩).run s).fst =
    ⟨.PureFieldUpdate
      ((pushOldInwardExpr t).run s).fst fn
      ((pushOldInwardExpr nv).run ((pushOldInwardExpr t).run s).snd).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.PureFieldUpdate t fn nv, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hT : (mapStmtExprPrePostM visitOld pure t) s = resT
  obtain ⟨t', sT⟩ := resT
  generalize hN : (mapStmtExprPrePostM visitOld pure nv sT) = resN
  obtain ⟨nv', sN⟩ := resN
  rfl

private theorem pushOldInwardExpr_canonical_pureFieldUpdate
    (s : PushOldState) (t : StmtExprMd) (fn : Identifier) (nv : StmtExprMd) (src : Option FileRange)
    (ihT : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr t).run s).fst)
    (ihNv : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr nv).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.PureFieldUpdate t fn nv, src⟩).run s).fst := by
  rw [pushOldInwardExpr_pureFieldUpdate_run]
  intro subOld hSub
  rw [subOlds_pureFieldUpdate] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h => exact ihT subOld h
  | inr h =>
    have hPresT := pushOldInwardExpr_preserves_inoutNames s t
    exact ihNv _ hPresT subOld h

/-- Reduction for `.ProveBy v p`. -/
private theorem pushOldInwardExpr_proveBy_run
    (s : PushOldState) (v p : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.ProveBy v p, src⟩).run s).fst =
    ⟨.ProveBy
      ((pushOldInwardExpr v).run s).fst
      ((pushOldInwardExpr p).run ((pushOldInwardExpr v).run s).snd).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.ProveBy v p, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  generalize hV : (mapStmtExprPrePostM visitOld pure v) s = resV
  obtain ⟨v', sV⟩ := resV
  generalize hP : (mapStmtExprPrePostM visitOld pure p sV) = resP
  obtain ⟨p', sP⟩ := resP
  rfl

private theorem pushOldInwardExpr_canonical_proveBy
    (s : PushOldState) (v p : StmtExprMd) (src : Option FileRange)
    (ihV : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr v).run s).fst)
    (ihP : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr p).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.ProveBy v p, src⟩).run s).fst := by
  rw [pushOldInwardExpr_proveBy_run]
  intro subOld hSub
  rw [subOlds_proveBy] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h => exact ihV subOld h
  | inr h =>
    have hPresV := pushOldInwardExpr_preserves_inoutNames s v
    exact ihP _ hPresV subOld h

/-- Reduction for `.IfThenElse cond th none`. -/
private theorem pushOldInwardExpr_ifThenElse_none_run
    (s : PushOldState) (cond th : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IfThenElse cond th none, src⟩).run s).fst =
    ⟨.IfThenElse
      ((pushOldInwardExpr cond).run s).fst
      ((pushOldInwardExpr th).run ((pushOldInwardExpr cond).run s).snd).fst
      none, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IfThenElse cond th none, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  generalize hT : (mapStmtExprPrePostM visitOld pure th sC) = resT
  obtain ⟨th', sT⟩ := resT
  rfl

private theorem pushOldInwardExpr_canonical_ifThenElse_none
    (s : PushOldState) (cond th : StmtExprMd) (src : Option FileRange)
    (ihC : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr cond).run s).fst)
    (ihT : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr th).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.IfThenElse cond th none, src⟩).run s).fst := by
  rw [pushOldInwardExpr_ifThenElse_none_run]
  intro subOld hSub
  rw [subOlds_ifThenElse_none] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h => exact ihC subOld h
  | inr h =>
    have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
    exact ihT _ hPresC subOld h

/-- Reduction for `.IfThenElse cond th (some elE)`. -/
private theorem pushOldInwardExpr_ifThenElse_some_run
    (s : PushOldState) (cond th elE : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.IfThenElse cond th (some elE), src⟩).run s).fst =
    ⟨.IfThenElse
      ((pushOldInwardExpr cond).run s).fst
      ((pushOldInwardExpr th).run ((pushOldInwardExpr cond).run s).snd).fst
      (some ((pushOldInwardExpr elE).run
              ((pushOldInwardExpr th).run ((pushOldInwardExpr cond).run s).snd).snd).fst), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.IfThenElse cond th (some elE), src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  generalize hT : (mapStmtExprPrePostM visitOld pure th sC) = resT
  obtain ⟨th', sT⟩ := resT
  generalize hE : (mapStmtExprPrePostM visitOld pure elE sT) = resE
  obtain ⟨elE', sE⟩ := resE
  rfl

private theorem pushOldInwardExpr_canonical_ifThenElse_some
    (s : PushOldState) (cond th elE : StmtExprMd) (src : Option FileRange)
    (ihC : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr cond).run s).fst)
    (ihT : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr th).run s').fst)
    (ihE : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr elE).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.IfThenElse cond th (some elE), src⟩).run s).fst := by
  rw [pushOldInwardExpr_ifThenElse_some_run]
  intro subOld hSub
  rw [subOlds_ifThenElse_some] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h =>
    rw [List.mem_append] at h
    cases h with
    | inl hC => exact ihC subOld hC
    | inr hT =>
      have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
      exact ihT _ hPresC subOld hT
  | inr hE =>
    have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
    have hPresT := pushOldInwardExpr_preserves_inoutNames
                    ((pushOldInwardExpr cond).run s).snd th
    exact ihE _ (hPresT.trans hPresC) subOld hE

/-- Reduction for `.Quantifier mode param none body`. -/
private theorem pushOldInwardExpr_quantifier_none_run
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Quantifier mode param none body, src⟩).run s).fst =
    ⟨.Quantifier mode param none ((pushOldInwardExpr body).run s).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Quantifier mode param none body, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hB : (mapStmtExprPrePostM visitOld pure body) s = resB
  obtain ⟨body', sB⟩ := resB
  rfl

private theorem pushOldInwardExpr_canonical_quantifier_none
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (body : StmtExprMd) (src : Option FileRange)
    (ih : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr body).run s).fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Quantifier mode param none body, src⟩).run s).fst := by
  rw [pushOldInwardExpr_quantifier_none_run]
  intro subOld hSub
  rw [subOlds_quantifier_no_trigger] at hSub
  exact ih subOld hSub

/-- Reduction for `.Quantifier mode param (some tr) body`. -/
private theorem pushOldInwardExpr_quantifier_some_run
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (tr body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Quantifier mode param (some tr) body, src⟩).run s).fst =
    ⟨.Quantifier mode param
      (some ((pushOldInwardExpr tr).run s).fst)
      ((pushOldInwardExpr body).run ((pushOldInwardExpr tr).run s).snd).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Quantifier mode param (some tr) body, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  unfold visitOld
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  generalize hT : (mapStmtExprPrePostM visitOld pure tr) s = resT
  obtain ⟨tr', sT⟩ := resT
  generalize hB : (mapStmtExprPrePostM visitOld pure body sT) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

private theorem pushOldInwardExpr_canonical_quantifier_some
    (s : PushOldState) (mode : QuantifierMode) (param : Parameter) (tr body : StmtExprMd) (src : Option FileRange)
    (ihT : AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr tr).run s).fst)
    (ihB : ∀ (s' : PushOldState), s'.inoutNames = s.inoutNames →
            AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr body).run s').fst) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Quantifier mode param (some tr) body, src⟩).run s).fst := by
  rw [pushOldInwardExpr_quantifier_some_run]
  intro subOld hSub
  rw [subOlds_quantifier_some] at hSub
  rw [List.mem_append] at hSub
  cases hSub with
  | inl h => exact ihT subOld h
  | inr h =>
    have hPresT := pushOldInwardExpr_preserves_inoutNames s tr
    exact ihB _ hPresT subOld h

/-- Each output of `xs.mapM pushOldInwardExpr` is canonical w.r.t. `target`,
    given that each input element is canonical from any starting state with
    `inoutNames = target`. -/
private theorem listMapM_pushOldInwardExpr_canonical
    (xs : List StmtExprMd) (s : PushOldState)
    (target : List String)
    (hSame : s.inoutNames = target)
    (hAll : ∀ x ∈ xs, ∀ (s' : PushOldState),
              s'.inoutNames = target →
              AllSubOldsCanonical target ((pushOldInwardExpr x).run s').fst) :
    ∀ y ∈ ((xs.mapM pushOldInwardExpr).run s).fst,
      AllSubOldsCanonical target y := by
  induction xs generalizing s with
  | nil =>
    intro y hy
    simp [List.mapM_nil, StateT.run, StateT.pure, pure] at hy
  | cons x xs ih =>
    intro y hy
    rw [List.mapM_cons] at hy
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hy
    generalize hM : (pushOldInwardExpr x) s = resX at hy
    obtain ⟨x', sX⟩ := resX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hy
    generalize hRest : xs.mapM pushOldInwardExpr sX = resRest at hy
    obtain ⟨ys', sRest⟩ := resRest
    simp at hy
    have hPresX := pushOldInwardExpr_preserves_inoutNames s x
    have hSXsnd : ((pushOldInwardExpr x).run s).snd = sX := by
      show (pushOldInwardExpr x s).snd = sX
      rw [hM]
    rw [hSXsnd] at hPresX
    have hSXTarget : sX.inoutNames = target := hPresX.trans hSame
    cases hy with
    | inl h =>
      have hCanX := hAll x List.mem_cons_self s hSame
      have hSXfst : ((pushOldInwardExpr x).run s).fst = x' := by
        show (pushOldInwardExpr x s).fst = x'
        rw [hM]
      rw [hSXfst] at hCanX
      rw [h]
      exact hCanX
    | inr h =>
      have hAll' : ∀ y ∈ xs, ∀ (s' : PushOldState),
            s'.inoutNames = target →
            AllSubOldsCanonical target ((pushOldInwardExpr y).run s').fst :=
        fun y hy s' hh => hAll y (List.mem_cons_of_mem _ hy) s' hh
      have ih' := ih sX hSXTarget hAll'
      have hRestEq : ((xs.mapM pushOldInwardExpr).run sX).fst = ys' := by
        show (xs.mapM pushOldInwardExpr sX).fst = ys'
        rw [hRest]
      apply ih' y
      rw [hRestEq]
      exact h

/-- `xs.attach.mapM (fun ⟨e, _⟩ => mapStmtExprPrePostM visitOld StateT.pure e) = xs.mapM pushOldInwardExpr`. -/
private theorem pushOldInwardExpr_attach_mapM_eq' (xs : List StmtExprMd) :
    (xs.attach.mapM fun (e : { e // e ∈ xs }) => mapStmtExprPrePostM visitOld StateT.pure e.val)
      = xs.mapM pushOldInwardExpr := by
  rw [List.mapM_subtype (g := pushOldInwardExpr) (by intros; rfl)]
  rw [List.unattach_attach]

/-- Reduction for `.Block stmts label`. -/
private theorem pushOldInwardExpr_block_run
    (s : PushOldState) (stmts : List StmtExprMd) (label : Option String) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.Block stmts label, src⟩).run s).fst =
    ⟨.Block ((stmts.mapM pushOldInwardExpr s).fst) label, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.Block stmts label, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.Block stmts label, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hM : (stmts.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_block
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (stmts : List StmtExprMd) (label : Option String) (src : Option FileRange)
    (hSize : sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.Block stmts label, src⟩).run s).fst := by
  rw [pushOldInwardExpr_block_run]
  intro subOld hSub
  rw [subOlds_block] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := hSub
  have hCanList : ∀ y' ∈ ((stmts.mapM pushOldInwardExpr).run s).fst,
        AllSubOldsCanonical s.inoutNames y' := by
    apply listMapM_pushOldInwardExpr_canonical stmts s s.inoutNames rfl
    intro x hx s' hh
    have hxLt : sizeOf x < sizeOf stmts := List.sizeOf_lt_of_mem hx
    have hSpec := StmtExpr.Block.sizeOf_spec stmts label
    have hValLt : sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd).val
                  < sizeOf (⟨.Block stmts label, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    have hValEq : (⟨.Block stmts label, src⟩ : StmtExprMd).val = .Block stmts label := rfl
    rw [hValEq] at hValLt
    have hxSize : sizeOf x < n := by omega
    have ih' := ih (sizeOf x) hxSize s' x rfl
    rw [hh] at ih'
    exact ih'
  rw [← hYsEq] at hSubInY
  apply hCanList y _ subOld hSubInY
  show y ∈ (stmts.mapM pushOldInwardExpr s).fst
  exact hy

/-- Reduction for `.StaticCall callee args`. -/
private theorem pushOldInwardExpr_staticCall_run
    (s : PushOldState) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.StaticCall callee args, src⟩).run s).fst =
    ⟨.StaticCall callee ((args.mapM pushOldInwardExpr s).fst), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.StaticCall callee args, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.StaticCall callee args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hM : (args.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_staticCall
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.StaticCall callee args, src⟩).run s).fst := by
  rw [pushOldInwardExpr_staticCall_run]
  intro subOld hSub
  rw [subOlds_staticCall] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := hSub
  have hCanList : ∀ y' ∈ ((args.mapM pushOldInwardExpr).run s).fst,
        AllSubOldsCanonical s.inoutNames y' := by
    apply listMapM_pushOldInwardExpr_canonical args s s.inoutNames rfl
    intro x hx s' hh
    have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
    have hSpec := StmtExpr.StaticCall.sizeOf_spec callee args
    have hValLt : sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd).val
                  < sizeOf (⟨.StaticCall callee args, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    have hValEq : (⟨.StaticCall callee args, src⟩ : StmtExprMd).val = .StaticCall callee args := rfl
    rw [hValEq] at hValLt
    have hxSize : sizeOf x < n := by omega
    have ih' := ih (sizeOf x) hxSize s' x rfl
    rw [hh] at ih'
    exact ih'
  rw [← hYsEq] at hSubInY
  apply hCanList y _ subOld hSubInY
  show y ∈ (args.mapM pushOldInwardExpr s).fst
  exact hy

/-- Reduction for `.PrimitiveOp op args`. -/
private theorem pushOldInwardExpr_primitiveOp_run
    (s : PushOldState) (op : Operation) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.PrimitiveOp op args, src⟩).run s).fst =
    ⟨.PrimitiveOp op ((args.mapM pushOldInwardExpr s).fst), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.PrimitiveOp op args, src⟩).run s).fst = _
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.PrimitiveOp op args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hM : (args.mapM pushOldInwardExpr) s = res
  obtain ⟨ys, sR⟩ := res
  rfl

private theorem pushOldInwardExpr_canonical_primitiveOp
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (op : Operation) (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.PrimitiveOp op args, src⟩).run s).fst := by
  rw [pushOldInwardExpr_primitiveOp_run]
  intro subOld hSub
  rw [subOlds_primitiveOp] at hSub
  simp only [List.mem_flatten, List.mem_map] at hSub
  obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := hSub
  have hCanList : ∀ y' ∈ ((args.mapM pushOldInwardExpr).run s).fst,
        AllSubOldsCanonical s.inoutNames y' := by
    apply listMapM_pushOldInwardExpr_canonical args s s.inoutNames rfl
    intro x hx s' hh
    have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
    have hSpec := StmtExpr.PrimitiveOp.sizeOf_spec op args
    have hValLt : sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd).val
                  < sizeOf (⟨.PrimitiveOp op args, src⟩ : StmtExprMd) :=
      AstNode.sizeOf_val_lt _
    have hValEq : (⟨.PrimitiveOp op args, src⟩ : StmtExprMd).val = .PrimitiveOp op args := rfl
    rw [hValEq] at hValLt
    have hxSize : sizeOf x < n := by omega
    have ih' := ih (sizeOf x) hxSize s' x rfl
    rw [hh] at ih'
    exact ih'
  rw [← hYsEq] at hSubInY
  apply hCanList y _ subOld hSubInY
  show y ∈ (args.mapM pushOldInwardExpr s).fst
  exact hy

/-- Reduction for `.While cond invs none body`. -/
private theorem pushOldInwardExpr_while_none_run
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.While cond invs none body, src⟩).run s).fst =
    ⟨.While
      ((pushOldInwardExpr cond).run s).fst
      ((invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).fst)
      none
      ((pushOldInwardExpr body).run
        ((invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).snd)).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.While cond invs none body, src⟩).run s).fst =
       ⟨.While ((mapStmtExprPrePostM visitOld pure cond).run s).fst
         ((invs.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure cond).run s).snd).fst)
         none
         ((mapStmtExprPrePostM visitOld pure body).run
           ((invs.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd)).fst, src⟩
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.While cond invs none body, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  simp only [Prod.fst, Prod.snd]
  generalize hI : (invs.mapM pushOldInwardExpr sC) = resI
  obtain ⟨invs', sI⟩ := resI
  simp only [Prod.fst, Prod.snd]
  generalize hB : (mapStmtExprPrePostM visitOld pure body sI) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

/-- subOlds of `.While cond invs none body`. -/
private theorem subOlds_while_none' (cond : StmtExprMd) (invs : List StmtExprMd) (body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.While cond invs none body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++
    (invs.attach.map fun ⟨i, _⟩ => StmtExprMd.subOlds i).flatten ++
    StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]
  simp

private theorem pushOldInwardExpr_canonical_while_none
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (body : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.While cond invs none body, src⟩).run s).fst := by
  rw [pushOldInwardExpr_while_none_run]
  intro subOld hSub
  rw [subOlds_while_none'] at hSub
  rw [List.mem_append, List.mem_append] at hSub
  have hSpec := StmtExpr.While.sizeOf_spec cond invs none body
  have hValLt : sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd).val
                < sizeOf (⟨.While cond invs none body, src⟩ : StmtExprMd) :=
    AstNode.sizeOf_val_lt _
  have hValEq : (⟨.While cond invs none body, src⟩ : StmtExprMd).val = .While cond invs none body := rfl
  rw [hValEq] at hValLt
  have hCSz : sizeOf cond < n := by omega
  have hBSz : sizeOf body < n := by omega
  cases hSub with
  | inl h =>
    cases h with
    | inl hC => exact ih (sizeOf cond) hCSz s cond rfl subOld hC
    | inr hI =>
      simp only [List.mem_flatten, List.mem_map] at hI
      obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := hI
      have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
      have hCanInvs : ∀ y' ∈ ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).fst,
          AllSubOldsCanonical s.inoutNames y' := by
        apply listMapM_pushOldInwardExpr_canonical invs _ s.inoutNames hPresC
        intro x hx s' hh
        have hxLt : sizeOf x < sizeOf invs := List.sizeOf_lt_of_mem hx
        have hxSize : sizeOf x < n := by omega
        have ih' := ih (sizeOf x) hxSize s' x rfl
        rw [hh] at ih'; exact ih'
      rw [← hYsEq] at hSubInY
      apply hCanInvs y _ subOld hSubInY
      show y ∈ (invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).fst
      exact hy
  | inr hB =>
    have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
    have hPresI : ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd.inoutNames
                  = ((pushOldInwardExpr cond).run s).snd.inoutNames := by
      apply listMapM_pushOldInwardExpr_preserves_inoutNames_of
      intro x _ s'; exact pushOldInwardExpr_preserves_inoutNames s' x
    have ihB := ih (sizeOf body) hBSz
                  ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd body rfl
    rw [hPresI.trans hPresC] at ihB
    exact ihB subOld hB

/-- Reduction for `.While cond invs (some d) body`. -/
private theorem pushOldInwardExpr_while_some_run
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (d body : StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.While cond invs (some d) body, src⟩).run s).fst =
    ⟨.While
      ((pushOldInwardExpr cond).run s).fst
      ((invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).fst)
      (some ((pushOldInwardExpr d).run
              ((invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).snd)).fst)
      ((pushOldInwardExpr body).run
        ((pushOldInwardExpr d).run
          ((invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).snd)).snd).fst, src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.While cond invs (some d) body, src⟩).run s).fst =
       ⟨.While ((mapStmtExprPrePostM visitOld pure cond).run s).fst
         ((invs.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure cond).run s).snd).fst)
         (some ((mapStmtExprPrePostM visitOld pure d).run
                 ((invs.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd)).fst)
         ((mapStmtExprPrePostM visitOld pure body).run
           ((mapStmtExprPrePostM visitOld pure d).run
             ((invs.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure cond).run s).snd).snd)).snd).fst, src⟩
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.While cond invs (some d) body, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure,
             Option.attach, Option.attachWith, Option.mapM,
             Functor.map, StateT.map]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hC : (mapStmtExprPrePostM visitOld pure cond) s = resC
  obtain ⟨cond', sC⟩ := resC
  simp only [Prod.fst, Prod.snd]
  generalize hI : (invs.mapM pushOldInwardExpr sC) = resI
  obtain ⟨invs', sI⟩ := resI
  simp only [Prod.fst, Prod.snd]
  generalize hD : (mapStmtExprPrePostM visitOld pure d sI) = resD
  obtain ⟨d', sD⟩ := resD
  simp only [Prod.fst, Prod.snd]
  generalize hB : (mapStmtExprPrePostM visitOld pure body sD) = resB
  obtain ⟨body', sB⟩ := resB
  rfl

/-- subOlds of `.While cond invs (some d) body`. -/
private theorem subOlds_while_some' (cond : StmtExprMd) (invs : List StmtExprMd) (d body : StmtExprMd) (src : Option FileRange) :
    StmtExprMd.subOlds (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) =
    StmtExprMd.subOlds cond ++
    (invs.attach.map fun ⟨i, _⟩ => StmtExprMd.subOlds i).flatten ++
    StmtExprMd.subOlds d ++
    StmtExprMd.subOlds body := by
  rw [StmtExprMd.subOlds]

private theorem pushOldInwardExpr_canonical_while_some
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (cond : StmtExprMd) (invs : List StmtExprMd) (d body : StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.While cond invs (some d) body, src⟩).run s).fst := by
  rw [pushOldInwardExpr_while_some_run]
  intro subOld hSub
  rw [subOlds_while_some'] at hSub
  rw [List.mem_append, List.mem_append, List.mem_append] at hSub
  have hSpec := StmtExpr.While.sizeOf_spec cond invs (some d) body
  have hOptSpec : sizeOf (some d) = 1 + sizeOf d := rfl
  have hValLt : sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val
                < sizeOf (⟨.While cond invs (some d) body, src⟩ : StmtExprMd) :=
    AstNode.sizeOf_val_lt _
  have hValEq : (⟨.While cond invs (some d) body, src⟩ : StmtExprMd).val = .While cond invs (some d) body := rfl
  rw [hValEq] at hValLt
  have hCSz : sizeOf cond < n := by omega
  have hDSz : sizeOf d < n := by omega
  have hBSz : sizeOf body < n := by omega
  cases hSub with
  | inl h =>
    cases h with
    | inl hLL =>
      cases hLL with
      | inl hC => exact ih (sizeOf cond) hCSz s cond rfl subOld hC
      | inr hI =>
        simp only [List.mem_flatten, List.mem_map] at hI
        obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := hI
        have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
        have hCanInvs : ∀ y' ∈ ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).fst,
            AllSubOldsCanonical s.inoutNames y' := by
          apply listMapM_pushOldInwardExpr_canonical invs _ s.inoutNames hPresC
          intro x hx s' hh
          have hxLt : sizeOf x < sizeOf invs := List.sizeOf_lt_of_mem hx
          have hxSize : sizeOf x < n := by omega
          have ih' := ih (sizeOf x) hxSize s' x rfl
          rw [hh] at ih'; exact ih'
        rw [← hYsEq] at hSubInY
        apply hCanInvs y _ subOld hSubInY
        show y ∈ (invs.mapM pushOldInwardExpr ((pushOldInwardExpr cond).run s).snd).fst
        exact hy
    | inr hD =>
      have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
      have hPresI : ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd.inoutNames
                    = ((pushOldInwardExpr cond).run s).snd.inoutNames := by
        apply listMapM_pushOldInwardExpr_preserves_inoutNames_of
        intro x _ s'; exact pushOldInwardExpr_preserves_inoutNames s' x
      have ihD := ih (sizeOf d) hDSz
                    ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd d rfl
      rw [hPresI.trans hPresC] at ihD
      exact ihD subOld hD
  | inr hB =>
    have hPresC := pushOldInwardExpr_preserves_inoutNames s cond
    have hPresI : ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd.inoutNames
                  = ((pushOldInwardExpr cond).run s).snd.inoutNames := by
      apply listMapM_pushOldInwardExpr_preserves_inoutNames_of
      intro x _ s'; exact pushOldInwardExpr_preserves_inoutNames s' x
    have hPresD := pushOldInwardExpr_preserves_inoutNames
                    ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd d
    have ihB := ih (sizeOf body) hBSz
                  ((pushOldInwardExpr d).run
                    ((invs.mapM pushOldInwardExpr).run ((pushOldInwardExpr cond).run s).snd).snd).snd body rfl
    rw [(hPresD.trans hPresI).trans hPresC] at ihB
    exact ihB subOld hB

/-- Reduction for `.InstanceCall t callee args`. -/
private theorem pushOldInwardExpr_instanceCall_run
    (s : PushOldState) (t : StmtExprMd) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange) :
    ((pushOldInwardExpr ⟨.InstanceCall t callee args, src⟩).run s).fst =
    ⟨.InstanceCall ((pushOldInwardExpr t).run s).fst callee
      ((args.mapM pushOldInwardExpr ((pushOldInwardExpr t).run s).snd).fst), src⟩ := by
  show ((mapStmtExprPrePostM visitOld pure ⟨.InstanceCall t callee args, src⟩).run s).fst =
       ⟨.InstanceCall ((mapStmtExprPrePostM visitOld pure t).run s).fst callee
         ((args.mapM pushOldInwardExpr ((mapStmtExprPrePostM visitOld pure t).run s).snd).fst), src⟩
  rw [mapStmtExprPrePostM]
  rw [show (visitOld ⟨.InstanceCall t callee args, src⟩) = (StateT.pure none : PushOldM _) from rfl]
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
  rw [pushOldInwardExpr_attach_mapM_eq']
  generalize hT : (mapStmtExprPrePostM visitOld pure t) s = resT
  obtain ⟨t', sT⟩ := resT
  simp only [Prod.fst]
  generalize hA : (args.mapM pushOldInwardExpr sT) = resA
  obtain ⟨ys, sR⟩ := resA
  rfl

private theorem pushOldInwardExpr_canonical_instanceCall
    {n : Nat}
    (ih : ∀ m : Nat, m < n →
          ∀ (s' : PushOldState) (e' : StmtExprMd),
          sizeOf e' = m →
          AllSubOldsCanonical s'.inoutNames ((pushOldInwardExpr e').run s').fst)
    (s : PushOldState) (t : StmtExprMd) (callee : Identifier) (args : List StmtExprMd) (src : Option FileRange)
    (hSize : sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) = n) :
    AllSubOldsCanonical s.inoutNames
      ((pushOldInwardExpr ⟨.InstanceCall t callee args, src⟩).run s).fst := by
  rw [pushOldInwardExpr_instanceCall_run]
  intro subOld hSub
  rw [subOlds_instanceCall] at hSub
  rw [List.mem_append] at hSub
  have hSpec := StmtExpr.InstanceCall.sizeOf_spec t callee args
  have hValLt : sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val
                < sizeOf (⟨.InstanceCall t callee args, src⟩ : StmtExprMd) :=
    AstNode.sizeOf_val_lt _
  have hValEq : (⟨.InstanceCall t callee args, src⟩ : StmtExprMd).val = .InstanceCall t callee args := rfl
  rw [hValEq] at hValLt
  have hTSz : sizeOf t < n := by omega
  cases hSub with
  | inl h => exact ih (sizeOf t) hTSz s t rfl subOld h
  | inr h =>
    simp only [List.mem_flatten, List.mem_map] at h
    obtain ⟨ys, ⟨⟨y, hy⟩, _, hYsEq⟩, hSubInY⟩ := h
    have hPresT := pushOldInwardExpr_preserves_inoutNames s t
    have hCanArgs : ∀ y' ∈ ((args.mapM pushOldInwardExpr).run ((pushOldInwardExpr t).run s).snd).fst,
          AllSubOldsCanonical s.inoutNames y' := by
      apply listMapM_pushOldInwardExpr_canonical args _ s.inoutNames hPresT
      intro x hx s' hh
      have hxLt : sizeOf x < sizeOf args := List.sizeOf_lt_of_mem hx
      have hxSize : sizeOf x < n := by omega
      have ih' := ih (sizeOf x) hxSize s' x rfl
      rw [hh] at ih'
      exact ih'
    rw [← hYsEq] at hSubInY
    apply hCanArgs y _ subOld hSubInY
    show y ∈ (args.mapM pushOldInwardExpr ((pushOldInwardExpr t).run s).snd).fst
    exact hy

theorem pushOldInwardExpr_canonical
    (s : PushOldState) (e : StmtExprMd) :
    AllSubOldsCanonical s.inoutNames ((pushOldInwardExpr e).run s).fst := by
  induction h_sz : sizeOf e using Nat.strongRecOn generalizing e s with
  | ind n ih =>
  cases hVal : e.val with
  | LiteralInt v =>
    have he : e = ⟨.LiteralInt v, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_literalInt s v e.source
  | LiteralBool v =>
    have he : e = ⟨.LiteralBool v, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_literalBool s v e.source
  | LiteralString str =>
    have he : e = ⟨.LiteralString str, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_literalString s str e.source
  | LiteralDecimal d =>
    have he : e = ⟨.LiteralDecimal d, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_literalDecimal s d e.source
  | New ref =>
    have he : e = ⟨.New ref, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_new s ref e.source
  | This =>
    have he : e = ⟨.This, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_this s e.source
  | Abstract =>
    have he : e = ⟨.Abstract, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_abstract s e.source
  | All =>
    have he : e = ⟨.All, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_all s e.source
  | Exit label =>
    have he : e = ⟨.Exit label, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_exit s label e.source
  | Hole det ty =>
    have he : e = ⟨.Hole det ty, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_hole s det ty e.source
  | Var v =>
    cases v with
    | Local nm =>
      have he : e = ⟨.Var (.Local nm), e.source⟩ := by cases e; simp_all
      rw [he]
      exact pushOldInwardExpr_canonical_varLocal s nm e.source
    | Declare p =>
      have he : e = ⟨.Var (.Declare p), e.source⟩ := by cases e; simp_all
      rw [he]
      exact pushOldInwardExpr_canonical_varDeclare s p e.source
    | Field target fn =>
      have he : e = ⟨.Var (.Field target fn), e.source⟩ := by cases e; simp_all
      rw [he]
      apply pushOldInwardExpr_canonical_varField s target fn e.source
      apply ih (sizeOf target) _ s target rfl
      have hVal_size : sizeOf e.val = 1 + (1 + sizeOf target + sizeOf fn) := by
        rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
  | Old inner =>
    have he : e = ⟨.Old inner, e.source⟩ := by cases e; simp_all
    rw [he]
    exact pushOldInwardExpr_canonical_old s inner e.source
  | Assigned m =>
    have he : e = ⟨.Assigned m, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_assigned s m e.source
    apply ih (sizeOf m) _ s m rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf m := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | Fresh v =>
    have he : e = ⟨.Fresh v, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_fresh s v e.source
    apply ih (sizeOf v) _ s v rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf v := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | AsType target ty =>
    have he : e = ⟨.AsType target ty, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_asType s target ty e.source
    apply ih (sizeOf target) _ s target rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | IsType target ty =>
    have he : e = ⟨.IsType target ty, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_isType s target ty e.source
    apply ih (sizeOf target) _ s target rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf target + sizeOf ty := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | Assume cond =>
    have he : e = ⟨.Assume cond, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_assume s cond e.source
    apply ih (sizeOf cond) _ s cond rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf cond := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | ContractOf ty fn =>
    have he : e = ⟨.ContractOf ty fn, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_contractOf s ty fn e.source
    apply ih (sizeOf fn) _ s fn rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf ty + sizeOf fn := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    omega
  | Assert c =>
    have he : e = ⟨.Assert c, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_assert s c e.source
    apply ih (sizeOf c.condition) _ s c.condition rfl
    have hVal_size : sizeOf e.val = 1 + sizeOf c := by rw [hVal]; rfl
    have := AstNode.sizeOf_val_lt e
    have := Condition.sizeOf_condition_lt c
    omega
  | Return v =>
    cases v with
    | none =>
      have he : e = ⟨.Return none, e.source⟩ := by cases e; simp_all
      rw [he]
      exact pushOldInwardExpr_canonical_return_none s e.source
    | some r =>
      have he : e = ⟨.Return (some r), e.source⟩ := by cases e; simp_all
      rw [he]
      apply pushOldInwardExpr_canonical_return_some s r e.source
      apply ih (sizeOf r) _ s r rfl
      have hVal_size : sizeOf e.val = 1 + (1 + sizeOf r) := by rw [hVal]; rfl
      have := AstNode.sizeOf_val_lt e
      omega
  | ReferenceEquals lhs rhs =>
    have he : e = ⟨.ReferenceEquals lhs rhs, e.source⟩ := by cases e; simp_all
    rw [he]
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    have hSpec := StmtExpr.ReferenceEquals.sizeOf_spec lhs rhs
    rw [hVal] at hValLt
    have hLSz : sizeOf lhs < n := by omega
    have hRSz : sizeOf rhs < n := by omega
    apply pushOldInwardExpr_canonical_referenceEquals s lhs rhs e.source
    · exact ih (sizeOf lhs) hLSz s lhs rfl
    · intro s' hSame
      have ihR := ih (sizeOf rhs) hRSz s' rhs rfl
      rw [hSame] at ihR
      exact ihR
  | PureFieldUpdate t fn nv =>
    have he : e = ⟨.PureFieldUpdate t fn nv, e.source⟩ := by cases e; simp_all
    rw [he]
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    have hSpec := StmtExpr.PureFieldUpdate.sizeOf_spec t fn nv
    rw [hVal] at hValLt
    have hTSz : sizeOf t < n := by omega
    have hNSz : sizeOf nv < n := by omega
    apply pushOldInwardExpr_canonical_pureFieldUpdate s t fn nv e.source
    · exact ih (sizeOf t) hTSz s t rfl
    · intro s' hSame
      have ihN := ih (sizeOf nv) hNSz s' nv rfl
      rw [hSame] at ihN
      exact ihN
  | ProveBy v p =>
    have he : e = ⟨.ProveBy v p, e.source⟩ := by cases e; simp_all
    rw [he]
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    have hSpec := StmtExpr.ProveBy.sizeOf_spec v p
    rw [hVal] at hValLt
    have hVSz : sizeOf v < n := by omega
    have hPSz : sizeOf p < n := by omega
    apply pushOldInwardExpr_canonical_proveBy s v p e.source
    · exact ih (sizeOf v) hVSz s v rfl
    · intro s' hSame
      have ihP := ih (sizeOf p) hPSz s' p rfl
      rw [hSame] at ihP
      exact ihP
  | IfThenElse cond th el =>
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    cases el with
    | none =>
      have he : e = ⟨.IfThenElse cond th none, e.source⟩ := by cases e; simp_all
      rw [he]
      have hSpec := StmtExpr.IfThenElse.sizeOf_spec cond th none
      rw [hVal] at hValLt
      have hCSz : sizeOf cond < n := by omega
      have hTSz : sizeOf th < n := by omega
      apply pushOldInwardExpr_canonical_ifThenElse_none s cond th e.source
      · exact ih (sizeOf cond) hCSz s cond rfl
      · intro s' hSame
        have ihT := ih (sizeOf th) hTSz s' th rfl
        rw [hSame] at ihT
        exact ihT
    | some elE =>
      have he : e = ⟨.IfThenElse cond th (some elE), e.source⟩ := by cases e; simp_all
      rw [he]
      have hSpec := StmtExpr.IfThenElse.sizeOf_spec cond th (some elE)
      have hOptSpec : sizeOf (some elE) = 1 + sizeOf elE := rfl
      rw [hVal] at hValLt
      have hCSz : sizeOf cond < n := by omega
      have hTSz : sizeOf th < n := by omega
      have hESz : sizeOf elE < n := by omega
      apply pushOldInwardExpr_canonical_ifThenElse_some s cond th elE e.source
      · exact ih (sizeOf cond) hCSz s cond rfl
      · intro s' hSame
        have ihT := ih (sizeOf th) hTSz s' th rfl
        rw [hSame] at ihT; exact ihT
      · intro s' hSame
        have ihE := ih (sizeOf elE) hESz s' elE rfl
        rw [hSame] at ihE; exact ihE
  | Quantifier mode param trigger body =>
    have hValLt : sizeOf e.val < sizeOf e := AstNode.sizeOf_val_lt e
    cases trigger with
    | none =>
      have he : e = ⟨.Quantifier mode param none body, e.source⟩ := by cases e; simp_all
      rw [he]
      have hSpec := StmtExpr.Quantifier.sizeOf_spec mode param none body
      rw [hVal] at hValLt
      have hBSz : sizeOf body < n := by omega
      apply pushOldInwardExpr_canonical_quantifier_none s mode param body e.source
      exact ih (sizeOf body) hBSz s body rfl
    | some tr =>
      have he : e = ⟨.Quantifier mode param (some tr) body, e.source⟩ := by cases e; simp_all
      rw [he]
      have hSpec := StmtExpr.Quantifier.sizeOf_spec mode param (some tr) body
      have hOptSpec : sizeOf (some tr) = 1 + sizeOf tr := rfl
      rw [hVal] at hValLt
      have hTSz : sizeOf tr < n := by omega
      have hBSz : sizeOf body < n := by omega
      apply pushOldInwardExpr_canonical_quantifier_some s mode param tr body e.source
      · exact ih (sizeOf tr) hTSz s tr rfl
      · intro s' hSame
        have ihB := ih (sizeOf body) hBSz s' body rfl
        rw [hSame] at ihB; exact ihB
  | Block stmts label =>
    have he : e = ⟨.Block stmts label, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_block ih s stmts label e.source
    rw [← he, h_sz]
  | StaticCall callee args =>
    have he : e = ⟨.StaticCall callee args, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_staticCall ih s callee args e.source
    rw [← he, h_sz]
  | PrimitiveOp op args =>
    have he : e = ⟨.PrimitiveOp op args, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_primitiveOp ih s op args e.source
    rw [← he, h_sz]
  | InstanceCall t callee args =>
    have he : e = ⟨.InstanceCall t callee args, e.source⟩ := by cases e; simp_all
    rw [he]
    apply pushOldInwardExpr_canonical_instanceCall ih s t callee args e.source
    rw [← he, h_sz]
  | While cond invs dec body =>
    cases dec with
    | none =>
      have he : e = ⟨.While cond invs none body, e.source⟩ := by cases e; simp_all
      rw [he]
      apply pushOldInwardExpr_canonical_while_none ih s cond invs body e.source
      rw [← he, h_sz]
    | some d =>
      have he : e = ⟨.While cond invs (some d) body, e.source⟩ := by cases e; simp_all
      rw [he]
      apply pushOldInwardExpr_canonical_while_some ih s cond invs d body e.source
      rw [← he, h_sz]
  | Assign targets value =>
    have he : e = ⟨.Assign targets value, e.source⟩ := by cases e; simp_all
    rw [he]
    have hValLt := AstNode.sizeOf_val_lt e
    rw [hVal] at hValLt
    have hSpec : sizeOf (StmtExpr.Assign targets value) = 1 + sizeOf targets + sizeOf value :=
      StmtExpr.Assign.sizeOf_spec targets value
    have hVSz : sizeOf value < n := by omega
    intro subOld hSub
    -- Generalize the entire result to bridge the inline-form mismatch.
    generalize hRun :
      ((pushOldInwardExpr ⟨.Assign targets value, e.source⟩).run s) = run0
    have hSub_named : subOld ∈ run0.fst.subOlds := by
      rw [← hRun]
      exact hSub
    obtain ⟨result, sRes⟩ := run0
    simp only [Prod.fst, Prod.snd] at hSub_named
    -- Extract the result's shape via injection on the explicit form.
    have hResShape :
        ∃ (ts' : List (AstNode Variable)) (val' : StmtExprMd) (sT : PushOldState),
          result = ⟨.Assign ts' val', e.source⟩ ∧
          sT.inoutNames = s.inoutNames ∧
          val' = ((pushOldInwardExpr value).run sT).fst := by
      refine ⟨(pushAssignTargets targets s).fst,
              ((pushOldInwardExpr value).run (pushAssignTargets targets s).snd).fst,
              (pushAssignTargets targets s).snd, ?_, ?_, ?_⟩
      · -- result = ⟨.Assign _ _, e.source⟩
        have hEq : ((pushOldInwardExpr ⟨.Assign targets value, e.source⟩).run s) =
                   ((⟨.Assign (pushAssignTargets targets s).fst
                         ((pushOldInwardExpr value).run
                           (pushAssignTargets targets s).snd).fst, e.source⟩ : StmtExprMd),
                    ((pushOldInwardExpr value).run
                      (pushAssignTargets targets s).snd).snd) := pushOldInwardExpr_assign_run_eq _ _ _ _
        rw [hEq] at hRun
        injection hRun with hRes _
        exact hRes.symm
      · -- preserves inoutNames — use the global theorem (already proved in this file)
        apply pushAssignTargets_preserves_inoutNames_ofIH
        intro tgt _ _ _ s'
        exact pushOldInwardExpr_preserves_inoutNames s' tgt
      · rfl
    obtain ⟨ts', val', sT, hShape, hPresT, hValEq'⟩ := hResShape
    rw [hShape] at hSub_named
    rw [subOlds_assign] at hSub_named
    have ihV := ih (sizeOf value) hVSz sT value rfl
    rw [hPresT] at ihV
    rw [← hValEq'] at ihV
    exact ihV subOld hSub_named

/-! ## Subgoal 5: lifting to `mapProcedureM` -/

/-- Helper: each output of `List.mapM f` over a `StateM` is `f` applied
    to some input element with some threaded state. -/
private theorem listMapM_mem_form (xs : List StmtExprMd) (s : PushOldState)
    (e : StmtExprMd)
    (h : e ∈ ((xs.mapM pushOldInwardExpr).run s).fst) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, pure, StateT.pure] at h
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp [StateT.run, StateT.bind, bind] at h
    cases h with
    | head => exact ⟨x, s, rfl⟩
    | tail _ h1 =>
      obtain ⟨e0, s_e, hEq⟩ := ih _ h1
      exact ⟨e0, s_e, hEq⟩

/-- List membership form: `e ∈ (xs.mapM pushOldInwardExpr s).fst` iff
    `e = ((pushOldInwardExpr e0).run s_e).fst` for some `e0 ∈ xs` and threaded
    `s_e` with `inoutNames = s.inoutNames`. -/
private theorem listMapM_pushOldInwardExpr_mem
    (xs : List StmtExprMd) (s : PushOldState) (e : StmtExprMd)
    (h : e ∈ ((xs.mapM pushOldInwardExpr).run s).fst) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst ∧
      s_e.inoutNames = s.inoutNames := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure] at h
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at h
    generalize hM : (pushOldInwardExpr x) s = resX at h
    obtain ⟨x', sX⟩ := resX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at h
    generalize hRest : xs.mapM pushOldInwardExpr sX = resRest at h
    obtain ⟨ys', sRest⟩ := resRest
    simp at h
    cases h with
    | inl heq =>
      refine ⟨x, s, ?_, rfl⟩
      rw [heq]
      show x' = (pushOldInwardExpr x s).fst
      rw [hM]
    | inr hmem =>
      have hPresX := pushOldInwardExpr_preserves_inoutNames s x
      have hSX : ((pushOldInwardExpr x).run s).snd = sX := by
        show (pushOldInwardExpr x s).snd = sX; rw [hM]
      rw [hSX] at hPresX
      have hMemRest : e ∈ ((xs.mapM pushOldInwardExpr).run sX).fst := by
        show e ∈ (xs.mapM pushOldInwardExpr sX).fst
        rw [hRest]; exact hmem
      obtain ⟨e0, s_e, hEq, hSame⟩ := ih sX hMemRest
      exact ⟨e0, s_e, hEq, hSame.trans hPresX⟩

/-- `Option.mapM pushOldInwardExpr o` member form. -/
private theorem optionMapM_pushOldInwardExpr_mem
    (o : Option StmtExprMd) (s : PushOldState) (e : StmtExprMd)
    (h : e ∈ ((o.mapM pushOldInwardExpr).run s).fst.toList) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst ∧
      s_e.inoutNames = s.inoutNames := by
  cases o with
  | none =>
    simp [Option.mapM, StateT.run, StateT.pure, pure] at h
  | some r =>
    simp only [Option.mapM, StateT.run, StateT.bind, bind, StateT.pure, pure,
               Functor.map, StateT.map] at h
    generalize hM : (pushOldInwardExpr r) s = resR at h
    obtain ⟨r', sR⟩ := resR
    simp [Option.toList] at h
    rw [h]
    refine ⟨r, s, ?_, rfl⟩
    show r' = (pushOldInwardExpr r s).fst
    rw [hM]

/-- `condition` field membership for a `xs.mapM (Condition.mapM pushOldInwardExpr)`. -/
private theorem listMapM_conditionMapM_mem
    (xs : List Condition) (s : PushOldState) (e : StmtExprMd)
    (h : e ∈ (((xs.mapM (Condition.mapM pushOldInwardExpr)).run s).fst).map (·.condition)) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst ∧
      s_e.inoutNames = s.inoutNames := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure] at h
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp only [Condition.mapM, StateT.run, StateT.bind, bind, StateT.pure, pure] at h
    generalize hM : (pushOldInwardExpr x.condition) s = resX at h
    obtain ⟨c', sX⟩ := resX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at h
    generalize hRest : xs.mapM (Condition.mapM pushOldInwardExpr) sX = resRest at h
    obtain ⟨ys', sRest⟩ := resRest
    simp [List.map_cons] at h
    cases h with
    | inl heq =>
      refine ⟨x.condition, s, ?_, rfl⟩
      rw [heq]
      show c' = (pushOldInwardExpr x.condition s).fst
      rw [hM]
    | inr hmem =>
      have hPresX := pushOldInwardExpr_preserves_inoutNames s x.condition
      have hSX : ((pushOldInwardExpr x.condition).run s).snd = sX := by
        show (pushOldInwardExpr x.condition s).snd = sX; rw [hM]
      rw [hSX] at hPresX
      have hMemRest : e ∈ ((xs.mapM (Condition.mapM pushOldInwardExpr)).run sX).fst.map (·.condition) := by
        show e ∈ (xs.mapM (Condition.mapM pushOldInwardExpr) sX).fst.map (·.condition)
        rw [hRest]
        rw [List.mem_map]
        exact hmem
      obtain ⟨e0, s_e, hEq, hSame⟩ := ih sX hMemRest
      exact ⟨e0, s_e, hEq, hSame.trans hPresX⟩

/-- A `xs.mapM (Condition.mapM pushOldInwardExpr)` preserves `inoutNames`. -/
private theorem listMapM_conditionMapM_preserves_inoutNames
    (xs : List Condition) (s : PushOldState) :
    ((xs.mapM (Condition.mapM pushOldInwardExpr)).run s).snd.inoutNames = s.inoutNames := by
  induction xs generalizing s with
  | nil => simp [List.mapM_nil, StateT.run, StateT.pure, pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    simp only [Condition.mapM, StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (pushOldInwardExpr x.condition) s = resX
    obtain ⟨c', sX⟩ := resX
    have hPresX := pushOldInwardExpr_preserves_inoutNames s x.condition
    have hSX : ((pushOldInwardExpr x.condition).run s).snd = sX := by
      show (pushOldInwardExpr x.condition s).snd = sX; rw [hM]
    rw [hSX] at hPresX
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hRest : xs.mapM (Condition.mapM pushOldInwardExpr) sX = resRest
    obtain ⟨ys', sRest⟩ := resRest
    have hRestPres := ih sX
    have hSR : ((xs.mapM (Condition.mapM pushOldInwardExpr)).run sX).snd = sRest := by
      show (xs.mapM (Condition.mapM pushOldInwardExpr) sX).snd = sRest; rw [hRest]
    rw [hSR] at hRestPres
    show sRest.inoutNames = s.inoutNames
    exact hRestPres.trans hPresX

/-- `Option.mapM pushOldInwardExpr` preserves `inoutNames`. -/
private theorem optionMapM_pushOldInwardExpr_preserves_inoutNames
    (o : Option StmtExprMd) (s : PushOldState) :
    ((o.mapM pushOldInwardExpr).run s).snd.inoutNames = s.inoutNames := by
  cases o with
  | none => simp [Option.mapM, StateT.run, StateT.pure, pure]
  | some r =>
    simp only [Option.mapM, StateT.run, StateT.bind, bind, StateT.pure, pure,
               Functor.map, StateT.map]
    generalize hM : (pushOldInwardExpr r) s = resR
    obtain ⟨r', sR⟩ := resR
    have hPresR := pushOldInwardExpr_preserves_inoutNames s r
    have hSR : ((pushOldInwardExpr r).run s).snd = sR := by
      show (pushOldInwardExpr r s).snd = sR; rw [hM]
    rw [hSR] at hPresR
    exact hPresR

/-- `mapProcedureBodiesM pushOldInwardExpr proc` preserves `inoutNames`. -/
private theorem mapProcedureBodiesM_pushOldInwardExpr_preserves_inoutNames
    (proc : Procedure) (s : PushOldState) :
    ((mapProcedureBodiesM pushOldInwardExpr proc).run s).snd.inoutNames = s.inoutNames := by
  unfold mapProcedureBodiesM
  cases proc.body with
  | Transparent b =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hM : (pushOldInwardExpr b) s = resB
    obtain ⟨b', sB⟩ := resB
    have hPres := pushOldInwardExpr_preserves_inoutNames s b
    have hSB : ((pushOldInwardExpr b).run s).snd = sB := by
      show (pushOldInwardExpr b s).snd = sB; rw [hM]
    rw [hSB] at hPres
    exact hPres
  | Opaque posts impl mods =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hP : (posts.mapM (Condition.mapM pushOldInwardExpr)) s = resP
    obtain ⟨p', sP⟩ := resP
    have hPresP := listMapM_conditionMapM_preserves_inoutNames posts s
    have hSP : ((posts.mapM (Condition.mapM pushOldInwardExpr)).run s).snd = sP := by
      show (posts.mapM (Condition.mapM pushOldInwardExpr) s).snd = sP; rw [hP]
    rw [hSP] at hPresP
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hI : (impl.mapM pushOldInwardExpr) sP = resI
    obtain ⟨i', sI⟩ := resI
    have hPresI := optionMapM_pushOldInwardExpr_preserves_inoutNames impl sP
    have hSI : ((impl.mapM pushOldInwardExpr).run sP).snd = sI := by
      show (impl.mapM pushOldInwardExpr sP).snd = sI; rw [hI]
    rw [hSI] at hPresI
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hMo : (mods.mapM pushOldInwardExpr) sI = resMo
    obtain ⟨m', sM⟩ := resMo
    have hPresM : ((mods.mapM pushOldInwardExpr).run sI).snd.inoutNames = sI.inoutNames :=
      listMapM_pushOldInwardExpr_preserves mods sI
        (fun x _ s' => pushOldInwardExpr_preserves_inoutNames s' x)
    have hSM : ((mods.mapM pushOldInwardExpr).run sI).snd = sM := by
      show (mods.mapM pushOldInwardExpr sI).snd = sM; rw [hMo]
    rw [hSM] at hPresM
    exact ((hPresM.trans hPresI).trans hPresP)
  | Abstract posts =>
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure]
    generalize hP : (posts.mapM (Condition.mapM pushOldInwardExpr)) s = resP
    obtain ⟨p', sP⟩ := resP
    have hPresP := listMapM_conditionMapM_preserves_inoutNames posts s
    have hSP : ((posts.mapM (Condition.mapM pushOldInwardExpr)).run s).snd = sP := by
      show (posts.mapM (Condition.mapM pushOldInwardExpr) s).snd = sP; rw [hP]
    rw [hSP] at hPresP
    exact hPresP
  | External =>
    simp [StateT.run, StateT.pure, pure]

/-- `Body`-list selection (the lookup used inside `Procedure.allStmtExprs`). -/
private def bodyAllStmtExprs (b : Body) : List StmtExprMd :=
  match b with
  | .Transparent body => [body]
  | .Opaque ps impl mods => ps.map (fun c : Condition => c.condition) ++ impl.toList ++ mods
  | .Abstract ps => ps.map (fun c : Condition => c.condition)
  | .External => []

/-- Membership in `mapProcedureBodiesM`'s body output traces back to a
    `pushOldInwardExpr` on some input element. -/
private theorem mapProcedureBodiesM_body_form
    (proc : Procedure) (s : PushOldState) (e : StmtExprMd)
    (hE : e ∈ bodyAllStmtExprs ((mapProcedureBodiesM pushOldInwardExpr proc).run s).fst.body) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst ∧
      s_e.inoutNames = s.inoutNames := by
  unfold mapProcedureBodiesM at hE
  cases hBody : proc.body with
  | Transparent b =>
    rw [hBody] at hE
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
    generalize hM : (pushOldInwardExpr b) s = resB at hE
    obtain ⟨b', sB⟩ := resB
    -- hE : e ∈ bodyAllStmtExprs (Body.Transparent b') — equiv. e ∈ [b']
    simp only [bodyAllStmtExprs, List.mem_singleton] at hE
    rw [hE]
    refine ⟨b, s, ?_, rfl⟩
    show b' = (pushOldInwardExpr b s).fst
    rw [hM]
  | Opaque posts impl mods =>
    rw [hBody] at hE
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
    generalize hP : (posts.mapM (Condition.mapM pushOldInwardExpr)) s = resP at hE
    obtain ⟨p', sP⟩ := resP
    have hPresP := listMapM_conditionMapM_preserves_inoutNames posts s
    have hSP : ((posts.mapM (Condition.mapM pushOldInwardExpr)).run s).snd = sP := by
      show (posts.mapM (Condition.mapM pushOldInwardExpr) s).snd = sP; rw [hP]
    rw [hSP] at hPresP
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
    generalize hI : (impl.mapM pushOldInwardExpr) sP = resI at hE
    obtain ⟨i', sI⟩ := resI
    have hPresI := optionMapM_pushOldInwardExpr_preserves_inoutNames impl sP
    have hSI : ((impl.mapM pushOldInwardExpr).run sP).snd = sI := by
      show (impl.mapM pushOldInwardExpr sP).snd = sI; rw [hI]
    rw [hSI] at hPresI
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
    generalize hMo : (mods.mapM pushOldInwardExpr) sI = resMo at hE
    obtain ⟨m', sM⟩ := resMo
    have hPresM : ((mods.mapM pushOldInwardExpr).run sI).snd.inoutNames = sI.inoutNames :=
      listMapM_pushOldInwardExpr_preserves mods sI
        (fun x _ s' => pushOldInwardExpr_preserves_inoutNames s' x)
    have hSM : ((mods.mapM pushOldInwardExpr).run sI).snd = sM := by
      show (mods.mapM pushOldInwardExpr sI).snd = sM; rw [hMo]
    rw [hSM] at hPresM
    simp only [bodyAllStmtExprs, List.mem_append] at hE
    rcases hE with (hPre | hImpl) | hMods
    · have hMem : e ∈ ((posts.mapM (Condition.mapM pushOldInwardExpr)).run s).fst.map
                    (fun c : Condition => c.condition) := by
        show e ∈ (posts.mapM (Condition.mapM pushOldInwardExpr) s).fst.map
                  (fun c : Condition => c.condition)
        rw [hP]; exact hPre
      exact listMapM_conditionMapM_mem _ _ _ hMem
    · have hMem : e ∈ ((impl.mapM pushOldInwardExpr).run sP).fst.toList := by
        show e ∈ (impl.mapM pushOldInwardExpr sP).fst.toList
        rw [hI]; exact hImpl
      obtain ⟨e0, s_e, hEq, hSame⟩ := optionMapM_pushOldInwardExpr_mem _ _ _ hMem
      exact ⟨e0, s_e, hEq, hSame.trans hPresP⟩
    · have hMem : e ∈ ((mods.mapM pushOldInwardExpr).run sI).fst := by
        show e ∈ (mods.mapM pushOldInwardExpr sI).fst
        rw [hMo]; exact hMods
      obtain ⟨e0, s_e, hEq, hSame⟩ := listMapM_pushOldInwardExpr_mem _ _ _ hMem
      exact ⟨e0, s_e, hEq, (hSame.trans hPresI).trans hPresP⟩
  | Abstract posts =>
    rw [hBody] at hE
    simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
    generalize hP : (posts.mapM (Condition.mapM pushOldInwardExpr)) s = resP at hE
    obtain ⟨p', sP⟩ := resP
    simp only [bodyAllStmtExprs] at hE
    have hMem : e ∈ ((posts.mapM (Condition.mapM pushOldInwardExpr)).run s).fst.map
                  (fun c : Condition => c.condition) := by
      show e ∈ (posts.mapM (Condition.mapM pushOldInwardExpr) s).fst.map
                (fun c : Condition => c.condition)
      rw [hP]; exact hE
    exact listMapM_conditionMapM_mem _ _ _ hMem
  | External =>
    rw [hBody] at hE
    simp only [StateT.run, StateT.pure, pure] at hE
    rw [hBody] at hE
    simp [bodyAllStmtExprs] at hE

private theorem mapProcedureM_allStmtExprs_form
    (s : PushOldState) (proc : Procedure) (e : StmtExprMd)
    (hE : e ∈ ((mapProcedureM pushOldInwardExpr proc).run s).fst.allStmtExprs) :
    ∃ (e0 : StmtExprMd) (s_e : PushOldState),
      e = ((pushOldInwardExpr e0).run s_e).fst ∧
      s_e.inoutNames = s.inoutNames := by
  unfold mapProcedureM at hE
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
  generalize hB : (mapProcedureBodiesM pushOldInwardExpr proc) s = resB at hE
  obtain ⟨procB, sB⟩ := resB
  have hPresB := mapProcedureBodiesM_pushOldInwardExpr_preserves_inoutNames proc s
  have hSB : ((mapProcedureBodiesM pushOldInwardExpr proc).run s).snd = sB := by
    show (mapProcedureBodiesM pushOldInwardExpr proc s).snd = sB; rw [hB]
  rw [hSB] at hPresB
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
  generalize hP : (procB.preconditions.mapM (Condition.mapM pushOldInwardExpr)) sB = resP at hE
  obtain ⟨preconds, sP⟩ := resP
  have hPresP := listMapM_conditionMapM_preserves_inoutNames procB.preconditions sB
  have hSP : ((procB.preconditions.mapM (Condition.mapM pushOldInwardExpr)).run sB).snd = sP := by
    show (procB.preconditions.mapM (Condition.mapM pushOldInwardExpr) sB).snd = sP; rw [hP]
  rw [hSP] at hPresP
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
  generalize hD : (procB.decreases.mapM pushOldInwardExpr) sP = resD at hE
  obtain ⟨dec, sD⟩ := resD
  have hPresD := optionMapM_pushOldInwardExpr_preserves_inoutNames procB.decreases sP
  have hSD : ((procB.decreases.mapM pushOldInwardExpr).run sP).snd = sD := by
    show (procB.decreases.mapM pushOldInwardExpr sP).snd = sD; rw [hD]
  rw [hSD] at hPresD
  simp only [StateT.run, StateT.bind, bind, StateT.pure, pure] at hE
  generalize hI : (procB.invokeOn.mapM pushOldInwardExpr) sD = resI at hE
  obtain ⟨invk, sI⟩ := resI
  have hSPres : sP.inoutNames = s.inoutNames := hPresP.trans hPresB
  have hSDPres : sD.inoutNames = s.inoutNames := hPresD.trans hSPres
  unfold Procedure.allStmtExprs at hE
  simp only [List.mem_append] at hE
  rcases hE with ((hPre | hDec) | hBody) | hInvk
  · have hMem : e ∈ ((procB.preconditions.mapM (Condition.mapM pushOldInwardExpr)).run sB).fst.map
                  (fun c : Condition => c.condition) := by
      show e ∈ (procB.preconditions.mapM (Condition.mapM pushOldInwardExpr) sB).fst.map
                (fun c : Condition => c.condition)
      rw [hP]
      simp only [List.mem_map] at hPre
      simp only [List.mem_map]
      exact hPre
    obtain ⟨e0, s_e, hEq, hSame⟩ := listMapM_conditionMapM_mem _ _ _ hMem
    exact ⟨e0, s_e, hEq, hSame.trans hPresB⟩
  · have hMem : e ∈ ((procB.decreases.mapM pushOldInwardExpr).run sP).fst.toList := by
      show e ∈ (procB.decreases.mapM pushOldInwardExpr sP).fst.toList
      rw [hD]; exact hDec
    obtain ⟨e0, s_e, hEq, hSame⟩ := optionMapM_pushOldInwardExpr_mem _ _ _ hMem
    exact ⟨e0, s_e, hEq, hSame.trans hSPres⟩
  · -- body. Note that procB.body equals the body of `mapProcedureBodiesM ... .fst`,
    -- since structure-update doesn't touch the body field.
    have hBodyEq : procB.body = ((mapProcedureBodiesM pushOldInwardExpr proc).run s).fst.body := by
      show procB.body = (mapProcedureBodiesM pushOldInwardExpr proc s).fst.body
      rw [hB]
    have hMem : e ∈ bodyAllStmtExprs ((mapProcedureBodiesM pushOldInwardExpr proc).run s).fst.body := by
      rw [← hBodyEq]
      show e ∈ bodyAllStmtExprs procB.body
      unfold bodyAllStmtExprs
      exact hBody
    exact mapProcedureBodiesM_body_form proc s e hMem
  · have hMem : e ∈ ((procB.invokeOn.mapM pushOldInwardExpr).run sD).fst.toList := by
      show e ∈ (procB.invokeOn.mapM pushOldInwardExpr sD).fst.toList
      rw [hI]; exact hInvk
    obtain ⟨e0, s_e, hEq, hSame⟩ := optionMapM_pushOldInwardExpr_mem _ _ _ hMem
    exact ⟨e0, s_e, hEq, hSame.trans hSDPres⟩

/-- Every `StmtExprMd` reachable from `mapProcedureM pushOldInwardExpr proc`
    has all-canonical `Old`s for `s.inoutNames`. -/
theorem mapProcedureM_pushOldInwardExpr_canonical
    (s : PushOldState) (proc : Procedure) (e : StmtExprMd)
    (hE : e ∈ ((mapProcedureM pushOldInwardExpr proc).run s).fst.allStmtExprs) :
    AllSubOldsCanonical s.inoutNames e := by
  obtain ⟨e0, s_e, hEq, hSame⟩ := mapProcedureM_allStmtExprs_form s proc e hE
  rw [hEq, ← hSame]
  exact pushOldInwardExpr_canonical s_e e0

/-! ## Subgoal 6: `transformProcedurePushOld` sets `inoutNames` correctly -/

/-- After `transformProcedurePushOld proc`, the procedure's contents are all
    canonical for `procInoutNames proc`.

    Reduces to subgoal 5: `transformProcedurePushOld` first sets
    `inoutNames := procInoutNames proc`, then runs `mapProcedureM
    pushOldInwardExpr proc` against that state. -/
theorem transformProcedurePushOld_canonical
    (s : PushOldState) (proc : Procedure) (e : StmtExprMd)
    (hE : e ∈ ((transformProcedurePushOld proc).run s).fst.allStmtExprs) :
    AllSubOldsCanonical (procInoutNames proc) e := by
  -- `transformProcedurePushOld` is `modify (inoutNames := ...) >>= mapProcedureM ...`.
  -- The result equals running `mapProcedureM pushOldInwardExpr proc`
  -- against state `{ s with inoutNames := procInoutNames proc }`.
  have hSame : ((transformProcedurePushOld proc).run s).fst =
               ((mapProcedureM pushOldInwardExpr proc).run
                 { s with inoutNames := procInoutNames proc }).fst := by
    simp [transformProcedurePushOld, StateT.run, StateT.bind, bind, modify,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  rw [hSame] at hE
  exact mapProcedureM_pushOldInwardExpr_canonical _ proc e hE

/-! ## Subgoal 7: `pushOldInward` lifts to all procedures -/

/-- Each output procedure of `procs.mapM transformProcedurePushOld` is the
    image of some input procedure under `transformProcedurePushOld`. -/
private theorem mapM_transformProcedurePushOld_mem
    (procs : List Procedure) (s : PushOldState)
    (output : Procedure)
    (h : output ∈ ((procs.mapM transformProcedurePushOld).run s).fst) :
    ∃ (input : Procedure) (s_in : PushOldState),
      input ∈ procs ∧
      output = ((transformProcedurePushOld input).run s_in).fst := by
  induction procs generalizing s with
  | nil =>
    simp [List.mapM_nil, StateT.run, pure, StateT.pure] at h
  | cons p ps ih =>
    rw [List.mapM_cons] at h
    simp [StateT.run, StateT.bind, bind] at h
    cases h with
    | head =>
      exact ⟨p, s, List.mem_cons_self, rfl⟩
    | tail _ h1 =>
      obtain ⟨input, s_in, hMem, hEq⟩ := ih _ h1
      exact ⟨input, s_in, List.mem_cons_of_mem _ hMem, hEq⟩

/-- Every procedure produced by `pushOldInward` has its contents all
    canonical for that procedure's inouts. -/
theorem pushOldInward_canonical (p : Program) :
    ∀ proc ∈ (pushOldInward p).fst.staticProcedures,
    ∀ e ∈ proc.allStmtExprs,
    AllSubOldsCanonical (procInoutNames proc) e := by
  intro outProc hOut e hE
  unfold pushOldInward at hOut
  obtain ⟨inProc, s_in, _hInMem, hEq⟩ :=
    mapM_transformProcedurePushOld_mem _ _ _ hOut
  have hInouts : procInoutNames outProc = procInoutNames inProc := by
    have hPreserve :
        ((transformProcedurePushOld inProc).run s_in).fst.inputs = inProc.inputs ∧
        ((transformProcedurePushOld inProc).run s_in).fst.outputs = inProc.outputs := by
      simp [transformProcedurePushOld, mapProcedureM, mapProcedureBodiesM]
      cases inProc.body <;>
        (simp only [StateT.run, StateT.bind, bind, StateT.pure, pure, modify,
                    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
         exact ⟨rfl, rfl⟩)
    rw [hEq]
    unfold procInoutNames
    rw [hPreserve.1, hPreserve.2]
  rw [hInouts]
  rw [hEq] at hE
  exact transformProcedurePushOld_canonical s_in inProc e hE

/-! ## The main theorem -/

/-- Every `Old` subterm in `pushOldInward`'s output has shape
    `.Old ⟨.Var (.Local n), _⟩` with `n.text` an inout parameter. -/
theorem pushOldInward_old_normalized (p : Program) :
    ∀ proc ∈ (pushOldInward p).fst.staticProcedures,
    ∀ e ∈ proc.allStmtExprs,
    ∀ subOld ∈ e.subOlds,
    ∃ (n : Identifier) (src1 src2 : Option FileRange),
      subOld = ⟨.Old ⟨.Var (.Local n), src1⟩, src2⟩ ∧
      n.text ∈ procInoutNames proc := by
  intro proc hProc e hE subOld hSub
  have hCan := pushOldInward_canonical p proc hProc e hE
  exact hCan subOld hSub

end -- public section
end Laurel
end Strata
