/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Languages.Core.StmtExtendCallBridgeProps
public import Strata.Transform.DetToKleeneCorrect
public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect
public import Strata.Transform.CoreTransformProps

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.DetToKleeneCorrect
import all Strata.Transform.NondetElimCorrect
import all Strata.Transform.StructuredToUnstructuredCorrect

/-! # Loop-init hoist properties

Structural and well-formedness facts about the same-name loop-init hoist
(`Block.liftInitsInLoopBody` / `Block.hoistLoopPrefixInits`). The trace
correctness proof in `LoopInitHoistCorrect` consumes them.

Key results:
  * Typed definedness — `DTyped` with `DTyped.append` and
    `DTyped.projectStore`: every hoisted name holds a value of its declared type.
  * Lift residuals — `liftP_cons_residual`, `liftP_block_residual`,
    `liftP_ite_residual`, and the `liftP_stmt_residual_no_inits` /
    `liftP_body_residual_no_inits` pair: lifting leaves init-free code unchanged.
  * Typed harvested inits — `Stmt`/`Block.typedInitVars`, `Cmds.typedInitVars`,
    `typedInitVarsLookup` with `typedInitVarsLookup_agrees`, and
    `Stmt`/`Block.liftP_typedInitVars_res`.
  * Prelude — `preludeHavocs` / `preludeNames`, the `Stmt`/`Block.liftP_havocs_nondet`
    pair, and `nondet_cmds_to_prelude`: the lifted commands are the prelude havocs.
  * Init names and types — `Stmt`/`Block.liftP_initVars_mem`,
    `Stmt`/`Block.hoistP_initVars_sub`, the `*_initVars_perm` and
    `*_initTypes_perm` lift/hoist pairs, `Block.hoistP_initTypesInhabited`, and
    `Stmt`/`Block.typedInitVars_snd_sub_initTypes`.
  * Output shape — the hoist preserves `noNondetGuards`, `loopHasNoInvariants`,
    `noMeasureLoops`, and `getBlockLabels` (`Stmt`/`Block.hoistP_*`, built from
    the `Stmt`/`Block.liftP_res_*` pairs), and its output is unconditionally
    `loopBodyNoInits` (`Stmt`/`Block.hoistP_allLoop_uncond`,
    `Block.hoistP_loopBodyNoInits`).
  * Def-use preservation — `LoopInitHoistWF.Block.liftInitsInLoopBody_defUseWellFormed`
    and `LoopInitHoistWF.Block.hoistLoopPrefixInits_defUseWellFormed`.
  * Annotation-check preservation —
    `LoopInitHoistWF.Block.hoistLoopPrefixInits_fvarTypesWellAnnotated`: when the
    source's init names are distinct, the hoisted program passes the free-variable
    annotation check against every typing that the source passes it against and that
    types none of those names.
  * Core bridge — `Core.hoistLoopPrefixInits_eq_some` and
    `Core.LoopInitHoist.blockInitEnvWF`, which transports `BlockInitEnvWF` to
    the Core wrapper's output. -/

public section

namespace Imperative

/-! ## Typed target-definedness invariant.

The hoisted `set y := e` step (the same-name rewrite of a body-local `init y := e`)
carries a typed-store premise (`HasVal.valueOfStoredTy`): the value written must
share a type with the value already stored at `y`.  The prelude havoc seeds `y` with
a value of `y`'s DECLARED type, so the hoist simulation must record, for each
hoisted name, the declared type of its value in the target store, not merely that
it is defined.  `Dτ` is a total type assignment (only its values on `D` matter). -/
/-- Every name in `D` holds, in `ρ`, a value of the type `Dτ` assigns it. -/
def DTyped {P : PureExpr} [HasVal P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident) (ρ : Env P) : Prop :=
  ∀ y ∈ D, ∃ prev, ρ.store y = some prev ∧ HasVal.valueOfTy ρ.factory prev (Dτ y)

/-- `DTyped` splits/combines over a list append. -/
theorem DTyped.append {P : PureExpr} [HasVal P]
    {Dτ : P.Ident → P.Ty} {D₁ D₂ : List P.Ident} {ρ : Env P}
    (h₁ : DTyped Dτ D₁ ρ) (h₂ : DTyped Dτ D₂ ρ) :
    DTyped Dτ (D₁ ++ D₂) ρ := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact h₁ y h
  · exact h₂ y h

/-- Re-establish `DTyped` across a per-iteration / block-scope `projectStore`
boundary: every `D`-name is parent-defined (from the parent invariant) so it
survives the projection, taking the body's value, and the body invariant supplies
the type. -/
theorem DTyped.projectStore {P : PureExpr} [HasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {ρ_parent ρ_body : Env P}
    (h_parent : DTyped Dτ D ρ_parent)
    (h_body : DTyped Dτ D ρ_body) :
    DTyped Dτ D
      { ρ_body with store := projectStore ρ_parent.store ρ_body.store } := by
  intro y hy
  obtain ⟨prevP, hP, _⟩ := h_parent y hy
  obtain ⟨prevB, hB, htyB⟩ := h_body y hy
  have hsome : (ρ_parent.store y).isSome = true := by rw [hP]; rfl
  refine ⟨prevB, ?_, htyB⟩
  show (if (ρ_parent.store y).isSome then ρ_body.store y else none) = some prevB
  rw [ite_eq_left hsome]; exact hB

namespace LoopInitHoistProducerProps

/-!
# Loop-init hoist producer: pass-output facts

The same-name loop-init hoist (`Block.liftInitsInLoopBody`) lifts each body-local
`init y := e` to a same-name prelude havoc `init y := *` and rewrites the body's
`init y` to `set y`, with no fresh name and no rename.  This namespace proves the
`hoistP_*`/`liftP_*` shape-preservation lemmas that the `.loop` arm of the hoist
correctness proof consumes.
-/

/-! ## Residual peel lemmas for the same-name lift. -/

/-- The same-name lift residual of `s :: rest` is the residual of `s` followed by
the residual of `rest`. -/
theorem liftP_cons_residual {P : PureExpr} (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    (Block.liftInitsInLoopBody (s :: rest)).2
      = (Stmt.liftInitsInLoopBody s).2 ++ (Block.liftInitsInLoopBody rest).2 := by
  rw [Block.liftInitsInLoopBody]

/-- The same-name lift residual of a `.block` is the block with its body replaced by
the body's residual. -/
theorem liftP_block_residual {P : PureExpr} (lbl : String) (bss : List (Stmt P (Cmd P))) (md :
    MetaData P) :
    (Stmt.liftInitsInLoopBody (.block lbl bss md)).2 = [.block lbl (Block.liftInitsInLoopBody bss).2
        md] := by
  rw [Stmt.liftInitsInLoopBody]

/-- The same-name lift residual of an `.ite` is the `.ite` with both branches replaced
by their residuals. -/
theorem liftP_ite_residual {P : PureExpr} (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md
    : MetaData P) :
    (Stmt.liftInitsInLoopBody (.ite g tss ess md)).2
      = [.ite g (Block.liftInitsInLoopBody tss).2 (Block.liftInitsInLoopBody ess).2 md] := by
  rw [Stmt.liftInitsInLoopBody]

mutual
/-- An init-free statement's same-name lift residual is the statement verbatim. -/
theorem liftP_stmt_residual_no_inits {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.noInitsAnywhere s
    = true) :
    (Stmt.liftInitsInLoopBody s).2 = [s] := by
  match s with
  | .cmd (.init _ _ _ _) => exact absurd h (by simp [Stmt.noInitsAnywhere])
  | .cmd (.set _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.assert _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.assume _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.cover _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .block lbl bss md =>
      rw [liftP_block_residual]
      rw [liftP_body_residual_no_inits bss (by simpa [Stmt.noInitsAnywhere] using h)]
  | .ite g tss ess md =>
      rw [liftP_ite_residual]
      simp only [Stmt.noInitsAnywhere, Bool.and_eq_true] at h
      rw [liftP_body_residual_no_inits tss h.1, liftP_body_residual_no_inits ess h.2]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody]
  termination_by sizeOf s

/-- An init-free body's same-name lift residual is the body verbatim. -/
theorem liftP_body_residual_no_inits {P : PureExpr} (body : List (Stmt P (Cmd P))) (h :
    Block.noInitsAnywhere body = true) :
    (Block.liftInitsInLoopBody body).2 = body := by
  match body with
  | [] => rw [Block.liftInitsInLoopBody]
  | s :: rest =>
      rw [liftP_cons_residual]
      simp only [Block.noInitsAnywhere, Bool.and_eq_true] at h
      rw [liftP_stmt_residual_no_inits s h.1, liftP_body_residual_no_inits rest h.2]
      rfl
  termination_by sizeOf body
end

/-! `Dτ`-harvestable typed inits of a statement/block: each `.init a ty` reachable
without descending into a nested loop, paired with its declared type.  Mirrors the
positions `Block.liftInitsInLoopBody` harvests.  A list-valued walker (like
`definedVars`) so the `∀ p ∈ …` consistency hypothesis threads through the
producer's structural recursion without disturbing termination. -/
mutual
/-- The typed inits of a statement that the lift harvests: each `.init a ty`
reachable without entering a nested loop, paired with its declared type. -/
def Stmt.typedInitVars {P : PureExpr} : Stmt P (Cmd P) → List (P.Ident × P.Ty)
  | .cmd (.init a ty _ _) => [(a, ty)]
  | .cmd _ => []
  | .block _ bss _ => Block.typedInitVars bss
  | .ite _ tss ess _ => Block.typedInitVars tss ++ Block.typedInitVars ess
  | .loop _ _ _ _ _ => []
  | .exit _ _ => []
  | .typeDecl _ _ => []

/-- The typed inits of a block that the lift harvests (see `Stmt.typedInitVars`). -/
def Block.typedInitVars {P : PureExpr} : List (Stmt P (Cmd P)) → List (P.Ident × P.Ty)
  | [] => []
  | s :: rest => Stmt.typedInitVars s ++ Block.typedInitVars rest
end

/-- An init-free block harvests no typed inits. -/
theorem Block.typedInitVars_eq_nil_of_noInitsAnywhere {P : PureExpr} [HasFvars P] :
    (ss : List (Stmt P (Cmd P))) → Block.noInitsAnywhere ss = true → Block.typedInitVars ss = []
  | [], _ => rfl
  | s :: rest, h => by
    rw [Block.noInitsAnywhere, Bool.and_eq_true] at h
    rw [Block.typedInitVars, Block.typedInitVars_eq_nil_of_noInitsAnywhere rest h.2, List.append_nil]
    have hs := h.1
    cases s with
    | cmd c =>
        cases c with
        | init _ _ _ _ => simp [Stmt.noInitsAnywhere] at hs
        | set _ _ _ => rfl
        | assert _ _ _ => rfl
        | assume _ _ _ => rfl
        | cover _ _ _ => rfl
    | block lbl bss md =>
        rw [Stmt.typedInitVars]
        exact Block.typedInitVars_eq_nil_of_noInitsAnywhere bss (by simpa [Stmt.noInitsAnywhere] using hs)
    | ite g tss ess md =>
        rw [Stmt.typedInitVars]
        simp only [Stmt.noInitsAnywhere, Bool.and_eq_true] at hs
        rw [Block.typedInitVars_eq_nil_of_noInitsAnywhere tss hs.1,
            Block.typedInitVars_eq_nil_of_noInitsAnywhere ess hs.2, List.append_nil]
    | loop _ _ _ _ _ => rfl
    | exit _ _ => rfl
    | typeDecl _ _ => rfl
  termination_by ss => sizeOf ss

/-! ## A total `Dτ` lookup from a typed-init association list.

The loop arm builds its total type assignment `Dτ` from the harvested typed inits
of the (post-hoist) loop body via a plain association-list lookup, falling back to
`HasBool.boolTy` off the list (its off-list value is irrelevant — only in-list
names are ever queried).  With `Nodup` keys, the lookup agrees with every recorded
pair. -/
/-- Look up a name's type in a typed-init association list, defaulting to
`HasBool.boolTy` for names not on the list. -/
def typedInitVarsLookup {P : PureExpr} [HasBool P] [DecidableEq P.Ident]
    (l : List (P.Ident × P.Ty)) (y : P.Ident) : P.Ty :=
  match l with
  | [] => HasBool.boolTy
  | p :: rest => if p.1 = y then p.2 else typedInitVarsLookup rest y

/-- With `Nodup` keys, `typedInitVarsLookup` returns each recorded pair's type. -/
theorem typedInitVarsLookup_agrees {P : PureExpr} [HasBool P] [DecidableEq P.Ident]
    (l : List (P.Ident × P.Ty)) (h_nodup : (l.map Prod.fst).Nodup)
    (p : P.Ident × P.Ty) (hp : p ∈ l) :
    typedInitVarsLookup l p.1 = p.2 := by
  induction l with
  | nil => exact absurd hp List.not_mem_nil
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at h_nodup
    obtain ⟨ha_notin, h_rest_nodup⟩ := h_nodup
    rw [typedInitVarsLookup]
    by_cases hpa : a.1 = p.1
    · rw [ite_eq_left hpa]
      rcases List.mem_cons.mp hp with h_eq | h_rest
      · rw [h_eq]
      · exfalso; apply ha_notin; rw [hpa]; exact List.mem_map.mpr ⟨p, h_rest, rfl⟩
    · rw [ite_eq_right hpa]
      rcases List.mem_cons.mp hp with h_eq | h_rest
      · exact absurd (congrArg Prod.fst h_eq).symm hpa
      · exact ih h_rest_nodup h_rest

/-- The `(name, type)` pairs carried by a command list's `.init` entries. -/
def Cmds.typedInitVars {P : PureExpr} (cs : List (Cmd P)) : List (P.Ident × P.Ty) :=
  match cs with
  | [] => []
  | (.init y ty _ _) :: rest => (y, ty) :: Cmds.typedInitVars rest
  | _ :: rest => Cmds.typedInitVars rest

/-- The typed inits of a command list distribute over append. -/
theorem Cmds.typedInitVars_append {P : PureExpr} (cs ds : List (Cmd P)) :
    Cmds.typedInitVars (cs ++ ds) = Cmds.typedInitVars cs ++ Cmds.typedInitVars ds := by
  induction cs with
  | nil => rfl
  | cons c rest ih => cases c <;> simp only [List.cons_append, Cmds.typedInitVars, ih]

/-! The typed-init pairs harvested by the same-name lift's prelude (`.1`) are
exactly the statement's shallow `typedInitVars`. -/
mutual
/-- The typed inits of the commands the lift harvests from a statement are exactly
the statement's `typedInitVars`. -/
theorem Stmt.liftP_typedInitVars_res {P : PureExpr} (s : Stmt P (Cmd P)) :
    Cmds.typedInitVars (Stmt.liftInitsInLoopBody s).1 = Stmt.typedInitVars s := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Cmds.typedInitVars, Stmt.typedInitVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.typedInitVars]
      exact Block.liftP_typedInitVars_res bss
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.typedInitVars]
      rw [Cmds.typedInitVars_append, Block.liftP_typedInitVars_res tss,
          Block.liftP_typedInitVars_res ess]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.typedInitVars, Stmt.typedInitVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.typedInitVars, Stmt.typedInitVars]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Cmds.typedInitVars, Stmt.typedInitVars]
  termination_by sizeOf s

/-- The typed inits of the commands the lift harvests from a block are exactly the
block's `typedInitVars`. -/
theorem Block.liftP_typedInitVars_res {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Cmds.typedInitVars (Block.liftInitsInLoopBody ss).1 = Block.typedInitVars ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.typedInitVars, Block.typedInitVars]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody]
      simp only [Block.typedInitVars]
      rw [Cmds.typedInitVars_append, Stmt.liftP_typedInitVars_res s,
          Block.liftP_typedInitVars_res rest]
  termination_by sizeOf ss
end

/-! # Same-name hoist prelude.

The same-name `.loop` arm of the hoist lifts a body-local `init y := e` to a
SAME-name prelude havoc `init y := *` *before* the loop and rewrites the body
init to `set y := e`.  The hoist of a single loop is therefore
`havocs.map Stmt.cmd ++ [.loop g m inv body₂ md]` where `havocs` are the lifted
prelude inits.  `preludeHavocs` / `preludeNames` are the prelude statement list
and its names. -/

/-- The prelude havoc statements built from a `(name, ty, md)` triple list: each
triple `(y, ty, md)` becomes a havoc `Stmt.cmd (Cmd.init y ty .nondet md)`. -/
def preludeHavocs (hs : List (P.Ident × P.Ty × MetaData P)) :
    List (Stmt P (Cmd P)) :=
  hs.map (fun t => .cmd (Cmd.init t.1 t.2.1 .nondet t.2.2))

/-- The names introduced by a prelude triple list. -/
def preludeNames (hs : List (P.Ident × P.Ty × MetaData P)) : List P.Ident :=
  hs.map Prod.fst

/-! ## Lift-level init-name membership (iff). -/
mutual
/-- A name is initialized by the lift of a statement (in the harvested prelude or in
the residual) iff the statement initializes it. -/
theorem Stmt.liftP_initVars_mem {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) (y : P.Ident) :
    (y ∈ Cmds.definedVars (Stmt.liftInitsInLoopBody s).1
      ∨ y ∈ Block.initVars (Stmt.liftInitsInLoopBody s).2) ↔ y ∈ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Cmd.definedVars,
              Block.initVars, Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.liftP_initVars_mem bss y
  | .ite g tss ess md =>
      have ht := Block.liftP_initVars_mem tss y
      have he := Block.liftP_initVars_mem ess y
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, List.mem_append, Cmds.definedVars_append] at ht he ⊢
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl (ht.mp (Or.inl h))
        · exact Or.inr (he.mp (Or.inl h))
        · exact Or.inl (ht.mp (Or.inr h))
        · exact Or.inr (he.mp (Or.inr h))
      · rintro (h | h)
        · rcases ht.mpr h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inl h')
        · rcases he.mpr h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

/-- A name is initialized by the lift of a block (in the harvested prelude or in the
residual) iff the block initializes it. -/
theorem Block.liftP_initVars_mem {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) (y : P.Ident) :
    (y ∈ Cmds.definedVars (Block.liftInitsInLoopBody ss).1
      ∨ y ∈ Block.initVars (Block.liftInitsInLoopBody ss).2) ↔ y ∈ Block.initVars ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | s :: rest =>
      have hs := Stmt.liftP_initVars_mem s y
      have hr := Block.liftP_initVars_mem rest y
      simp only [Block.liftInitsInLoopBody, Block.initVars_cons, Cmds.definedVars_append,
        Block.initVars_append, List.mem_append] at hs hr ⊢
      constructor
      · rintro (h | h)
        · rcases h with h' | h'
          · exact Or.inl (hs.mp (Or.inl h'))
          · exact Or.inr (hr.mp (Or.inl h'))
        · rcases h with h' | h'
          · exact Or.inl (hs.mp (Or.inr h'))
          · exact Or.inr (hr.mp (Or.inr h'))
      · rintro (h | h)
        · rcases hs.mpr h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inl h')
        · rcases hr.mpr h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')
  termination_by sizeOf ss
end

/-! ## Hoist-level init-name membership subset. -/
mutual
/-- Every name initialized by the hoist of a statement is initialized by the
statement. -/
theorem Stmt.hoistP_initVars_sub {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) (y : P.Ident)
    (hy : y ∈ Block.initVars (Stmt.hoistLoopPrefixInits s)) : y ∈ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars,
        Cmd.definedVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil] at hy ⊢
      exact Block.hoistP_initVars_sub bss y hy
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, List.mem_append] at hy ⊢
      rcases hy with h | h
      · exact Or.inl (Block.hoistP_initVars_sub tss y h)
      · exact Or.inr (Block.hoistP_initVars_sub ess y h)
  | .loop g m inv body md =>
      -- hoist = havocs.map .cmd ++ [.loop g m inv body₂ md] where
      -- (havocs, body₂) = lift (hoist body).
      simp only [Stmt.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        Stmt.initVars_loop, Block.initVars_nil, List.append_nil, Block.initVars_map_cmd,
        List.mem_append] at hy ⊢
      -- hy : y ∈ defined havocs ∨ y ∈ initVars body₂  (modulo the [loop] singleton)
      have := (Block.liftP_initVars_mem (Block.hoistLoopPrefixInits body) y).mp hy
      exact Block.hoistP_initVars_sub body y this
  | .exit lbl md => simp_all [Stmt.hoistLoopPrefixInits, Block.initVars]
  | .typeDecl t md => simp_all [Stmt.hoistLoopPrefixInits, Block.initVars]
  termination_by sizeOf s

/-- Every name initialized by the hoist of a block is initialized by the block. -/
theorem Block.hoistP_initVars_sub {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) (y : P.Ident)
    (hy : y ∈ Block.initVars (Block.hoistLoopPrefixInits ss)) : y ∈ Block.initVars ss := by
  match ss with
  | [] => simp_all [Block.hoistLoopPrefixInits, Block.initVars]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        List.mem_append] at hy ⊢
      rcases hy with h | h
      · exact Or.inl (Stmt.hoistP_initVars_sub s y h)
      · exact Or.inr (Block.hoistP_initVars_sub rest y h)
  termination_by sizeOf ss
end

/-! ## Lift havocs are all `.nondet`-inits, hence reconstructible as `preludeHavocs hs`. -/
mutual
/-- Every command the lift harvests from a statement is a nondeterministic `init`. -/
theorem Stmt.liftP_havocs_nondet {P : PureExpr} (s : Stmt P (Cmd P)) :
    ∀ c ∈ (Stmt.liftInitsInLoopBody s).1, ∃ y ty md, c = Cmd.init y ty .nondet md := by
  match s with
  | .cmd c =>
      intro c' hc
      cases c <;> simp_all [Stmt.liftInitsInLoopBody]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody]
      exact Block.liftP_havocs_nondet bss
  | .ite g tss ess md =>
      intro c hc
      simp only [Stmt.liftInitsInLoopBody, List.mem_append] at hc
      rcases hc with h | h
      · exact Block.liftP_havocs_nondet tss c h
      · exact Block.liftP_havocs_nondet ess c h
  | .loop g m inv body md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  | .exit lbl md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  | .typeDecl t md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  termination_by sizeOf s

/-- Every command the lift harvests from a block is a nondeterministic `init`. -/
theorem Block.liftP_havocs_nondet {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    ∀ c ∈ (Block.liftInitsInLoopBody ss).1, ∃ y ty md, c = Cmd.init y ty .nondet md := by
  match ss with
  | [] => intro c hc; simp [Block.liftInitsInLoopBody] at hc
  | s :: rest =>
      intro c hc
      rw [Block.liftInitsInLoopBody] at hc
      simp only [List.mem_append] at hc
      rcases hc with h | h
      · exact Stmt.liftP_havocs_nondet s c h
      · exact Block.liftP_havocs_nondet rest c h
  termination_by sizeOf ss
end

/-- A command list all of whose entries are `.nondet`-inits reconstructs to a
triple list with the matching `preludeHavocs`/`preludeNames`. -/
theorem nondet_cmds_to_prelude {P : PureExpr} (cs : List (Cmd P))
    (h : ∀ c ∈ cs, ∃ y ty md, c = Cmd.init y ty .nondet md) :
    ∃ hs : List (P.Ident × P.Ty × MetaData P),
      cs.map Stmt.cmd = preludeHavocs hs ∧ preludeNames hs = Cmds.definedVars cs
        ∧ hs.map (fun t => (t.1, t.2.1)) = Cmds.typedInitVars cs := by
  induction cs with
  | nil =>
    exact ⟨[], by simp [preludeHavocs], by simp [preludeNames, Cmds.definedVars],
      by simp [Cmds.typedInitVars]⟩
  | cons c rest ih =>
    obtain ⟨y, ty, md, h_c⟩ := h c (List.mem_cons_self)
    obtain ⟨hs, h_map, h_names, h_typed⟩ := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    refine ⟨(y, ty, md) :: hs, ?_, ?_, ?_⟩
    · subst h_c
      simp only [List.map_cons, preludeHavocs, List.map_cons] at h_map ⊢
      rw [h_map]
    · subst h_c
      simp only [preludeNames, List.map_cons, Cmds.definedVars, Cmd.definedVars] at h_names ⊢
      rw [h_names]; rfl
    · subst h_c
      simp only [List.map_cons, Cmds.typedInitVars]
      rw [h_typed]

/-! ## Hoist preserves transportShape / loopBodyNoInits / Nodup of initVars. -/

-- residual `.2` of the same-name lift is noInitsAnywhere when input is loopBodyNoInits.
mutual
/-- If a statement's loop bodies contain no inits, its lift residual contains no
inits anywhere. -/
theorem Stmt.liftP_res_noInits {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) (h : Stmt.loopBodyNoInits s =
    true) :
    Block.noInitsAnywhere (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere,
          Bool.and_true]
      exact Block.liftP_res_noInits bss (by simpa [Stmt.loopBodyNoInits] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      simp only [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere,
          Bool.and_true]
      rw [Block.liftP_res_noInits tss h.1, Block.liftP_res_noInits ess h.2]; rfl
  | .loop g m inv body md =>
      have h_nia : Block.noInitsAnywhere body = true := by
        simp only [Stmt.loopBodyNoInits, Bool.and_eq_true, List.isEmpty_iff] at h
        exact Block.noInitsAnywhere_of_initVars_nil body h.1
      simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere, h_nia]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  termination_by sizeOf s

/-- If a block's loop bodies contain no inits, its lift residual contains no inits
anywhere. -/
theorem Block.liftP_res_noInits {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) (h :
    Block.loopBodyNoInits ss = true) :
    Block.noInitsAnywhere (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noInitsAnywhere]
  | s :: rest =>
      simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody, Block.noInitsAnywhere_append,
          Stmt.liftP_res_noInits s h.1, Block.liftP_res_noInits rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## Hoist preserves loopBodyNoInits. -/
mutual
/-- Lifting preserves `loopBodyNoInits`: if a statement's loop bodies contain no
inits, neither do the loop bodies of its residual. -/
theorem Stmt.liftP_res_allLoop {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) (h : Stmt.loopBodyNoInits s =
    true) :
    Block.loopBodyNoInits (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      exact Block.liftP_res_allLoop bss (by simpa [Stmt.loopBodyNoInits] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      simp only [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      rw [Block.liftP_res_allLoop tss h.1, Block.liftP_res_allLoop ess h.2]; rfl
  | .loop g m inv body md =>
      rw [show (Stmt.liftInitsInLoopBody (.loop g m inv body md)).2 = [.loop g m inv body md] by
        rw [Stmt.liftInitsInLoopBody]]
      simpa only [Block.loopBodyNoInits, Bool.and_true] using h
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  termination_by sizeOf s

/-- Lifting preserves `loopBodyNoInits`: if a block's loop bodies contain no inits,
neither do the loop bodies of its residual. -/
theorem Block.liftP_res_allLoop {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) (h :
    Block.loopBodyNoInits ss = true) :
    Block.loopBodyNoInits (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.loopBodyNoInits]
  | s :: rest =>
      simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody, Block.loopBodyNoInits_append,
          Stmt.liftP_res_allLoop s h.1, Block.liftP_res_allLoop rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## Hoist output is unconditionally `loopBodyNoInits`.

The hoist transformation rewrites every `.loop` body to
`liftInitsInLoopBody (hoistLoopPrefixInits body)`, which lifts all `.init`
commands out of the body and into a havoc prelude. The result therefore has no
`.init` inside any loop body regardless of the source shape: the property holds
of the OUTPUT with no precondition on the input. -/
mutual
/-- The hoist of any statement has no inits in its loop bodies. -/
theorem Stmt.hoistP_allLoop_uncond {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    Block.loopBodyNoInits (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      exact Block.hoistP_allLoop_uncond bss
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      rw [Block.hoistP_allLoop_uncond tss, Block.hoistP_allLoop_uncond ess]; rfl
  | .loop g m inv body md =>
      -- hoist = havocs.map .cmd ++ [.loop g m inv (lift (hoist body)).2 md];
      -- the lift residual lemmas need loopBodyNoInits (hoist body), supplied by the IH.
      have h_hb : Block.loopBodyNoInits (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_allLoop_uncond body
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits_append]
      rw [Block.loopBodyNoInits_map_cmd']
      simp only [Block.loopBodyNoInits, Stmt.loopBodyNoInits, Bool.true_and, Bool.and_true,
        Block.isEmpty_initVars_eq_noInitsAnywhere]
      rw [Block.liftP_res_noInits (Block.hoistLoopPrefixInits body) h_hb,
          Block.liftP_res_allLoop (Block.hoistLoopPrefixInits body) h_hb]; rfl
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  termination_by sizeOf s

/-- The hoist of any block has no inits in its loop bodies. -/
theorem Block.hoistP_allLoop_uncond {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.loopBodyNoInits]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInits, Block.loopBodyNoInits_append,
          Stmt.hoistP_allLoop_uncond s, Block.hoistP_allLoop_uncond rest]; rfl
  termination_by sizeOf ss
end

/-! ## initVars multiset is preserved (List.Perm) by lift and hoist → Nodup transfers. -/

mutual
/-- Lifting a statement permutes its init names: the harvested prelude names
followed by the residual's init names are a permutation of the statement's. -/
theorem Stmt.liftP_initVars_perm {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    List.Perm (Cmds.definedVars (Stmt.liftInitsInLoopBody s).1
      ++ Block.initVars (Stmt.liftInitsInLoopBody s).2) (Stmt.initVars s) := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Cmd.definedVars, Block.initVars,
          Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.liftP_initVars_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, Cmds.definedVars_append]
      have ht := Block.liftP_initVars_perm tss
      have he := Block.liftP_initVars_perm ess
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact ht.append he
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

/-- Lifting a block permutes its init names: the harvested prelude names followed by
the residual's init names are a permutation of the block's. -/
theorem Block.liftP_initVars_perm {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    List.Perm (Cmds.definedVars (Block.liftInitsInLoopBody ss).1
      ++ Block.initVars (Block.liftInitsInLoopBody ss).2) (Block.initVars ss) := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | s :: rest =>
      simp only [Block.liftInitsInLoopBody, Cmds.definedVars_append, Block.initVars_append,
        Block.initVars_cons]
      have hs := Stmt.liftP_initVars_perm s
      have hr := Block.liftP_initVars_perm rest
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact hs.append hr
  termination_by sizeOf ss
end

mutual
/-- Hoisting a statement permutes its init names. -/
theorem Stmt.hoistP_initVars_perm {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    List.Perm (Block.initVars (Stmt.hoistLoopPrefixInits s)) (Stmt.initVars s) := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars,
      Cmd.definedVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.hoistP_initVars_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact (Block.hoistP_initVars_perm tss).append (Block.hoistP_initVars_perm ess)
  | .loop g m inv body md =>
      -- initVars (havocs.map .cmd ++ [loop body₂]) = defined havocs ++ initVars body₂
      --   ~ initVars (hoist body) ~ initVars body.
      simp only [Stmt.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        Stmt.initVars_loop, Block.initVars_nil, List.append_nil, Block.initVars_map_cmd]
      exact (Block.liftP_initVars_perm (Block.hoistLoopPrefixInits body)).trans
        (Block.hoistP_initVars_perm body)
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

/-- Hoisting a block permutes its init names. -/
theorem Block.hoistP_initVars_perm {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    List.Perm (Block.initVars (Block.hoistLoopPrefixInits ss)) (Block.initVars ss) := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.initVars]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons]
      exact (Stmt.hoistP_initVars_perm s).append (Block.hoistP_initVars_perm rest)
  termination_by sizeOf ss
end

/-! ## initTypes multiset preserved by lift and hoist (types analogue).

The type-level counterparts of the `initVars` perm lemmas: hoisting and lifting
permute (never add or drop) the multiset of declared init types, which lets a
source-side `InitTypesInhabited` witness set transport to the hoisted body. -/

/-- Init-declared types of a command list. -/
def Cmds.initTypes {P : PureExpr} (cs : List (Cmd P)) : List P.Ty :=
  match cs with
  | [] => []
  | c :: rest => Cmd.initTypes c ++ Cmds.initTypes rest

/-- The declared init types of a command list distribute over append. -/
theorem Cmds.initTypes_append {P : PureExpr} (xs ys : List (Cmd P)) :
    Cmds.initTypes (xs ++ ys) = Cmds.initTypes xs ++ Cmds.initTypes ys := by
  induction xs with
  | nil => rfl
  | cons c rest ih => simp only [List.cons_append, Cmds.initTypes, ih, List.append_assoc]

/-- Wrapping commands as `.cmd` statements keeps their declared init types. -/
theorem Block.initTypes_map_cmd {P : PureExpr} (cs : List (Cmd P)) :
    Block.initTypes (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = Cmds.initTypes cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.map_cons, Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes,
        Cmds.initTypes, ih]

mutual
/-- Lifting a statement permutes its declared init types: the harvested prelude's
types followed by the residual's are a permutation of the statement's. -/
theorem Stmt.liftP_initTypes_perm {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    List.Perm (Cmds.initTypes (Stmt.liftInitsInLoopBody s).1
      ++ Block.initTypes (Stmt.liftInitsInLoopBody s).2) (Stmt.initTypes s) := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Cmds.initTypes, Cmd.initTypes, Block.initTypes,
          Stmt.initTypes, HasInitTypesImp.initTypes]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initTypes, Block.initTypes, List.append_nil]
      exact Block.liftP_initTypes_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initTypes, Block.initTypes, List.append_nil,
        Cmds.initTypes_append]
      have ht := Block.liftP_initTypes_perm tss
      have he := Block.liftP_initTypes_perm ess
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact ht.append he
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.initTypes, Block.initTypes, Stmt.initTypes]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.initTypes, Block.initTypes, Stmt.initTypes]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.initTypes, Block.initTypes, Stmt.initTypes]
  termination_by sizeOf s

/-- Lifting a block permutes its declared init types: the harvested prelude's types
followed by the residual's are a permutation of the block's. -/
theorem Block.liftP_initTypes_perm {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    List.Perm (Cmds.initTypes (Block.liftInitsInLoopBody ss).1
      ++ Block.initTypes (Block.liftInitsInLoopBody ss).2) (Block.initTypes ss) := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.initTypes, Block.initTypes]
  | s :: rest =>
      simp only [Block.liftInitsInLoopBody, Cmds.initTypes_append, Block.initTypes_append,
        Block.initTypes]
      have hs := Stmt.liftP_initTypes_perm s
      have hr := Block.liftP_initTypes_perm rest
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact hs.append hr
  termination_by sizeOf ss
end

mutual
/-- Hoisting a statement permutes its declared init types. -/
theorem Stmt.hoistP_initTypes_perm {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    List.Perm (Block.initTypes (Stmt.hoistLoopPrefixInits s)) (Stmt.initTypes s) := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.hoistLoopPrefixInits, Block.initTypes, Stmt.initTypes,
      Cmd.initTypes, HasInitTypesImp.initTypes]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initTypes, Block.initTypes, List.append_nil]
      exact Block.hoistP_initTypes_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initTypes, Block.initTypes, List.append_nil]
      exact (Block.hoistP_initTypes_perm tss).append (Block.hoistP_initTypes_perm ess)
  | .loop g m inv body md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.initTypes_append, Block.initTypes,
        Stmt.initTypes, List.append_nil, Block.initTypes_map_cmd]
      exact (Block.liftP_initTypes_perm (Block.hoistLoopPrefixInits body)).trans
        (Block.hoistP_initTypes_perm body)
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.initTypes, Stmt.initTypes]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.initTypes, Stmt.initTypes]
  termination_by sizeOf s

/-- Hoisting a block permutes its declared init types. -/
theorem Block.hoistP_initTypes_perm {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    List.Perm (Block.initTypes (Block.hoistLoopPrefixInits ss)) (Block.initTypes ss) := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.initTypes]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.initTypes_append, Block.initTypes]
      exact (Stmt.hoistP_initTypes_perm s).append (Block.hoistP_initTypes_perm rest)
  termination_by sizeOf ss
end

/-- `InitTypesInhabited` transports from a source block to its hoist: every
hoisted init type is (a permutation of) a source init type. -/
theorem Block.hoistP_initTypesInhabited {P : PureExpr} [HasFvars P] [HasVal P]
    {f : P.Factory} {ss : List (Stmt P (Cmd P))}
    (h : Block.InitTypesInhabited f ss) :
    Block.InitTypesInhabited f (Block.hoistLoopPrefixInits ss) := by
  intro ty hty
  exact h ty ((Block.hoistP_initTypes_perm ss).mem_iff.mp hty)

/-! The declared type of every harvestable typed init is a deep init type. -/
mutual
/-- Every type recorded in a statement's `typedInitVars` is one of its declared init
types. -/
theorem Stmt.typedInitVars_snd_sub_initTypes {P : PureExpr} (s : Stmt P (Cmd P)) :
    ∀ p ∈ Stmt.typedInitVars s, p.2 ∈ Stmt.initTypes s := by
  match s with
  | .cmd c =>
      intro p hp
      cases c <;>
        simp_all [Stmt.typedInitVars, Stmt.initTypes, HasInitTypesImp.initTypes, Cmd.initTypes]
  | .block lbl bss md =>
      intro p hp
      simp only [Stmt.typedInitVars, Stmt.initTypes] at hp ⊢
      exact Block.typedInitVars_snd_sub_initTypes bss p hp
  | .ite g tss ess md =>
      intro p hp
      simp only [Stmt.typedInitVars, Stmt.initTypes, List.mem_append] at hp ⊢
      rcases hp with h | h
      · exact Or.inl (Block.typedInitVars_snd_sub_initTypes tss p h)
      · exact Or.inr (Block.typedInitVars_snd_sub_initTypes ess p h)
  | .loop g m inv body md =>
      intro p hp; simp only [Stmt.typedInitVars] at hp; exact absurd hp List.not_mem_nil
  | .exit lbl md =>
      intro p hp; simp only [Stmt.typedInitVars] at hp; exact absurd hp List.not_mem_nil
  | .typeDecl t md =>
      intro p hp; simp only [Stmt.typedInitVars] at hp; exact absurd hp List.not_mem_nil
  termination_by sizeOf s

/-- Every type recorded in a block's `typedInitVars` is one of its declared init
types. -/
theorem Block.typedInitVars_snd_sub_initTypes {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    ∀ p ∈ Block.typedInitVars ss, p.2 ∈ Block.initTypes ss := by
  match ss with
  | [] => intro p hp; simp only [Block.typedInitVars] at hp; exact absurd hp List.not_mem_nil
  | s :: rest =>
      intro p hp
      simp only [Block.typedInitVars, Block.initTypes, List.mem_append] at hp ⊢
      rcases hp with h | h
      · exact Or.inl (Stmt.typedInitVars_snd_sub_initTypes s p h)
      · exact Or.inr (Block.typedInitVars_snd_sub_initTypes rest p h)
  termination_by sizeOf ss
end

/-! ## Same-name hoist output shape lemmas (the pipeline-wiring facts).

The same-name pass keeps every loop head (`g`/`m`/`inv`) verbatim and emits the
hoisted body inits as a sibling `.cmd`-havoc prelude, so the shape predicates the
downstream S2U pass consumes are all preserved (or, for `loopBodyNoInits`, newly
established).  Each lemma mirrors the corresponding fresh-name preservation lemma
but is structurally simpler: there is no rename, so the residual is the plain
`liftInitsInLoopBody` output and the havoc prelude is a `.cmd` list. -/

/-! ### `noNondetGuards` is preserved (same-name). -/
mutual
/-- Lifting a loop body's inits out of it neither introduces nor removes a
    nondeterministic guard: the residual statement has one exactly when the
    original did. Guards are copied verbatim, and the harvested inits become
    commands, which carry no guard. -/
theorem Stmt.liftP_res_noNondetGuards {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.noNondetGuards (Stmt.liftInitsInLoopBody s).2 = Stmt.noNondetGuards s := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noNondetGuards, Stmt.noNondetGuards]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true]
      exact Block.liftP_res_noNondetGuards bss
  | .ite g tss ess md =>
      cases g <;>
        simp [Stmt.liftInitsInLoopBody, Block.noNondetGuards, Stmt.noNondetGuards,
          Block.liftP_res_noNondetGuards tss, Block.liftP_res_noNondetGuards ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.noNondetGuards]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noNondetGuards, Stmt.noNondetGuards]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noNondetGuards, Stmt.noNondetGuards]
  termination_by sizeOf s

/-- Block-level counterpart: the residual block has a nondeterministic guard
    exactly when the original block did. -/
theorem Block.liftP_res_noNondetGuards {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.noNondetGuards (Block.liftInitsInLoopBody ss).2 = Block.noNondetGuards ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noNondetGuards]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.noNondetGuards_append,
          Stmt.liftP_res_noNondetGuards s, Block.liftP_res_noNondetGuards rest, Block.noNondetGuards]
  termination_by sizeOf ss
end

mutual
/-- Hoisting the prefix inits of every loop in a statement free of
    nondeterministic guards leaves it free of them: the prelude it emits is a
    list of havoc commands, and every guard is carried over unchanged. -/
theorem Stmt.hoistP_noNondetGuards {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.noNondetGuards s = true)
    :
    Block.noNondetGuards (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.noNondetGuards, Stmt.noNondetGuards]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true]
      exact Block.hoistP_noNondetGuards bss (by simpa [Stmt.noNondetGuards] using h)
  | .ite g tss ess md =>
      cases g with
      | det e =>
          simp only [Stmt.noNondetGuards, Bool.and_eq_true] at h
          simp only [Stmt.hoistLoopPrefixInits, Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true]
          rw [Block.hoistP_noNondetGuards tss h.1, Block.hoistP_noNondetGuards ess h.2]; rfl
      | nondet => exact absurd h (by simp [Stmt.noNondetGuards])
  | .loop g m inv body md =>
      cases g with
      | nondet => exact absurd h (by simp [Stmt.noNondetGuards])
      | det g' =>
        have h_body : Block.noNondetGuards body = true := by
          simpa [Stmt.noNondetGuards] using h
        have h_hb : Block.noNondetGuards (Block.hoistLoopPrefixInits body) = true :=
          Block.hoistP_noNondetGuards body h_body
        simp only [Stmt.hoistLoopPrefixInits, Block.noNondetGuards_append]
        rw [Block.noNondetGuards_map_cmd']
        simp only [Block.noNondetGuards, Stmt.noNondetGuards, Bool.true_and, Bool.and_true]
        rw [Block.liftP_res_noNondetGuards (Block.hoistLoopPrefixInits body)]; exact h_hb
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.noNondetGuards, Stmt.noNondetGuards]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.noNondetGuards, Stmt.noNondetGuards]
  termination_by sizeOf s

/-- Block-level counterpart, and the form the pipeline uses: hoisting preserves
    freedom from nondeterministic guards for a whole block. -/
theorem Block.hoistP_noNondetGuards {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h : Block.noNondetGuards
    ss = true) :
    Block.noNondetGuards (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.noNondetGuards]
  | s :: rest =>
      simp only [Block.noNondetGuards, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.noNondetGuards_append,
          Stmt.hoistP_noNondetGuards s h.1, Block.hoistP_noNondetGuards rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `loopHasNoInvariants` is preserved (same-name; the loop's `inv` is verbatim). -/
mutual
/-- A statement's lift residual has no loop invariants exactly when the statement
has none. -/
theorem Stmt.liftP_res_loopHasNoInvariants {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.loopHasNoInvariants (Stmt.liftInitsInLoopBody s).2 = Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants,
          Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      exact Block.liftP_res_loopHasNoInvariants bss
  | .ite g tss ess md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
        Block.liftP_res_loopHasNoInvariants tss, Block.liftP_res_loopHasNoInvariants ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

/-- A block's lift residual has no loop invariants exactly when the block has none. -/
theorem Block.liftP_res_loopHasNoInvariants {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (Block.liftInitsInLoopBody ss).2 = Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.loopHasNoInvariants]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.loopHasNoInvariants_append,
          Stmt.liftP_res_loopHasNoInvariants s, Block.liftP_res_loopHasNoInvariants rest,
          Block.loopHasNoInvariants]
  termination_by sizeOf ss
end

mutual
/-- Hoisting preserves `loopHasNoInvariants` for a statement. -/
theorem Stmt.hoistP_loopHasNoInvariants {P : PureExpr} (s : Stmt P (Cmd P))
    (h : Stmt.loopHasNoInvariants s = true) :
    Block.loopHasNoInvariants (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      exact Block.hoistP_loopHasNoInvariants bss (by simpa [Stmt.loopHasNoInvariants] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      rw [Block.hoistP_loopHasNoInvariants tss h.1, Block.hoistP_loopHasNoInvariants ess h.2]; rfl
  | .loop g m inv body md =>
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      have h_body : Block.loopHasNoInvariants body = true := h.2
      have h_hb : Block.loopHasNoInvariants (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_loopHasNoInvariants body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants_append]
      rw [Block.loopHasNoInvariants_map_cmd']
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.true_and, Bool.and_true,
        Bool.and_eq_true]
      have h_res : Block.loopHasNoInvariants
          (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 = true := by
        rw [Block.liftP_res_loopHasNoInvariants (Block.hoistLoopPrefixInits body)]; exact h_hb
      exact ⟨h.1, h_res⟩
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

/-- Hoisting preserves `loopHasNoInvariants` for a block. -/
theorem Block.hoistP_loopHasNoInvariants {P : PureExpr} (ss : List (Stmt P (Cmd P)))
    (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.loopHasNoInvariants]
  | s :: rest =>
      simp only [Block.loopHasNoInvariants, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.loopHasNoInvariants_append,
          Stmt.hoistP_loopHasNoInvariants s h.1, Block.hoistP_loopHasNoInvariants rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `noMeasureLoops` is preserved (same-name; the loop's `m` is verbatim). -/
mutual
/-- A statement's lift residual has no loop measures exactly when the statement has
none. -/
theorem Stmt.liftP_res_noMeasureLoops {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.noMeasureLoops (Stmt.liftInitsInLoopBody s).2 = Stmt.noMeasureLoops s := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true]
      exact Block.liftP_res_noMeasureLoops bss
  | .ite g tss ess md =>
      simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops,
        Block.liftP_res_noMeasureLoops tss, Block.liftP_res_noMeasureLoops ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  termination_by sizeOf s

/-- A block's lift residual has no loop measures exactly when the block has none. -/
theorem Block.liftP_res_noMeasureLoops {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.noMeasureLoops (Block.liftInitsInLoopBody ss).2 = Block.noMeasureLoops ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noMeasureLoops]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.noMeasureLoops_append,
          Stmt.liftP_res_noMeasureLoops s, Block.liftP_res_noMeasureLoops rest,
          Block.noMeasureLoops]
  termination_by sizeOf ss
end

mutual
/-- Hoisting preserves `noMeasureLoops` for a statement. -/
theorem Stmt.hoistP_noMeasureLoops {P : PureExpr} (s : Stmt P (Cmd P))
    (h : Stmt.noMeasureLoops s = true) :
    Block.noMeasureLoops (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops,
          Bool.and_true]
      exact Block.hoistP_noMeasureLoops bss (by simpa [Stmt.noMeasureLoops] using h)
  | .ite g tss ess md =>
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops,
          Bool.and_true]
      rw [Block.hoistP_noMeasureLoops tss h.1, Block.hoistP_noMeasureLoops ess h.2]; rfl
  | .loop g m inv body md =>
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      have h_body : Block.noMeasureLoops body = true := h.2
      have h_hb : Block.noMeasureLoops (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_noMeasureLoops body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops_append]
      rw [Block.noMeasureLoops_map_cmd']
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.true_and, Bool.and_true,
        Bool.and_eq_true]
      have h_res : Block.noMeasureLoops
          (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 = true := by
        rw [Block.liftP_res_noMeasureLoops (Block.hoistLoopPrefixInits body)]; exact h_hb
      exact ⟨h.1, h_res⟩
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  termination_by sizeOf s

/-- Hoisting preserves `noMeasureLoops` for a block. -/
theorem Block.hoistP_noMeasureLoops {P : PureExpr} (ss : List (Stmt P (Cmd P)))
    (h : Block.noMeasureLoops ss = true) :
    Block.noMeasureLoops (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.noMeasureLoops]
  | s :: rest =>
      simp only [Block.noMeasureLoops, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.noMeasureLoops_append,
          Stmt.hoistP_noMeasureLoops s h.1, Block.hoistP_noMeasureLoops rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `loopBodyNoInits` is established (same-name), unconditionally. -/
/-- The hoist of any block satisfies `loopBodyNoInits`. -/
theorem Block.hoistP_loopBodyNoInits {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistP_allLoop_uncond ss

/-! ### `getBlockLabels` is preserved (same-name; no rename, `.cmd` prelude has no labels). -/

mutual
/-- Lifting keeps a statement's block labels. -/
theorem Stmt.liftP_res_getBlockLabels {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.getBlockLabels (Stmt.liftInitsInLoopBody s).2 = Block.getBlockLabels [s] := by
  match s with
  | .cmd c =>
      cases c <;>
        simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_cmd_cons]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_block_cons,
        Block.liftP_res_getBlockLabels bss]
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_ite_cons,
        Block.liftP_res_getBlockLabels tss, Block.liftP_res_getBlockLabels ess]
  | .loop g m inv body md => rw [Stmt.liftInitsInLoopBody]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.getBlockLabels]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.getBlockLabels]
  termination_by sizeOf s

/-- Lifting keeps a block's block labels. -/
theorem Block.liftP_res_getBlockLabels {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.liftInitsInLoopBody ss).2 = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.liftP_res_getBlockLabels s, Block.liftP_res_getBlockLabels rest]
  termination_by sizeOf ss
end

mutual
/-- Hoisting keeps a statement's block labels. -/
theorem Stmt.hoistP_getBlockLabels {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.getBlockLabels (Stmt.hoistLoopPrefixInits s) = Block.getBlockLabels [s] := by
  match s with
  | .cmd c => rw [Stmt.hoistLoopPrefixInits]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_block_cons,
        Block.hoistP_getBlockLabels bss]
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_ite_cons,
        Block.hoistP_getBlockLabels tss, Block.hoistP_getBlockLabels ess]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_append, Block.getBlockLabels_map_cmd,
          List.nil_append]
      simp only [Block.getBlockLabels_loop_cons,
        Block.liftP_res_getBlockLabels (Block.hoistLoopPrefixInits body),
        Block.hoistP_getBlockLabels body]
  | .exit lbl md => rw [Stmt.hoistLoopPrefixInits]
  | .typeDecl t md => rw [Stmt.hoistLoopPrefixInits]
  termination_by sizeOf s

/-- Hoisting keeps a block's block labels. -/
theorem Block.hoistP_getBlockLabels {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.hoistLoopPrefixInits ss) = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInits, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.hoistP_getBlockLabels s, Block.hoistP_getBlockLabels rest]
  termination_by sizeOf ss
end

end LoopInitHoistProducerProps

end Imperative

end -- public section

public section

namespace Imperative

open LoopInitHoistProducerProps

/-!
# Well-formedness preservation for loop-init hoisting

This section owns flow-sensitive well-formedness preservation for
`Block.hoistLoopPrefixInits`. A lifted declaration becomes a prelude declaration
and a residual assignment. Global `uniqueInits` prevents moved declarations
from colliding, while the loop guard, measure, and invariant checks remain valid
when the prelude extends the set of defined variables. Definition and init-type
multisets are preserved independently.
-/


/-- `target` defines at least what `source` defines, and agrees with `source` on
`protectedVars`. -/
private def DefinedRel {P : PureExpr} [HasFvars P]
    (protectedVars : List P.Ident) (source target : P.Ident → Bool) : Prop :=
  (∀ x, source x = true → target x = true) ∧
  (∀ x ∈ protectedVars, target x = source x)

mutual

/-- Def-use well-formedness is stable when entry definedness grows, provided it
is unchanged on all names initialized by the statement.  This local lemma is
used when an earlier Hoist prelude becomes visible to a later residual. -/
private theorem Stmt.defUseWellFormed_of_definedRel {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (source target declared : P.Ident → Bool)
    (hrel : DefinedRel (Stmt.initVars s) source target)
    (hdu : Stmt.defUseWellFormed source declared s = true) :
    Stmt.defUseWellFormed target declared s = true := by
  match s with
  | .cmd c =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
      refine ⟨⟨⟨List.all_mono hrel.1 hdu.1.1.1, List.all_mono hrel.1 hdu.1.1.2⟩, ?_⟩, hdu.2⟩
      have hfresh := hdu.1.2
      rw [List.all_eq_true] at hfresh ⊢
      intro x hx
      have heq : target x = source x := hrel.2 x (by
        show x ∈ Stmt.initVars (.cmd c)
        exact hx)
      rw [heq]
      exact hfresh x hx
  | .block lbl bss md =>
      exact Block.defUseWellFormed_of_definedRel bss source target declared
        (by simpa [Stmt.initVars] using hrel) hdu
  | .ite g tss ess md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
      refine ⟨⟨⟨List.all_mono hrel.1 hdu.1.1.1, hdu.1.1.2⟩, ?_⟩, ?_⟩
      · exact Block.defUseWellFormed_of_definedRel tss source target declared
          ⟨hrel.1, fun x hx => hrel.2 x (by
            rw [Stmt.initVars_ite, List.mem_append]
            exact Or.inl hx)⟩ hdu.1.2
      · exact Block.defUseWellFormed_of_definedRel ess source target declared
          ⟨hrel.1, fun x hx => hrel.2 x (by
            rw [Stmt.initVars_ite, List.mem_append]
            exact Or.inr hx)⟩ hdu.2
  | .loop g m inv body md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
      refine ⟨⟨⟨⟨⟨⟨List.all_mono hrel.1 hdu.1.1.1.1.1.1, hdu.1.1.1.1.1.2⟩,
        List.all_mono hrel.1 hdu.1.1.1.1.2⟩, hdu.1.1.1.2⟩,
        List.all_mono hrel.1 hdu.1.1.2⟩, hdu.1.2⟩, ?_⟩
      exact Block.defUseWellFormed_of_definedRel body source target declared
        (by simpa [Stmt.initVars] using hrel) hdu.2
  | .exit lbl md => exact hdu
  | .typeDecl t md => exact hdu
  termination_by sizeOf s

/-- Block form of `Stmt.defUseWellFormed_of_definedRel`: def-use well-formedness is
stable when entry definedness grows without changing the block's init names. -/
private theorem Block.defUseWellFormed_of_definedRel {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (source target declared : P.Ident → Bool)
    (hrel : DefinedRel (Block.initVars ss) source target)
    (hdu : Block.defUseWellFormed source declared ss = true) :
    Block.defUseWellFormed target declared ss = true := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
      have hhead : Stmt.defUseWellFormed target declared s = true :=
        Stmt.defUseWellFormed_of_definedRel s source target declared
          ⟨hrel.1, fun x hx => hrel.2 x (by
            rw [Block.initVars_cons, List.mem_append]
            exact Or.inl hx)⟩ hdu.1
      let source' := fun x => source x || decide (x ∈ Stmt.definedVars s true)
      let target' := fun x => target x || decide (x ∈ Stmt.definedVars s true)
      have htailRel : DefinedRel (Block.initVars rest) source' target' := by
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [source', target'] at hx ⊢
          rw [Bool.or_eq_true] at hx ⊢
          exact hx.elim (fun hs => Or.inl (hrel.1 x hs)) Or.inr
        · intro x hx
          simp only [source', target']
          rw [hrel.2 x (by
            rw [Block.initVars_cons, List.mem_append]
            exact Or.inr hx)]
      exact ⟨hhead, Block.defUseWellFormed_of_definedRel rest source' target' declared
        htailRel hdu.2⟩
  termination_by sizeOf ss

end

end Imperative

end -- public section

public section

namespace Imperative
namespace LoopInitHoistWF


open LoopInitHoistProducerProps

/-- Wrapping commands as `.cmd` statements keeps their unscoped defined variables. -/
private theorem Block.definedVars_map_cmd_true {P : PureExpr} [HasFvars P]
    (cs : List (Cmd P)) :
    Block.definedVars (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) true =
      Cmds.definedVars cs := by
  induction cs with
  | nil => simp [Block.definedVars, Cmds.definedVars]
  | cons c rest ih =>
      cases c <;>
        simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
          Cmd.definedVars, Cmds.definedVars, ih]

/-- A statement's lift residual defines no unscoped variables: the lift turns each
unscoped `init` into a `set`. -/
private theorem Stmt.lift_res_definedVars_true_nil {P : PureExpr} [HasFvars P]
    (s : Stmt P (Cmd P)) :
    Block.definedVars (Stmt.liftInitsInLoopBody s).2 true = [] := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.definedVars,
        Stmt.definedVars, HasVarsImp.definedVars, Cmd.definedVars]
  | .block lbl bss md =>
      simp [Stmt.liftInitsInLoopBody, Block.definedVars, Stmt.definedVars]
  | .ite g tss ess md =>
      simp [Stmt.liftInitsInLoopBody, Block.definedVars, Stmt.definedVars]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Block.definedVars, Stmt.definedVars]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBody, Block.definedVars, Stmt.definedVars]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Block.definedVars, Stmt.definedVars]

/-- Every unscoped variable a statement defines is defined by the commands the lift
harvests from it. -/
private theorem Stmt.definedVars_true_mem_lift_harvested {P : PureExpr}
    [HasFvars P] (s : Stmt P (Cmd P)) {x : P.Ident}
    (hx : x ∈ Stmt.definedVars s true) :
    x ∈ Cmds.definedVars (Stmt.liftInitsInLoopBody s).1 := by
  match s with
  | .cmd c =>
      cases c <;>
        simp_all [Stmt.definedVars, Stmt.liftInitsInLoopBody,
          Cmd.definedVars, HasVarsImp.definedVars, Cmds.definedVars]
  | .block .. | .ite .. | .loop .. | .exit .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hx

/-- Definedness relation for a lift residual: `target` defines at least what `source`
defines, agrees with `source` on the residual's init names, and defines every
name the harvested prelude `hs` defines. -/
private def LiftDefinedRel {P : PureExpr} [HasFvars P]
    (source target : P.Ident → Bool) (hs : List (Cmd P))
    (residual : List (Stmt P (Cmd P))) : Prop :=
  (∀ x, source x = true → target x = true) ∧
  (∀ x ∈ Block.initVars residual, target x = source x) ∧
  (∀ x ∈ Cmds.definedVars hs, target x = true)

/-- A prelude of nondeterministic `init`s with distinct, initially undefined names is
def-use well-formed. -/
private theorem prelude_defUseWellFormed {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (cs : List (Cmd P)) (defined declared : P.Ident → Bool)
    (hshape : ∀ c ∈ cs, ∃ x ty md, c = .init x ty .nondet md)
    (hnone : ∀ x ∈ Cmds.definedVars cs, defined x = false)
    (hnodup : (Cmds.definedVars cs).Nodup) :
    Block.defUseWellFormed defined declared
      (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true := by
  induction cs generalizing defined with
  | nil => rfl
  | cons c rest ih =>
      obtain ⟨x, ty, md, rfl⟩ := hshape c List.mem_cons_self
      have hdefsEq : Cmds.definedVars
          (Cmd.init x ty .nondet md :: rest) = x :: Cmds.definedVars rest := by
        simp [Cmds.definedVars, Cmd.definedVars]
      rw [hdefsEq] at hnodup hnone
      rw [List.nodup_cons] at hnodup
      have hxnone : defined x = false := hnone x List.mem_cons_self
      have hrestnone : ∀ y ∈ Cmds.definedVars rest,
          (defined y || decide (y = x)) = false := by
        intro y hy
        have hy_none : defined y = false := hnone y (List.mem_cons_of_mem _ hy)
        have hy_ne : y ≠ x := by
          intro h
          apply hnodup.1
          rw [← h]
          exact hy
        simp [hy_none, hy_ne]
      have hrestshape : ∀ c ∈ rest, ∃ x ty md, c = .init x ty .nondet md := by
        intro c hc
        exact hshape c (List.mem_cons_of_mem _ hc)
      simp only [List.map_cons, Block.defUseWellFormed, Stmt.defUseWellFormed,
        Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars, Cmd.getOps,
        HasVarsImp.readVars, HasVarsImp.modifiedVars, HasVarsImp.definedVars,
        HasOpsImp.getOps, ExprOrNondet.getVars,
        List.all_nil, Bool.and_self, Bool.true_and,
        List.all_cons, Bool.and_true, Bool.not_eq_true]
      rw [Bool.and_eq_true]
      have hnext :
          (fun n => defined n || decide
            (n ∈ Stmt.definedVars
              (.cmd (Cmd.init x ty .nondet md) : Stmt P (Cmd P)) true)) =
          (fun y => defined y || decide (y = x)) := by
        funext y
        simp [Stmt.definedVars, HasVarsImp.definedVars, Cmd.definedVars]
      rw [hnext]
      have hxnone' : decide (defined x = false) = true := by simp [hxnone]
      exact ⟨hxnone', ih (fun y => defined y || decide (y = x)) hrestshape
        hrestnone hnodup.2⟩

mutual

/-- The lift residual of a def-use well-formed statement with unique inits is def-use
well-formed once the harvested prelude has run (`LiftDefinedRel`). -/
private theorem Stmt.lift_res_defUseWellFormed {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (source target declared : P.Ident → Bool)
    (hrel : LiftDefinedRel source target
      (Stmt.liftInitsInLoopBody s).1 (Stmt.liftInitsInLoopBody s).2)
    (hdu : Stmt.defUseWellFormed source declared s = true)
    (huniq : (Stmt.initVars s).Nodup) :
    Block.defUseWellFormed target declared (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd (.init x ty rhs md) =>
      rw [Stmt.liftInitsInLoopBody] at hrel ⊢
      simp only [] at hrel ⊢
      have hxTarget : target x = true := hrel.2.2 x (by
        simp [Cmds.definedVars, Cmd.definedVars])
      simp only [Block.defUseWellFormed, Bool.and_true]
      rw [Stmt.defUseWellFormed]
      simp only [HasVarsImp.readVars, Cmd.getVars,
        HasVarsImp.modifiedVars, Cmd.modifiedVars,
        HasVarsImp.definedVars, Cmd.definedVars,
        HasOpsImp.getOps, Cmd.getOps,
        List.all_cons, List.all_nil, Bool.and_true]
      simp only [Stmt.defUseWellFormed,
        HasVarsImp.readVars, Cmd.getVars,
        HasVarsImp.modifiedVars, Cmd.modifiedVars,
        HasVarsImp.definedVars, Cmd.definedVars,
        HasOpsImp.getOps, Cmd.getOps,
        List.all_cons, List.all_nil, Bool.and_true] at hdu
      simp only [Bool.and_eq_true] at hdu ⊢
      refine ⟨⟨List.all_mono hrel.1 hdu.1.1, hxTarget⟩, ?_⟩
      cases rhs <;> exact hdu.2
  | .cmd (.set x rhs md) =>
      simpa [Stmt.liftInitsInLoopBody, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.cmd (.set x rhs md)) source target declared
          ⟨hrel.1, by
            intro y hy
            simp [Stmt.initVars, Stmt.definedVars, HasVarsImp.definedVars,
              Cmd.definedVars] at hy⟩ hdu
  | .cmd (.assert l e md) =>
      simpa [Stmt.liftInitsInLoopBody, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.cmd (.assert l e md)) source target declared
          ⟨hrel.1, by
            intro y hy
            simp [Stmt.initVars, Stmt.definedVars, HasVarsImp.definedVars,
              Cmd.definedVars] at hy⟩ hdu
  | .cmd (.assume l e md) =>
      simpa [Stmt.liftInitsInLoopBody, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.cmd (.assume l e md)) source target declared
          ⟨hrel.1, by
            intro y hy
            simp [Stmt.initVars, Stmt.definedVars, HasVarsImp.definedVars,
              Cmd.definedVars] at hy⟩ hdu
  | .cmd (.cover l e md) =>
      simpa [Stmt.liftInitsInLoopBody, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.cmd (.cover l e md)) source target declared
          ⟨hrel.1, by
            intro y hy
            simp [Stmt.initVars, Stmt.definedVars, HasVarsImp.definedVars,
              Cmd.definedVars] at hy⟩ hdu
  | .block lbl bss md =>
      rcases hLift : Block.liftInitsInLoopBody bss with ⟨hs, residual⟩
      simp only [Stmt.liftInitsInLoopBody, hLift] at hrel ⊢
      have hbaseRel : LiftDefinedRel source target
          (Block.liftInitsInLoopBody bss).1 (Block.liftInitsInLoopBody bss).2 := by
        rw [hLift]
        refine ⟨hrel.1, ?_, hrel.2.2⟩
        intro x hx
        apply hrel.2.1 x
        simp only [Block.initVars, Block.definedVars, Stmt.definedVars, Bool.false_eq_true,
          ↓reduceIte, List.append_nil]
        exact hx
      have hb := Block.lift_res_defUseWellFormed bss source target declared
        hbaseRel hdu huniq
      rw [hLift] at hb
      simpa [Block.defUseWellFormed, Stmt.defUseWellFormed] using hb
  | .ite g tss ess md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have huniq' : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa [Stmt.initVars] using huniq
      have htRel : LiftDefinedRel source target
          (Block.liftInitsInLoopBody tss).1 (Block.liftInitsInLoopBody tss).2 := by
        refine ⟨hrel.1, ?_, ?_⟩
        · intro x hx
          exact hrel.2.1 x (by
            simp only [Stmt.liftInitsInLoopBody, Block.initVars_cons,
              Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
              List.mem_append]
            exact Or.inl hx)
        · intro x hx
          apply hrel.2.2 x
          simp only [Stmt.liftInitsInLoopBody, Cmds.definedVars_append,
            List.mem_append]
          exact Or.inl hx
      have heRel : LiftDefinedRel source target
          (Block.liftInitsInLoopBody ess).1 (Block.liftInitsInLoopBody ess).2 := by
        refine ⟨hrel.1, ?_, ?_⟩
        · intro x hx
          exact hrel.2.1 x (by
            simp only [Stmt.liftInitsInLoopBody, Block.initVars_cons,
              Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
              List.mem_append]
            exact Or.inr hx)
        · intro x hx
          apply hrel.2.2 x
          simp only [Stmt.liftInitsInLoopBody, Cmds.definedVars_append,
            List.mem_append]
          exact Or.inr hx
      have ht := Block.lift_res_defUseWellFormed tss source target declared htRel
        hdu.1.2 (List.nodup_append.mp huniq').1
      have he := Block.lift_res_defUseWellFormed ess source target declared heRel
        hdu.2 (List.nodup_append.mp huniq').2.1
      simp only [Stmt.liftInitsInLoopBody, Block.defUseWellFormed,
        Stmt.defUseWellFormed, Bool.and_eq_true, Bool.and_true]
      exact ⟨⟨⟨List.all_mono hrel.1 hdu.1.1.1, hdu.1.1.2⟩, ht⟩, he⟩
  | .loop g m inv body md =>
      simpa [Stmt.liftInitsInLoopBody, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.loop g m inv body md)
          source target declared
          ⟨hrel.1, by simpa [Stmt.liftInitsInLoopBody, LiftDefinedRel] using hrel.2.1⟩ hdu
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBody, Block.defUseWellFormed, Stmt.defUseWellFormed]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Block.defUseWellFormed, Stmt.defUseWellFormed]
  termination_by sizeOf s

/-- The lift residual of a def-use well-formed block with unique inits is def-use
well-formed once the harvested prelude has run (`LiftDefinedRel`). -/
private theorem Block.lift_res_defUseWellFormed {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (source target declared : P.Ident → Bool)
    (hrel : LiftDefinedRel source target
      (Block.liftInitsInLoopBody ss).1 (Block.liftInitsInLoopBody ss).2)
    (hdu : Block.defUseWellFormed source declared ss = true)
    (huniq : (Block.initVars ss).Nodup) :
    Block.defUseWellFormed target declared (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.defUseWellFormed]
  | s :: rest =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      have huniq' : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa [Block.initVars] using huniq
      have hsRel : LiftDefinedRel source target
          (Stmt.liftInitsInLoopBody s).1 (Stmt.liftInitsInLoopBody s).2 := by
        refine ⟨hrel.1, ?_, ?_⟩
        · intro x hx
          apply hrel.2.1 x
          simp only [Block.liftInitsInLoopBody, Block.initVars_append,
            List.mem_append]
          exact Or.inl hx
        · intro x hx
          apply hrel.2.2 x
          simp only [Block.liftInitsInLoopBody, Cmds.definedVars_append,
            List.mem_append]
          exact Or.inl hx
      have hsdu := Stmt.lift_res_defUseWellFormed s source target declared hsRel
        hdu.1 (List.nodup_append.mp huniq').1
      let source' := fun x => source x || decide (x ∈ Stmt.definedVars s true)
      have hrRel : LiftDefinedRel source' target
          (Block.liftInitsInLoopBody rest).1 (Block.liftInitsInLoopBody rest).2 := by
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          simp only [source'] at hx
          rw [Bool.or_eq_true] at hx
          rcases hx with hx | hx
          · exact hrel.1 x hx
          · exact hrel.2.2 x (by
              simp only [Block.liftInitsInLoopBody, Cmds.definedVars_append,
                List.mem_append]
              exact Or.inl (Stmt.definedVars_true_mem_lift_harvested s
                (of_decide_eq_true hx)))
        · intro x hx
          have hx_source : target x = source x := hrel.2.1 x (by
            simp only [Block.liftInitsInLoopBody, Block.initVars_append,
              List.mem_append]
            exact Or.inr hx)
          have hx_rest_src : x ∈ Block.initVars rest :=
            (Block.liftP_initVars_mem rest x).mp (Or.inr hx)
          have hx_not_head : x ∉ Stmt.initVars s := by
            intro hx_head
            exact (List.nodup_append.mp huniq').2.2 x hx_head x hx_rest_src rfl
          have hx_not_top : x ∉ Stmt.definedVars s true := fun hx_top =>
            hx_not_head (Stmt.definedVars_true_subset_false
              (P := P) (C := Cmd P) (fun c m hm => by
                cases c <;>
                  simp_all [HasVarsImp.definedVars, Cmd.definedVars]) hx_top)
          simp only [source']
          rw [hx_source]
          simp [hx_not_top]
        · intro x hx
          apply hrel.2.2 x
          simp only [Block.liftInitsInLoopBody, Cmds.definedVars_append,
            List.mem_append]
          exact Or.inr hx
      have hrdu := Block.lift_res_defUseWellFormed rest source' target declared hrRel
        hdu.2 (List.nodup_append.mp huniq').2.1
      rw [Block.liftInitsInLoopBody, Block.defUseWellFormed_append]
      rw [Stmt.lift_res_definedVars_true_nil]
      have htarget : (fun x => target x || decide (x ∈ ([] : List P.Ident))) = target := by
        funext x
        simp
      rw [htarget, Bool.and_eq_true]
      exact ⟨hsdu, hrdu⟩
  termination_by sizeOf ss

end

/-- Lifting declarations out of a block preserves flow-sensitive def-use
well-formedness when init names are globally unique. -/
theorem Block.liftInitsInLoopBody_defUseWellFormed {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (defined declared : P.Ident → Bool)
    (hdu : Block.defUseWellFormed defined declared ss = true)
    (huniq : Block.uniqueInits ss) :
    Block.defUseWellFormed defined declared
      ((Block.liftInitsInLoopBody ss).1.map
        (Stmt.cmd : Cmd P → Stmt P (Cmd P)) ++
       (Block.liftInitsInLoopBody ss).2) = true := by
  let hs := (Block.liftInitsInLoopBody ss).1
  let residual := (Block.liftInitsInLoopBody ss).2
  have hperm := Block.liftP_initVars_perm ss
  have hnodup : (Cmds.definedVars hs ++ Block.initVars residual).Nodup := by
    exact hperm.nodup_iff.mpr huniq
  have hpre : Block.defUseWellFormed defined declared
      (hs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true := by
    apply prelude_defUseWellFormed hs defined declared
    · intro c hc
      exact Block.liftP_havocs_nondet ss c (by simpa [hs] using hc)
    · intro x hx
      exact Block.not_defined_of_mem_definedVars hdu
        (hperm.mem_iff.mp (List.mem_append_left _ hx))
    · exact (List.nodup_append.mp hnodup).1
  let afterPrelude := fun x => defined x || decide (x ∈ Cmds.definedVars hs)
  have hrel : LiftDefinedRel defined afterPrelude hs residual := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [afterPrelude, hx]
    · intro x hx
      have hnot : x ∉ Cmds.definedVars hs := by
        intro hh
        exact (List.nodup_append.mp hnodup).2.2 x hh x hx rfl
      change (defined x || decide (x ∈ Cmds.definedVars hs)) = defined x
      rw [decide_eq_false hnot, Bool.or_false]
    · intro x hx
      change (defined x || decide (x ∈ Cmds.definedVars hs)) = true
      rw [decide_eq_true hx, Bool.or_true]
  have hres : Block.defUseWellFormed afterPrelude declared residual = true :=
    Block.lift_res_defUseWellFormed ss defined afterPrelude declared hrel hdu huniq
  rw [Block.defUseWellFormed_append, Block.definedVars_map_cmd_true]
  rw [Bool.and_eq_true]
  exact ⟨hpre, hres⟩

/-- Every unscoped variable a statement defines is still defined, unscoped, by its
hoist. -/
private theorem Stmt.definedVars_true_mem_hoist {P : PureExpr}
    [HasFvars P] (s : Stmt P (Cmd P)) {x : P.Ident}
    (hx : x ∈ Stmt.definedVars s true) :
    x ∈ Block.definedVars (Stmt.hoistLoopPrefixInits s) true := by
  match s with
  | .cmd c =>
      simpa [Stmt.hoistLoopPrefixInits, Block.definedVars] using hx
  | .block .. | .ite .. | .loop .. | .exit .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hx

mutual

/-- Hoisting a def-use well-formed statement with unique inits yields a def-use
well-formed block, from any entry definedness related by `DefinedRel`. -/
private theorem Stmt.hoistLoopPrefixInits_defUseWellFormed_rel {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (source target declared : P.Ident → Bool)
    (hrel : DefinedRel (Stmt.initVars s) source target)
    (hdu : Stmt.defUseWellFormed source declared s = true)
    (huniq : (Stmt.initVars s).Nodup) :
    Block.defUseWellFormed target declared (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c =>
      simpa [Stmt.hoistLoopPrefixInits, Block.defUseWellFormed] using
        Stmt.defUseWellFormed_of_definedRel (.cmd c) source target declared hrel hdu
  | .block lbl bss md =>
      have hb := Block.hoistLoopPrefixInits_defUseWellFormed_rel bss source target declared
        (by simpa [Stmt.initVars] using hrel) hdu (by simpa [Stmt.initVars] using huniq)
      simpa [Stmt.hoistLoopPrefixInits, Block.defUseWellFormed,
        Stmt.defUseWellFormed] using hb
  | .ite g tss ess md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have huniq' : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa [Stmt.initVars] using huniq
      have ht := Block.hoistLoopPrefixInits_defUseWellFormed_rel tss source target declared
        ⟨hrel.1, fun x hx => hrel.2 x (by
          rw [Stmt.initVars_ite, List.mem_append]
          exact Or.inl hx)⟩ hdu.1.2 (List.nodup_append.mp huniq').1
      have he := Block.hoistLoopPrefixInits_defUseWellFormed_rel ess source target declared
        ⟨hrel.1, fun x hx => hrel.2 x (by
          rw [Stmt.initVars_ite, List.mem_append]
          exact Or.inr hx)⟩ hdu.2 (List.nodup_append.mp huniq').2.1
      simp only [Stmt.hoistLoopPrefixInits, Block.defUseWellFormed,
        Stmt.defUseWellFormed, Bool.and_eq_true, Bool.and_true]
      exact ⟨⟨⟨List.all_mono hrel.1 hdu.1.1.1, hdu.1.1.2⟩, ht⟩, he⟩
  | .loop g m inv body md =>
      have hduTarget := Stmt.defUseWellFormed_of_definedRel
        (.loop g m inv body md) source target declared hrel hdu
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hduTarget
      have hbody := Block.hoistLoopPrefixInits_defUseWellFormed_rel
        body target target declared
        ⟨(fun _ h => h), fun _ _ => rfl⟩ hduTarget.2
        (by simpa [Stmt.initVars] using huniq)
      let body₁ := Block.hoistLoopPrefixInits body
      have huniq₁ : Block.uniqueInits body₁ := by
        unfold Block.uniqueInits
        exact (Block.hoistP_initVars_perm body).nodup_iff.mpr
          (by simpa [Stmt.initVars] using huniq)
      have hLift := Block.liftInitsInLoopBody_defUseWellFormed
        body₁ target declared (by simpa [body₁] using hbody) huniq₁
      rcases hEq : Block.liftInitsInLoopBody body₁ with ⟨hs, residual⟩
      rw [hEq] at hLift
      simp only [] at hLift
      rw [Block.defUseWellFormed_append, Bool.and_eq_true] at hLift
      let afterPrelude := fun x => target x || decide
        (x ∈ Block.definedVars
          (hs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) true)
      have hmono : ∀ x, target x = true → afterPrelude x = true := by
        intro x hx
        simp [afterPrelude, hx]
      have hloop : Stmt.defUseWellFormed afterPrelude declared
          (.loop g m inv residual md) = true := by
        simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
        exact ⟨⟨⟨⟨⟨⟨List.all_mono hmono hduTarget.1.1.1.1.1.1,
          hduTarget.1.1.1.1.1.2⟩,
          List.all_mono hmono hduTarget.1.1.1.1.2⟩,
          hduTarget.1.1.1.2⟩,
          List.all_mono hmono hduTarget.1.1.2⟩,
          hduTarget.1.2⟩,
          hLift.2⟩
      rw [Stmt.hoistLoopPrefixInits]
      simp only [body₁, hEq]
      rw [Block.defUseWellFormed_append, Bool.and_eq_true]
      exact ⟨hLift.1, by simpa [afterPrelude, Block.defUseWellFormed] using hloop⟩
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.defUseWellFormed,
      Stmt.defUseWellFormed]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.defUseWellFormed,
      Stmt.defUseWellFormed]
  termination_by sizeOf s

/-- Hoisting a def-use well-formed block with unique inits yields a def-use
well-formed block, from any entry definedness related by `DefinedRel`. -/
private theorem Block.hoistLoopPrefixInits_defUseWellFormed_rel {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (source target declared : P.Ident → Bool)
    (hrel : DefinedRel (Block.initVars ss) source target)
    (hdu : Block.defUseWellFormed source declared ss = true)
    (huniq : (Block.initVars ss).Nodup) :
    Block.defUseWellFormed target declared (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.defUseWellFormed]
  | s :: rest =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      have huniq' : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa [Block.initVars] using huniq
      have hsRel : DefinedRel (Stmt.initVars s) source target :=
        ⟨hrel.1, fun x hx => hrel.2 x (by
          rw [Block.initVars_cons, List.mem_append]
          exact Or.inl hx)⟩
      have hsdu := Stmt.hoistLoopPrefixInits_defUseWellFormed_rel s source target declared
        hsRel hdu.1 (List.nodup_append.mp huniq').1
      let source' := fun x => source x || decide (x ∈ Stmt.definedVars s true)
      let target' := fun x => target x || decide
        (x ∈ Block.definedVars (Stmt.hoistLoopPrefixInits s) true)
      have hrRel : DefinedRel (Block.initVars rest) source' target' := by
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [source', target'] at hx ⊢
          rw [Bool.or_eq_true] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl (hrel.1 x hx)
          · exact Or.inr (by
              have hxmem := of_decide_eq_true hx
              simpa using Stmt.definedVars_true_mem_hoist s hxmem)
        · intro x hx
          have hbase : target x = source x := hrel.2 x (by
            rw [Block.initVars_cons, List.mem_append]
            exact Or.inr hx)
          have hnotSource : x ∉ Stmt.definedVars s true := by
            intro hm
            have hm' := Stmt.definedVars_true_subset_false
              (P := P) (C := Cmd P) (fun c y hy => by
                cases c <;> simp_all [HasVarsImp.definedVars, Cmd.definedVars]) hm
            exact (List.nodup_append.mp huniq').2.2 x hm' x hx rfl
          have hnotTarget : x ∉ Block.definedVars
              (Stmt.hoistLoopPrefixInits s) true := by
            intro hm
            have hm' := Block.definedVars_true_subset_false
              (P := P) (C := Cmd P) (fun c y hy => by
                cases c <;> simp_all [HasVarsImp.definedVars, Cmd.definedVars]) hm
            have hsinit := Stmt.hoistP_initVars_sub s x hm'
            exact (List.nodup_append.mp huniq').2.2 x hsinit x hx rfl
          simp [source', target', hbase, hnotSource, hnotTarget]
      have hrdu := Block.hoistLoopPrefixInits_defUseWellFormed_rel
        rest source' target' declared hrRel hdu.2 (List.nodup_append.mp huniq').2.1
      rw [Block.hoistLoopPrefixInits, Block.defUseWellFormed_append, Bool.and_eq_true]
      exact ⟨hsdu, hrdu⟩
  termination_by sizeOf ss

end

/-- The same-name loop-init Hoist pass preserves flow-sensitive def-use
well-formedness.  `uniqueInits` is the only extra premise: it prevents a moved
prelude declaration from colliding with a later declaration. -/
theorem Block.hoistLoopPrefixInits_defUseWellFormed {P : PureExpr}
    [HasFvars P] [HasOps P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (defined declared : P.Ident → Bool)
    (hdu : Block.defUseWellFormed defined declared ss = true)
    (huniq : Block.uniqueInits ss) :
    Block.defUseWellFormed defined declared (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInits_defUseWellFormed_rel ss defined defined declared
    ⟨(fun _ h => h), fun _ _ => rfl⟩ hdu huniq

/-! ## The annotation check of the hoisted program

The hoisted program is checked against a typing `Γt` that types every variable the source's
typing `Γs` types: a prelude `init y : T := *` adds `y : T` to `Γt` before the loop, where the
source adds it at the body `init` the pass rewrites to `set y`.  `uniqueInits` keeps the
prelude names distinct and away from the variables `Γs` types. -/

section Annotations

variable {P : PureExpr} [HasFvars P]

omit [HasFvars P] in
/-- Extending `Γa` with definitions whose types `Γ` gives keeps `Γ` typing every variable
    `Γa` types. -/
private theorem extend_le_of_typed {Γa Γ : VarTyping P}
    (hle : ∀ x ty, Γa x = some ty → Γ x = some ty) (d : List (P.Ident × P.Ty))
    (hd : ∀ p ∈ d, Γ p.1 = some p.2) :
    ∀ x ty, Γa.extend d x = some ty → Γ x = some ty := by
  intro x ty h
  cases hf : d.find? (fun e => e.1 == x) with
  | some e =>
    simp only [VarTyping.extend, hf, Option.some.injEq] at h
    have hx : e.1 = x := by simpa using List.find?_some hf
    rw [← hx, ← h]
    exact hd e (List.mem_of_find?_eq_some hf)
  | none =>
    simp only [VarTyping.extend, hf] at h
    exact hle x ty h

omit [HasFvars P] in
/-- Extending a typing one definition at a time leaves the variables the definitions do not
    name unchanged. -/
private theorem foldl_extend_of_not_mem (L : List (P.Ident × P.Ty)) (Γ : VarTyping P)
    {x : P.Ident} (hx : x ∉ L.map Prod.fst) :
    L.foldl (fun Γ p => Γ.extend [p]) Γ x = Γ x := by
  induction L generalizing Γ with
  | nil => rfl
  | cons q L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    simp only [List.foldl_cons]
    rw [ih _ hx.2]
    exact VarTyping.extend_of_not_mem (by simpa using hx.1)

omit [HasFvars P] in
/-- Extending a typing one definition at a time, with distinct names, gives each name its
    declared type. -/
private theorem foldl_extend_of_mem (L : List (P.Ident × P.Ty)) (Γ : VarTyping P)
    (hnd : (L.map Prod.fst).Nodup) {p : P.Ident × P.Ty} (hp : p ∈ L) :
    L.foldl (fun Γ p => Γ.extend [p]) Γ p.1 = some p.2 := by
  induction L generalizing Γ with
  | nil => cases hp
  | cons q L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [foldl_extend_of_not_mem L _ hnd.1]
      simp [VarTyping.extend]
    · exact ih _ hnd.2 hp

omit [HasFvars P] in
/-- The names of the typed inits of a command list are its defined variables. -/
private theorem cmds_typedInitVars_fst (cs : List (Cmd P)) :
    (LoopInitHoistProducerProps.Cmds.typedInitVars cs).map Prod.fst = Cmds.definedVars cs := by
  induction cs with
  | nil => simp [LoopInitHoistProducerProps.Cmds.typedInitVars, Cmds.definedVars]
  | cons c cs ih =>
    cases c <;> simp [LoopInitHoistProducerProps.Cmds.typedInitVars, Cmds.definedVars,
      Cmd.definedVars, ih]

/-- A prelude of commands that read no annotated variable passes the annotation check, followed
    by `zs`, when `zs` passes it against the typing extended with the prelude's typed inits. -/
private theorem prelude_fvarTypes (cs : List (Cmd P)) (hcs : ∀ c ∈ cs, Cmd.getTypedVars c = [])
    (Γ : VarTyping P) (zs : List (Stmt P (Cmd P)))
    (h : Block.fvarTypesWellAnnotated
      ((LoopInitHoistProducerProps.Cmds.typedInitVars cs).foldl (fun Γ p => Γ.extend [p]) Γ)
      zs) :
    Block.fvarTypesWellAnnotated Γ (cs.map Stmt.cmd ++ zs) := by
  induction cs generalizing Γ with
  | nil => exact h
  | cons c cs ih =>
    have hc := hcs c List.mem_cons_self
    have ih' := ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    refine ⟨fun x ty hm => by
      simp [HasTypedVarsImp.typedReadVars, hc] at hm, ?_⟩
    cases c with
    | init y ty e md => exact ih' _ h
    | set | assert | assume | cover => exact ih' _ h

/-- The typed definitions of a statement are among its init names. -/
private theorem typedDefinedVars_mem_initVars (s : Stmt P (Cmd P)) :
    ∀ p ∈ Stmt.typedDefinedVars s, p.1 ∈ Stmt.initVars s := by
  intro p hp
  match s with
  | .cmd (.init y ty e md) =>
    simp only [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, Cmd.typedDefinedVars,
      List.mem_singleton] at hp
    subst hp
    simp [Stmt.initVars, Stmt.definedVars, HasVarsImp.definedVars, Cmd.definedVars]
  | .cmd (.set ..) | .cmd (.assert ..) | .cmd (.assume ..) | .cmd (.cover ..) | .block ..
  | .ite .. | .loop .. | .exit .. | .typeDecl .. =>
    simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, Cmd.typedDefinedVars] at hp

mutual
/-- The lift of a loop body passes the annotation check against a typing `Γ` that types
    every variable `Γa` types and gives every lifted init its declared type, when the body
    passes it against `Γa`. -/
private theorem Stmt.lift_fvarTypes (s : Stmt P (Cmd P)) (Γa Γ : VarTyping P)
    (hle : ∀ x ty, Γa x = some ty → Γ x = some ty)
    (hty : ∀ p ∈ LoopInitHoistProducerProps.Stmt.typedInitVars s, Γ p.1 = some p.2)
    (h : Stmt.fvarTypesWellAnnotated Γa s) :
    (∀ x ty, Γa.extend (Stmt.typedDefinedVars s) x = some ty → Γ x = some ty) ∧
    ∀ ys, Block.fvarTypesWellAnnotated Γ ys →
      Block.fvarTypesWellAnnotated Γ ((Stmt.liftInitsInLoopBody s).2 ++ ys) := by
  match s with
  | .cmd (.init y ty rhs md) =>
    simp only [Stmt.liftInitsInLoopBody, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at h ⊢
    exact ⟨extend_le_of_typed hle _ hty, fun ys hys => ⟨VarTyping.annotates_mono hle h, hys⟩⟩
  | .cmd (.set ..) | .cmd (.assert ..) | .cmd (.assume ..) | .cmd (.cover ..) =>
    simp only [Stmt.liftInitsInLoopBody, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at h ⊢
    exact ⟨hle, fun ys hys => ⟨VarTyping.annotates_mono hle h, hys⟩⟩
  | .block l bss md =>
    have hb := Block.lift_fvarTypes bss Γa Γ hle hty h [] trivial
    rw [List.append_nil] at hb
    refine ⟨hle, fun ys hys => ?_⟩
    rw [liftP_block_residual]
    exact ⟨hb, hys⟩
  | .ite g tss ess md =>
    simp only [Stmt.fvarTypesWellAnnotated] at h
    have ht := Block.lift_fvarTypes tss Γa Γ hle (fun p hp => hty p (List.mem_append_left _ hp))
      h.2.1 [] trivial
    have he := Block.lift_fvarTypes ess Γa Γ hle (fun p hp => hty p (List.mem_append_right _ hp))
      h.2.2 [] trivial
    rw [List.append_nil] at ht he
    refine ⟨hle, fun ys hys => ?_⟩
    rw [liftP_ite_residual]
    exact ⟨⟨VarTyping.annotates_mono hle h.1, ht, he⟩, hys⟩
  | .loop g m inv body md =>
    simp only [Stmt.liftInitsInLoopBody, List.singleton_append, Block.fvarTypesWellAnnotated]
    exact ⟨hle, fun ys hys => ⟨Stmt.fvarTypesWellAnnotated_mono _ _ _ hle h, hys⟩⟩
  | .exit l md | .typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody, List.singleton_append, Block.fvarTypesWellAnnotated]
    exact ⟨hle, fun ys hys => ⟨trivial, hys⟩⟩
  termination_by sizeOf s

/-- The lift of a loop-body statement list, followed by `ys`, passes the annotation check
    against a typing `Γ` that types every variable `Γa` types and gives every lifted init
    its declared type, when the list passes it against `Γa` and `ys` passes it against
    `Γ`. -/
private theorem Block.lift_fvarTypes (ss : List (Stmt P (Cmd P))) (Γa Γ : VarTyping P)
    (hle : ∀ x ty, Γa x = some ty → Γ x = some ty)
    (hty : ∀ p ∈ LoopInitHoistProducerProps.Block.typedInitVars ss, Γ p.1 = some p.2)
    (h : Block.fvarTypesWellAnnotated Γa ss) :
    ∀ ys, Block.fvarTypesWellAnnotated Γ ys →
      Block.fvarTypesWellAnnotated Γ ((Block.liftInitsInLoopBody ss).2 ++ ys) := by
  match ss with
  | [] =>
    intro ys hys
    simpa [Block.liftInitsInLoopBody] using hys
  | s :: rest =>
    intro ys hys
    rw [liftP_cons_residual, List.append_assoc]
    have hs := Stmt.lift_fvarTypes s Γa Γ hle (fun p hp => hty p (List.mem_append_left _ hp)) h.1
    exact hs.2 _ (Block.lift_fvarTypes rest _ Γ hs.1
      (fun p hp => hty p (List.mem_append_right _ hp)) h.2 ys hys)
  termination_by sizeOf ss
end

mutual
/-- The hoisted statement, followed by `ys`, passes the annotation check against a typing
    `Γt` that types every variable the source's typing `Γs` types, when the statement passes
    it against `Γs`, `Γs` types none of its init names, which are distinct, and `ys` passes it
    against every typing that types every variable `Γs` extended with the statement's
    definitions types. -/
private theorem Stmt.hoist_fvarTypes (s : Stmt P (Cmd P)) (Γs Γt : VarTyping P)
    (hle : ∀ x ty, Γs x = some ty → Γt x = some ty)
    (hfresh : ∀ y ∈ Stmt.initVars s, Γs y = none) (hnd : (Stmt.initVars s).Nodup)
    (h : Stmt.fvarTypesWellAnnotated Γs s) (ys : List (Stmt P (Cmd P)))
    (hys : ∀ Γt' : VarTyping P,
      (∀ x ty, Γs.extend (Stmt.typedDefinedVars s) x = some ty → Γt' x = some ty) →
      Block.fvarTypesWellAnnotated Γt' ys) :
    Block.fvarTypesWellAnnotated Γt (Stmt.hoistLoopPrefixInits s ++ ys) := by
  match s with
  | .cmd c =>
    simp only [Stmt.hoistLoopPrefixInits, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at h ⊢
    exact ⟨VarTyping.annotates_mono hle h, hys _ (VarTyping.extend_mono hle _)⟩
  | .block l bss md =>
    simp only [Stmt.hoistLoopPrefixInits, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at h ⊢
    simp only [Stmt.initVars_block] at hfresh hnd
    exact ⟨Block.hoist_fvarTypes bss Γs Γt hle hfresh hnd h, hys Γt hle⟩
  | .ite g tss ess md =>
    simp only [Stmt.hoistLoopPrefixInits, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at h ⊢
    simp only [Stmt.initVars_ite, List.mem_append, List.nodup_append] at hfresh hnd
    exact ⟨⟨VarTyping.annotates_mono hle h.1,
      Block.hoist_fvarTypes tss Γs Γt hle (fun y hy => hfresh y (.inl hy)) hnd.1 h.2.1,
      Block.hoist_fvarTypes ess Γs Γt hle (fun y hy => hfresh y (.inr hy)) hnd.2.1 h.2.2⟩,
      hys Γt hle⟩
  | .loop g m inv body md =>
    simp only [Stmt.fvarTypesWellAnnotated] at h
    obtain ⟨hg, hm, hi, hb⟩ := h
    simp only [Stmt.initVars_loop] at hfresh hnd
    rcases hL : Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body) with ⟨havocs, body₂⟩
    have hperm₂ := Block.liftP_initVars_perm (Block.hoistLoopPrefixInits body)
    rw [hL] at hperm₂
    have hperm := hperm₂.trans (Block.hoistP_initVars_perm body)
    have hndH : (Cmds.definedVars havocs).Nodup :=
      (List.nodup_append.1 (hperm.nodup_iff.2 hnd)).1
    have hmemH : ∀ y ∈ Cmds.definedVars havocs, y ∈ Block.initVars body :=
      fun y hy => hperm.subset (List.mem_append_left _ hy)
    have hkeys := cmds_typedInitVars_fst havocs
    have hle₁ : ∀ x ty, Γs x = some ty →
        (LoopInitHoistProducerProps.Cmds.typedInitVars havocs).foldl
          (fun Γ p => Γ.extend [p]) Γt x = some ty := by
      intro x ty hx
      have hxn : x ∉ (LoopInitHoistProducerProps.Cmds.typedInitVars havocs).map Prod.fst := by
        rw [hkeys]
        intro hmem
        rw [hfresh x (hmemH x hmem)] at hx
        cases hx
      rw [foldl_extend_of_not_mem _ _ hxn]
      exact hle x ty hx
    have hres := LoopInitHoistProducerProps.Block.liftP_typedInitVars_res
      (Block.hoistLoopPrefixInits body)
    rw [hL] at hres
    have htyped : ∀ p ∈ LoopInitHoistProducerProps.Block.typedInitVars
        (Block.hoistLoopPrefixInits body),
        (LoopInitHoistProducerProps.Cmds.typedInitVars havocs).foldl
          (fun Γ p => Γ.extend [p]) Γt p.1 = some p.2 := by
      intro p hp
      rw [← hres] at hp
      exact foldl_extend_of_mem _ _ (hkeys ▸ hndH) hp
    have hb₁ := Block.hoist_fvarTypes body Γs _ hle₁ hfresh hnd hb
    have hb₂ := Block.lift_fvarTypes (Block.hoistLoopPrefixInits body) _ _ (fun _ _ h => h)
      htyped hb₁ [] trivial
    rw [hL, List.append_nil] at hb₂
    simp only [Stmt.hoistLoopPrefixInits, hL, List.append_assoc]
    refine prelude_fvarTypes havocs (fun c hc => ?_) Γt _ ?_
    · obtain ⟨y, ty, md, rfl⟩ := LoopInitHoistProducerProps.Block.liftP_havocs_nondet _ c
        (by rw [hL]; exact hc)
      rfl
    · simp only [List.singleton_append, Block.fvarTypesWellAnnotated,
        Stmt.fvarTypesWellAnnotated]
      exact ⟨⟨VarTyping.annotates_mono hle₁ hg, VarTyping.annotates_mono hle₁ hm,
        VarTyping.annotates_mono hle₁ hi, hb₂⟩, hys _ hle₁⟩
  | .exit l md | .typeDecl t md =>
    simp only [Stmt.hoistLoopPrefixInits, List.singleton_append, Block.fvarTypesWellAnnotated]
    exact ⟨trivial, hys Γt hle⟩
  termination_by sizeOf s

/-- The hoisted statement list passes the annotation check against a typing `Γt` that
    types every variable the source's typing `Γs` types, when the list passes it against
    `Γs` and `Γs` types none of its init names, which are distinct. -/
private theorem Block.hoist_fvarTypes (ss : List (Stmt P (Cmd P))) (Γs Γt : VarTyping P)
    (hle : ∀ x ty, Γs x = some ty → Γt x = some ty)
    (hfresh : ∀ y ∈ Block.initVars ss, Γs y = none) (hnd : (Block.initVars ss).Nodup)
    (h : Block.fvarTypesWellAnnotated Γs ss) :
    Block.fvarTypesWellAnnotated Γt (Block.hoistLoopPrefixInits ss) := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.fvarTypesWellAnnotated]
  | s :: rest =>
    rw [Block.hoistLoopPrefixInits]
    simp only [Block.initVars_cons, List.mem_append, List.nodup_append] at hfresh hnd
    refine Stmt.hoist_fvarTypes s Γs Γt hle (fun y hy => hfresh y (.inl hy)) hnd.1 h.1 _
      fun Γt' hle' => Block.hoist_fvarTypes rest _ Γt' hle' (fun y hy => ?_) hnd.2.1 h.2
    have hy' : y ∉ (Stmt.typedDefinedVars s).map Prod.fst := by
      intro hmem
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmem
      exact hnd.2.2 _ (typedDefinedVars_mem_initVars s p hp) _ hy rfl
    rw [VarTyping.extend_of_not_mem hy']
    exact hfresh y (.inr hy)
  termination_by sizeOf ss
end

/-- The loop-init hoist keeps the annotation check: the hoisted program passes it against
    every typing the source passes it against that types none of the source's init names,
    when those names are distinct. -/
theorem Block.hoistLoopPrefixInits_fvarTypesWellAnnotated (ss : List (Stmt P (Cmd P)))
    (Γ : VarTyping P) (hfresh : ∀ y ∈ Block.initVars ss, Γ y = none)
    (huniq : Block.uniqueInits ss) (h : Block.fvarTypesWellAnnotated Γ ss) :
    Block.fvarTypesWellAnnotated Γ (Block.hoistLoopPrefixInits ss) :=
  Block.hoist_fvarTypes ss Γ Γ (fun _ _ h => h) hfresh huniq h

end Annotations

end LoopInitHoistWF
end Imperative

end -- public section

public section

namespace Core

open Imperative

/-- `Core.hoistLoopPrefixInits` succeeds with the embedded generic loop-init
hoist whenever the Core block projects to a call-free Imperative block. -/
theorem hoistLoopPrefixInits_eq_some {ss : Statements} {bs : List (Imperative.Stmt Expression (Cmd Expression))}
    (h : projectStmts ss = some bs) :
    hoistLoopPrefixInits ss = some (embedStmts (Imperative.Block.hoistLoopPrefixInits bs)) := by
  simp [hoistLoopPrefixInits, h]

end Core

namespace Core.LoopInitHoist

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

variable (π : String → Option Procedure)

/-! ## Per-transform output transport

The bridged wrapper `Core.hoistLoopPrefixInits` returns `embedStmts` of the base
loop-init hoist of the projected input, so its Core output `BlockInitEnvWF`
transports from the base conditions on the hoisted base block.  The
statement-independent fields come from the input condition; the block-shaped
set/type fields (`defsUndefined`, `definedVarsNotReserved`,
`initTypesInhabited`) are *preserved* because the base hoist only permutes the
block's `initVars` and `initTypes` multisets
(`Imperative.LoopInitHoistProducerProps.Block.hoistP_initVars_perm` /
`_initTypesInhabited`), so no new name or type appears.  Flow-sensitive
`defUseWellFormed` is preserved by the pass-owned
`Imperative.LoopInitHoistWF.Block.hoistLoopPrefixInits_defUseWellFormed` theorem,
using the Core-native `uniqueInits` condition exposed by the public theorem. -/

/-- The loop-init hoist wrapper preserves `BlockInitEnvWF`: from the Core
    condition on the input `ss`, a successful projection `ss ↝ bs`, and the
    Hoist precondition's global uniqueness of init names, the Core condition
    holds of the wrapper's embedded output.  The pass-owned def-use theorem
    proves that each moved typed declaration is fresh and that its replacement
    `set` is preceded by the corresponding prelude declaration;
    `defsUndefined`, `definedVarsNotReserved`, and `initTypesInhabited` are
    carried across by the Hoist `initVars` / `initTypes` permutations. -/
theorem blockInitEnvWF {params : InitEnvWFParams}
    {ss out : Statements} {bs : List (Imperative.Stmt Expression (Cmd Expression))} {ρ : Imperative.Env Expression}
    (h : Core.Logic.BlockInitEnvWF params ss ρ)
    (hp : projectStmts ss = some bs)
    (hout : Core.hoistLoopPrefixInits ss = some out)
    (huniq : Block.uniqueInits (C := Command) ss) :
    Core.Logic.BlockInitEnvWF params out ρ := by
  rw [Core.hoistLoopPrefixInits_eq_some hp] at hout
  simp only [Option.some.injEq] at hout
  subst hout
  have hemb : embedStmts bs = ss := embedStmts_projectStmts hp
  have huniqBase : Block.uniqueInits (C := Cmd Expression) bs :=
    (Imperative.embedStmts_uniqueInits bs).mp (by rwa [hemb])
  obtain ⟨hwf, hsv, hdefs, hdnr, hres, hdu, hfd, hinit, hty⟩ := blockInitEnvWF_projectBase h hp
  have hdu' : Block.defUseWellFormed (C := Cmd Expression)
      (fun n => (ρ.store n).isSome) params.declaredFuncs
      (Imperative.Block.hoistLoopPrefixInits bs) = Bool.true :=
    Imperative.LoopInitHoistWF.Block.hoistLoopPrefixInits_defUseWellFormed
      bs (fun n => (ρ.store n).isSome) params.declaredFuncs hdu huniqBase
  refine Core.Logic.BlockInitEnvWF.ofBaseEmbed hwf hsv ?_ ?_ hres hdu' hfd ?_ ?_
  · intro n hn
    exact hdefs n ((Imperative.LoopInitHoistProducerProps.Block.hoistP_initVars_perm bs).mem_iff.mp hn)
  · intro n hn
    exact hdnr n ((Imperative.LoopInitHoistProducerProps.Block.hoistP_initVars_perm bs).mem_iff.mp hn)
  · exact Imperative.LoopInitHoistProducerProps.Block.hoistP_initTypesInhabited hinit
  · obtain ⟨Γ, hσ, hw⟩ := hty
    refine ⟨Γ, hσ, Imperative.LoopInitHoistWF.Block.hoistLoopPrefixInits_fvarTypesWellAnnotated
      bs Γ (fun y hy => hσ.eq_none_of_store_none (hdefs y hy)) huniqBase hw⟩

end Core.LoopInitHoist

end -- public section
