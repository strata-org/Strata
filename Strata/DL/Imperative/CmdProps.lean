/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtProps
public import Strata.Util.ListMap

/-! # Properties of Imperative commands

Definitional equations for the generic command interfaces implemented by
`Cmd` and `CmdExt`, exact defined- and modified-variable equations for
base-command initialization and havoc, and the equational theory of the
identifier-rename definitions in `Strata.DL.Imperative.Cmd`.

Key results:
- `Cmd.hasInit_eq` / `Cmd.hasHavoc_eq` and their `CmdExt` counterparts expose
  the concrete constructors behind the generic interfaces.
- `init_cmd_definedVars` / `init_true_definedVars` characterize initialization
  targets.
- `init_modVars` / `havoc_modVars` characterize modified variables.
- `renameLookup_*` — `renameLookup`'s defining unfoldings, its identity off the
  sources, that a source lands in the targets, and injectivity under distinct
  targets.
- `substMapOf_find_*` — the substitution map returns the renamed target as an
  `fvar` on a source, and `none` off the sources.
- `Cmd.definedVars_substIdentMany` / `Cmd.modifiedVars_substIdentMany` — renaming
  leaves a command's defined (`init`) variables unchanged and maps its modified
  (`set`) variables through `renameLookup`.
- `Stmt.initVars_cmd_substIdentMany_*` — a `substIdentMany`-rewritten non-`init`
  command contributes no init vars.  These live here, with the rename lemmas they
  are built from, rather than with the general `Stmt.initVars_*` family in
  `StmtProps.lean` (the rename-free `Stmt.initVars_cmd` fact lives there).
-/

namespace Imperative

public section

/-- Base-command initialization through `HasInit` is `Cmd.init`. -/
@[simp] theorem Cmd.hasInit_eq {P : PureExpr}
    (ident : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    (HasInit.init (P := P) (CmdT := Cmd P) ident ty value md) =
      Cmd.init ident ty value md :=
  rfl

/-- Base-command havoc through `HasHavoc` is a nondeterministic `Cmd.set`. -/
@[simp] theorem Cmd.hasHavoc_eq {P : PureExpr}
    (ident : P.Ident) (md : MetaData P) :
    (HasHavoc.havoc (P := P) (CmdT := Cmd P) ident md) =
      Cmd.set ident .nondet md :=
  rfl

/-- Extended-command initialization wraps the base initialization. -/
@[simp] theorem CmdExt.hasInit_eq {P : PureExpr}
    (ident : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    (HasInit.init (P := P) (CmdT := CmdExt P) ident ty value md) =
      CmdExt.cmd (Cmd.init ident ty value md) :=
  rfl

/-- Extended-command havoc wraps a nondeterministic base `Cmd.set`. -/
@[simp] theorem CmdExt.hasHavoc_eq {P : PureExpr}
    (ident : P.Ident) (md : MetaData P) :
    (HasHavoc.havoc (P := P) (CmdT := CmdExt P) ident md) =
      CmdExt.cmd (Cmd.set ident .nondet md) :=
  rfl

/-- An initialization command defines exactly its target register. -/
theorem init_cmd_definedVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P)
    (md : MetaData P) (excludeScoped : Bool) :
    HasVarsImp.definedVars (P := P)
      (HasInit.init (P := P) (CmdT := Cmd P) x ty value md)
      excludeScoped = [x] := by
  with_unfolding_all rfl

/-- An initialization statement defines exactly its target register when
scoped definitions are included. -/
theorem init_true_definedVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    Stmt.definedVars
      (.cmd (HasInit.init (P := P) (CmdT := Cmd P) x ty value md))
      true = [x] := by
  with_unfolding_all rfl

/-- An `init` command defines its target but does not modify an existing slot. -/
theorem init_modVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    HasVarsImp.modifiedVars
      (HasInit.init (P := P) (CmdT := Cmd P) x ty value md) =
        ([] : List P.Ident) := by
  with_unfolding_all rfl

/-- A `havoc` command modifies exactly its target register. -/
theorem havoc_modVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (md : MetaData P) :
    HasVarsImp.modifiedVars
      (HasHavoc.havoc (P := P) (CmdT := Cmd P) x md) = [x] := by
  with_unfolding_all rfl

variable {P : PureExpr}

/-- `renameLookup` on the empty rename list is the identity. -/
@[simp] theorem renameLookup_nil (x : P.Ident) :
    renameLookup ([] : List (P.Ident × P.Ident)) x = x := rfl

/-- `renameLookup` on a cons is the head guard, else the tail lookup. -/
theorem renameLookup_cons_expand
    (q : P.Ident × P.Ident) (rest : List (P.Ident × P.Ident)) (k : P.Ident) :
    renameLookup (q :: rest) k = if k = q.1 then q.2 else renameLookup rest k := by
  show (Map.find? (q :: rest) k).getD k = _
  rw [Map.find?]
  by_cases h : q.1 = k
  · rw [ite_eq_left h, ite_eq_left h.symm]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun he : k = q.1 => h he.symm)]; rfl

/-- `renameLookup` is the identity off the sources. -/
theorem renameLookup_notin
    (subst : List (P.Ident × P.Ident)) (x : P.Ident)
    (h : x ∉ subst.map Prod.fst) :
    renameLookup subst x = x := by
  induction subst with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨h_head, h_tail⟩ := h
    rw [renameLookup_cons_expand, ite_eq_right h_head]
    exact ih h_tail

/-- On a source, `renameLookup` lands in the targets. -/
theorem renameLookup_mem_target
    (subst : List (P.Ident × P.Ident)) (x : P.Ident)
    (h : x ∈ subst.map Prod.fst) :
    renameLookup subst x ∈ subst.map Prod.snd := by
  induction subst with
  | nil => simp at h
  | cons p rest ih =>
    rw [renameLookup_cons_expand]
    by_cases h_eq : x = p.1
    · simp [h_eq]
    · simp only [ite_eq_right h_eq, List.map_cons, List.mem_cons]
      refine Or.inr (ih ?_)
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h_head | h_tail
      · exact absurd h_head h_eq
      · exact h_tail

/-- With distinct targets, `renameLookup` is injective on inputs each of which is
either a source or not a target. -/
theorem renameLookup_ne_of_ne
    (subst : List (P.Ident × P.Ident))
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    {w x : P.Ident} (hwx : w ≠ x)
    (hw : w ∈ subst.map Prod.fst ∨ w ∉ subst.map Prod.snd)
    (hx : x ∈ subst.map Prod.fst ∨ x ∉ subst.map Prod.snd) :
    renameLookup subst w ≠ renameLookup subst x := by
  induction subst with
  | nil =>
    simp only [renameLookup, Map.find?, Option.getD_none]
    exact hwx
  | cons p rest ih =>
    simp only [List.map_cons, List.nodup_cons] at h_tgt_nodup
    obtain ⟨hb_notin, h_rest_nodup⟩ := h_tgt_nodup
    rw [renameLookup_cons_expand p rest w, renameLookup_cons_expand p rest x]
    by_cases hwa : w = p.1 <;> by_cases hxa : x = p.1
    · exact absurd (hwa.trans hxa.symm) hwx
    · rw [ite_eq_left hwa, ite_eq_right hxa]
      by_cases hxf : x ∈ rest.map Prod.fst
      · have hx_mem := renameLookup_mem_target rest x hxf
        exact fun heq => hb_notin (heq ▸ hx_mem)
      · rw [renameLookup_notin rest x hxf]
        intro heq
        rcases hx with hx2 | hx2
        · simp only [List.map_cons, List.mem_cons] at hx2
          rcases hx2 with hx2 | hx2
          · exact hxa hx2
          · exact hxf hx2
        · simp only [List.map_cons, List.mem_cons, not_or] at hx2
          exact hx2.1 heq.symm
    · rw [ite_eq_right hwa, ite_eq_left hxa]
      by_cases hwf : w ∈ rest.map Prod.fst
      · have hw_mem := renameLookup_mem_target rest w hwf
        exact fun heq => hb_notin (heq ▸ hw_mem)
      · rw [renameLookup_notin rest w hwf]
        intro heq
        rcases hw with hw2 | hw2
        · simp only [List.map_cons, List.mem_cons] at hw2
          rcases hw2 with hw2 | hw2
          · exact hwa hw2
          · exact hwf hw2
        · simp only [List.map_cons, List.mem_cons, not_or] at hw2
          exact hw2.1 heq
    · rw [ite_eq_right hwa, ite_eq_right hxa]
      refine ih h_rest_nodup ?_ ?_
      · rcases hw with hwf | hwt
        · exact Or.inl (by
            simp only [List.map_cons, List.mem_cons] at hwf
            rcases hwf with h | h
            · exact absurd h hwa
            · exact h)
        · exact Or.inr (fun hc =>
            hwt (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hc))
      · rcases hx with hxf | hxt
        · exact Or.inl (by
            simp only [List.map_cons, List.mem_cons] at hxf
            rcases hxf with h | h
            · exact absurd h hxa
            · exact h)
        · exact Or.inr (fun hc =>
            hxt (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hc))

/-- On a source name, the rename list resolves to a target via `Map.find?`. -/
private theorem find?_eq_some_of_mem
    (subst : List (P.Ident × P.Ident)) (name : P.Ident)
    (h : name ∈ subst.map Prod.fst) :
    Map.find? subst name = some (renameLookup subst name) := by
  have hsome : ∃ w, Map.find? subst name = some w := by
    induction subst with
    | nil => simp at h
    | cons p rest ih =>
      simp only [Map.find?]
      by_cases hp : p.1 = name
      · exact ⟨p.2, by rw [ite_eq_left hp]⟩
      · rw [ite_eq_right hp]
        simp only [List.map_cons, List.mem_cons] at h
        exact ih (h.resolve_left (fun he => hp he.symm))
  obtain ⟨w, hw⟩ := hsome
  rw [hw, renameLookup, hw, Option.getD_some]

/-- On a source name, `substMapOf` returns the target as an `fvar` (first match). -/
theorem substMapOf_find_mem [HasFvar P]
    (subst : List (P.Ident × P.Ident)) (name : P.Ident)
    (h : name ∈ subst.map Prod.fst) :
    Map.find? (substMapOf subst) name = some (HasFvar.mkFvar (renameLookup subst name)) := by
  show Map.find? (Map.fmap HasFvar.mkFvar subst) name = _
  rw [Map.find?_fmap subst HasFvar.mkFvar name, find?_eq_some_of_mem subst name h,
    Option.map_some]

/-- Off the sources, `substMapOf` returns `none`. -/
theorem substMapOf_find_notin [HasFvar P]
    (subst : List (P.Ident × P.Ident)) (name : P.Ident)
    (h : name ∉ subst.map Prod.fst) :
    Map.find? (substMapOf subst) name = none := by
  have hnone : Map.find? subst name = none := by
    induction subst with
    | nil => simp [Map.find?]
    | cons p rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨h_head, h_tail⟩ := h
      simp only [Map.find?, ite_eq_right (fun he : p.1 = name => h_head he.symm)]
      exact ih h_tail
  show Map.find? (Map.fmap HasFvar.mkFvar subst) name = _
  rw [Map.find?_fmap subst HasFvar.mkFvar name, hnone, Option.map_none]

/-! ### `initVars` after a command rename -/

/-- Renaming leaves a command's defined (`init`) variables unchanged: the `init`
binder is not renamed, and no other constructor defines a variable. -/
theorem Cmd.definedVars_substIdentMany [HasSubstFvar P]
    (scope : List (P.Ident × P.Ident)) (c : Cmd P) :
    Cmd.definedVars (Cmd.substIdentMany scope c) = Cmd.definedVars c := by
  cases c <;> simp only [Cmd.substIdentMany, Cmd.definedVars]

/-- Renaming maps a command's modified (`set`) variables through `renameLookup`:
the `set` binder follows the rename, and no other constructor modifies a
variable. -/
theorem Cmd.modifiedVars_substIdentMany [HasSubstFvar P]
    (scope : List (P.Ident × P.Ident)) (c : Cmd P) :
    Cmd.modifiedVars (Cmd.substIdentMany scope c)
      = (Cmd.modifiedVars c).map (renameLookup scope) := by
  cases c <;> simp only [Cmd.substIdentMany, Cmd.modifiedVars, List.map_cons, List.map_nil]

/-- A `substIdentMany`-rewritten command with no defined vars still contributes no
init vars: renaming preserves a command's defined variables, so a command that
defines none still defines none after the rewrite. -/
theorem Stmt.initVars_cmd_substIdentMany_of_definedVars_nil [HasSubstFvar P] [HasFvars P]
    (scope : List (P.Ident × P.Ident)) (c : Cmd P) (h : Cmd.definedVars c = []) :
    Stmt.initVars (P := P) (Stmt.cmd (Cmd.substIdentMany scope c)) = [] := by
  rw [Stmt.initVars_cmd, Cmd.definedVars_substIdentMany, h]

/-- A `set` command rewritten by `substIdentMany` contributes no init vars
(`set` is not an `init`, so its `definedVars` is empty). -/
theorem Stmt.initVars_cmd_substIdentMany_set [HasSubstFvar P] [HasFvars P]
    (scope : List (P.Ident × P.Ident)) (name : P.Ident)
    (e : ExprOrNondet P) (md : MetaData P) :
    Stmt.initVars (P := P) (Stmt.cmd (Cmd.substIdentMany scope (Cmd.set name e md))) = [] :=
  Stmt.initVars_cmd_substIdentMany_of_definedVars_nil scope _ rfl

/-- An `assert` command rewritten by `substIdentMany` contributes no init vars
(`assert` is not an `init`, so its `definedVars` is empty). -/
theorem Stmt.initVars_cmd_substIdentMany_assert [HasSubstFvar P] [HasFvars P]
    (scope : List (P.Ident × P.Ident)) (label : String)
    (b : P.Expr) (md : MetaData P) :
    Stmt.initVars (P := P) (Stmt.cmd (Cmd.substIdentMany scope (Cmd.assert label b md))) = [] :=
  Stmt.initVars_cmd_substIdentMany_of_definedVars_nil scope _ rfl

/-- An `assume` command rewritten by `substIdentMany` contributes no init vars
(`assume` is not an `init`, so its `definedVars` is empty). -/
theorem Stmt.initVars_cmd_substIdentMany_assume [HasSubstFvar P] [HasFvars P]
    (scope : List (P.Ident × P.Ident)) (label : String)
    (b : P.Expr) (md : MetaData P) :
    Stmt.initVars (P := P) (Stmt.cmd (Cmd.substIdentMany scope (Cmd.assume label b md))) = [] :=
  Stmt.initVars_cmd_substIdentMany_of_definedVars_nil scope _ rfl

/-- A `cover` command rewritten by `substIdentMany` contributes no init vars
(`cover` is not an `init`, so its `definedVars` is empty). -/
theorem Stmt.initVars_cmd_substIdentMany_cover [HasSubstFvar P] [HasFvars P]
    (scope : List (P.Ident × P.Ident)) (label : String)
    (b : P.Expr) (md : MetaData P) :
    Stmt.initVars (P := P) (Stmt.cmd (Cmd.substIdentMany scope (Cmd.cover label b md))) = [] :=
  Stmt.initVars_cmd_substIdentMany_of_definedVars_nil scope _ rfl

end -- public section

end Imperative
