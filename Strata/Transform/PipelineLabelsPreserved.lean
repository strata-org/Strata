/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElim
public import Strata.Transform.LoopInitHoist
public import Strata.Languages.Core.Statement

-- `import all` to reach the (module-private) `_out`/`_residual` projection
-- lemmas of the two structured-to-structured passes; these are the same
-- per-constructor projections the downstream correctness files consume.
import all Strata.Transform.NondetElim
import all Strata.Transform.LoopInitHoist

public section

namespace Imperative

/-! # `userBlockLabels` is preserved by `nondetElim` and `hoistLoopPrefixInits`

The structured-to-structured passes `Block.nondetElim` (eliminates
nondeterministic control) and `Block.hoistLoopPrefixInits` (lifts loop-body
inits out as fresh-named siblings) both preserve the multiset *and order* of
user-provided `.block` labels: every label is carried through verbatim, the
freshly minted statements are all `.cmd`s (which `userBlockLabels` ignores),
and the loop-body rename step (`applyRenames`, a fold of `substIdent`) renames
identifiers without touching `.block` labels (which are `String` literals, not
`P.Ident` substitution targets).

Hence the source-side well-formedness condition `userLabelsShapeNodup ss`
(which depends only on `userBlockLabels ss` as a list) survives the pipeline
prefix `hoistLoopPrefixInits ∘ nondetElim`. The final corollary
`userLabelsShapeNodup_pipeline_preserved` discharges the transformed-body
obligation from the source-side condition, so the front-end never has to
reason about `hoist (nondetElim ss)`. -/

/-! ## Distributivity helpers for `userBlockLabels`

`userBlockLabels` is a list-valued structural walk, so the per-constructor
`_out`/`_residual`/havoc-prefix lemmas of the passes (which split via `++` and
`List.map Stmt.cmd`) need these two distributivity facts. -/

/-- `userBlockLabels` of the empty block is empty. -/
theorem Block.userBlockLabels_nil {P : PureExpr} {C : Type} :
    Block.userBlockLabels ([] : List (Stmt P C)) = [] := rfl

/-- `userBlockLabels` distributes over list concatenation. -/
theorem Block.userBlockLabels_append {P : PureExpr} {C : Type}
    (ss₁ ss₂ : List (Stmt P C)) :
    Block.userBlockLabels (ss₁ ++ ss₂) =
      Block.userBlockLabels ss₁ ++ Block.userBlockLabels ss₂ := by
  induction ss₁ with
  | nil => simp [Block.userBlockLabels]
  | cons s rest ih =>
      simp only [List.cons_append, Block.userBlockLabels, ih, List.append_assoc]

/-- A list of `.cmd` statements contributes no user block labels. -/
theorem Block.userBlockLabels_map_cmd {P : PureExpr} {C : Type}
    (cs : List C) :
    Block.userBlockLabels (cs.map (@Stmt.cmd P C)) = ([] : List String) := by
  induction cs with
  | nil => simp [Block.userBlockLabels]
  | cons c rest ih =>
      simp only [List.map_cons]
      rw [Block.userBlockLabels_cmd_cons, ih]

/-! ## `substIdent` / `applyRenames` preserve `userBlockLabels`

A rename `y → y'` rewrites command/guard/measure/invariant *identifiers*; the
`.block` arm carries its `String` label through verbatim (see
`Stmt.substIdent_block`). So `substIdent` — and `applyRenames`, a fold of
`substIdent` — leave `userBlockLabels` unchanged. Proof template:
`Stmt/Block.substIdent_noInitsAnywhere`. -/

mutual
/-- `Stmt.substIdent` preserves `userBlockLabels` (singleton form). -/
theorem Stmt.substIdent_userBlockLabels {P : PureExpr}
    [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] (y y' : P.Ident)
    (s : Stmt P (Cmd P)) :
    Block.userBlockLabels [Stmt.substIdent y y' s] = Block.userBlockLabels [s] := by
  match s with
  | .cmd c => simp only [Stmt.substIdent_cmd, Block.userBlockLabels_cmd_cons]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block]
      rw [show ([Stmt.block lbl (Block.substIdent y y' bss) md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.substIdent y y' bss) md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          Block.substIdent_userBlockLabels y y' bss]
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite]
      rw [show ([Stmt.ite (g.substIdent y y') (Block.substIdent y y' tss)
                  (Block.substIdent y y' ess) md] : List (Stmt P (Cmd P)))
            = Stmt.ite (g.substIdent y y') (Block.substIdent y y' tss)
                (Block.substIdent y y' ess) md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          show ([Stmt.ite g tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite g tss ess md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          Block.substIdent_userBlockLabels y y' tss,
          Block.substIdent_userBlockLabels y y' ess]
  | .loop g m inv body md =>
      simp only [Stmt.substIdent_loop]
      rw [show ([Stmt.loop (g.substIdent y y')
                  (m.map (fun mm => HasSubstFvar.substFvar mm y (HasFvar.mkFvar y')))
                  (inv.map (fun p => (p.1, HasSubstFvar.substFvar p.2 y (HasFvar.mkFvar y'))))
                  (Block.substIdent y y' body) md] : List (Stmt P (Cmd P)))
            = Stmt.loop (g.substIdent y y')
                  (m.map (fun mm => HasSubstFvar.substFvar mm y (HasFvar.mkFvar y')))
                  (inv.map (fun p => (p.1, HasSubstFvar.substFvar p.2 y (HasFvar.mkFvar y'))))
                  (Block.substIdent y y' body) md :: [] from rfl,
          Block.userBlockLabels_loop_cons,
          show ([Stmt.loop g m inv body md] : List (Stmt P (Cmd P)))
            = Stmt.loop g m inv body md :: [] from rfl,
          Block.userBlockLabels_loop_cons,
          Block.substIdent_userBlockLabels y y' body]
  | .exit lbl md => simp only [Stmt.substIdent]
  | .funcDecl d md => simp only [Stmt.substIdent]
  | .typeDecl t md => simp only [Stmt.substIdent]
  termination_by sizeOf s

/-- `Block.substIdent` preserves `userBlockLabels`. -/
theorem Block.substIdent_userBlockLabels {P : PureExpr}
    [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] (y y' : P.Ident)
    (ss : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (Block.substIdent y y' ss) = Block.userBlockLabels ss := by
  match ss with
  | [] => simp [Block.userBlockLabels]
  | s :: rest =>
      rw [Block.substIdent,
          show (Stmt.substIdent y y' s :: Block.substIdent y y' rest)
            = [Stmt.substIdent y y' s] ++ Block.substIdent y y' rest from rfl,
          Block.userBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl,
          Block.userBlockLabels_append,
          Stmt.substIdent_userBlockLabels y y' s,
          Block.substIdent_userBlockLabels y y' rest]
  termination_by sizeOf ss
end

/-- `Block.applyRenames` (a fold of `Block.substIdent`) preserves
`userBlockLabels`. Template: `Block.applyRenames_noInitsAnywhere`. -/
theorem Block.applyRenames_userBlockLabels {P : PureExpr}
    [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (Block.applyRenames renames ss) =
      Block.userBlockLabels ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_userBlockLabels]

/-! ## The lift residual preserves `userBlockLabels`

`liftInitsInLoopBodyM`'s residual (`.1.2.2`) rewrites every collected `.init`
into a same-name `.set` (still a `.cmd`), recurses through `.block`/`.ite`, and
leaves `.loop`s untouched (they are already hoist-processed). None of these
moves change `userBlockLabels`. -/

mutual
/-- `Stmt.liftInitsInLoopBodyM`'s residual preserves `userBlockLabels`. -/
theorem Stmt.liftInitsInLoopBodyM_userBlockLabels {P : PureExpr} [HasIdent P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.userBlockLabels (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Block.userBlockLabels [s] := by
  match s with
  | .cmd c =>
      -- Every `.cmd` arm of the lift returns a residual that is a singleton
      -- `.cmd` (the `.init` arm rewrites to a same-name `.set`), so both sides
      -- collapse to `[]`.
      cases c <;>
        simp only [Stmt.liftInitsInLoopBodyM, Block.userBlockLabels_cmd_cons]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      rw [show ([Stmt.block lbl (Block.liftInitsInLoopBodyM bss σ).1.2.2 md]
              : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.liftInitsInLoopBodyM bss σ).1.2.2 md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          Block.liftInitsInLoopBodyM_userBlockLabels bss σ]
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      rw [show ([Stmt.ite g (Block.liftInitsInLoopBodyM tss σ).1.2.2
                  (Block.liftInitsInLoopBodyM ess
                    (Block.liftInitsInLoopBodyM tss σ).2).1.2.2 md]
              : List (Stmt P (Cmd P)))
            = Stmt.ite g (Block.liftInitsInLoopBodyM tss σ).1.2.2
                (Block.liftInitsInLoopBodyM ess
                  (Block.liftInitsInLoopBodyM tss σ).2).1.2.2 md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          show ([Stmt.ite g tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite g tss ess md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          Block.liftInitsInLoopBodyM_userBlockLabels tss σ,
          Block.liftInitsInLoopBodyM_userBlockLabels ess _]
  | .loop g m inv body md =>
      rw [Stmt.liftInitsInLoopBodyM]
  | .exit lbl md => rw [Stmt.liftInitsInLoopBodyM]
  | .funcDecl d md => rw [Stmt.liftInitsInLoopBodyM]
  | .typeDecl t md => rw [Stmt.liftInitsInLoopBodyM]
  termination_by sizeOf s

/-- `Block.liftInitsInLoopBodyM`'s residual preserves `userBlockLabels`. -/
theorem Block.liftInitsInLoopBodyM_userBlockLabels {P : PureExpr} [HasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.userBlockLabels (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.userBlockLabels ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.userBlockLabels]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.userBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.userBlockLabels_append,
          Stmt.liftInitsInLoopBodyM_userBlockLabels s σ,
          Block.liftInitsInLoopBodyM_userBlockLabels rest _]
  termination_by sizeOf ss
end

/-! ## `nondetElim` preserves `userBlockLabels`

Template: `Stmt/Block.nondetElimM_loopHasNoInvariants`. The pass keeps every
`.block` label, recurses into sub-bodies, and the only minted statements (the
`init $g := *` havoc and, for nondet loops, the body-tail `set $g := *`) are
`.cmd`s. -/

mutual
/-- `Stmt.nondetElimM` preserves `userBlockLabels` at any threaded state. -/
theorem Stmt.nondetElimM_userBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.userBlockLabels (Stmt.nondetElimM s σ).1 = Block.userBlockLabels [s] := by
  match s with
  | .cmd c =>
      rw [Stmt.nondetElimM]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out,
          show ([Stmt.block lbl (Block.nondetElimM bss σ).1 md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.nondetElimM bss σ).1 md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          Block.nondetElimM_userBlockLabels bss σ]
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out,
          show ([Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                  (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          show ([Stmt.ite (.det e) tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) tss ess md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          Block.nondetElimM_userBlockLabels tss σ,
          Block.nondetElimM_userBlockLabels ess _]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      -- The output is `[init $g, ite (.det $g) tss' ess']`; the prelude `init`
      -- is a `.cmd` (label-free), and both branches recurse. Finish by the
      -- structural cons lemmas + the branch IHs.
      simp only [Block.userBlockLabels_cmd_cons,
                 Block.nondetElimM_userBlockLabels tss,
                 Block.nondetElimM_userBlockLabels ess, Block.userBlockLabels_nil,
                 Block.userBlockLabels_ite_cons]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out,
          show ([Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md :: [] from rfl,
          Block.userBlockLabels_loop_cons,
          show ([Stmt.loop (.det e) m inv body md] : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv body md :: [] from rfl,
          Block.userBlockLabels_loop_cons,
          Block.nondetElimM_userBlockLabels body σ]
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      -- The output is `[init $g, loop (body' ++ [havoc $g])]`; the prelude
      -- `init` and the body-tail `havoc` are `.cmd`s (label-free), and the loop
      -- body recurses. Generalise the generated name/state and finish by the
      -- structural cons/append lemmas + the body IH.
      simp only [Block.userBlockLabels_cmd_cons, Block.userBlockLabels_append,
                 Block.nondetElimM_userBlockLabels body, Block.userBlockLabels_nil,
                 Block.userBlockLabels_loop_cons, List.append_nil]
  | .exit lbl md =>
      rw [Stmt.nondetElimM]
  | .funcDecl d md =>
      rw [Stmt.nondetElimM]
  | .typeDecl t md =>
      rw [Stmt.nondetElimM]
  termination_by sizeOf s

/-- `Block.nondetElimM` preserves `userBlockLabels` at any threaded state. -/
theorem Block.nondetElimM_userBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.userBlockLabels (Block.nondetElimM ss σ).1 = Block.userBlockLabels ss := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.userBlockLabels]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.userBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.userBlockLabels_append,
          Stmt.nondetElimM_userBlockLabels s σ,
          Block.nondetElimM_userBlockLabels rest _]
  termination_by sizeOf ss
end

/-- Pure-wrapper corollary: `Block.nondetElim` preserves `userBlockLabels`. -/
theorem Block.nondetElim_userBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (Block.nondetElim ss) = Block.userBlockLabels ss := by
  rw [Block.nondetElim, Block.nondetElimM_userBlockLabels]

/-! ## `hoistLoopPrefixInits` preserves `userBlockLabels`

The `.loop` arm emits `havocs.map Stmt.cmd ++ [.loop … body₃ …]` where `body₃ =
applyRenames renames (lift residual)`: the havoc prelude is `.cmd`s (label-free,
H1), `applyRenames` is label-invariant (A), and the lift residual is
label-preserving (L). All other arms recurse structurally and keep their labels.
Template: `Stmt/Block.nondetElimM_loopHasNoInvariants`. -/

mutual
/-- `Stmt.hoistLoopPrefixInitsM` preserves `userBlockLabels` at any state. -/
theorem Stmt.hoistLoopPrefixInitsM_userBlockLabels {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.userBlockLabels (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Block.userBlockLabels [s] := by
  match s with
  | .cmd c =>
      rw [Stmt.hoistLoopPrefixInitsM]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out,
          show ([Stmt.block lbl (Block.hoistLoopPrefixInitsM bss σ).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.hoistLoopPrefixInitsM bss σ).1 md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.userBlockLabels_block_cons,
          Block.hoistLoopPrefixInitsM_userBlockLabels bss σ]
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out,
          show ([Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
                  (Block.hoistLoopPrefixInitsM ess
                    (Block.hoistLoopPrefixInitsM tss σ).2).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
                (Block.hoistLoopPrefixInitsM ess
                  (Block.hoistLoopPrefixInitsM tss σ).2).1 md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          show ([Stmt.ite g tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite g tss ess md :: [] from rfl,
          Block.userBlockLabels_ite_cons,
          Block.hoistLoopPrefixInitsM_userBlockLabels tss σ,
          Block.hoistLoopPrefixInitsM_userBlockLabels ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out, Block.userBlockLabels_append,
          Block.userBlockLabels_map_cmd,
          show ([Stmt.loop g m inv
                  (Block.applyRenames
                    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                      (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
                    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                      (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) md]
              : List (Stmt P (Cmd P)))
            = Stmt.loop g m inv
                  (Block.applyRenames
                    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                      (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
                    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                      (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) md :: [] from rfl,
          Block.userBlockLabels_loop_cons,
          Block.applyRenames_userBlockLabels,
          Block.liftInitsInLoopBodyM_userBlockLabels,
          Block.hoistLoopPrefixInitsM_userBlockLabels body σ,
          show ([Stmt.loop g m inv body md] : List (Stmt P (Cmd P)))
            = Stmt.loop g m inv body md :: [] from rfl,
          Block.userBlockLabels_loop_cons, List.nil_append]
  | .exit lbl md =>
      rw [Stmt.hoistLoopPrefixInitsM]
  | .funcDecl d md =>
      rw [Stmt.hoistLoopPrefixInitsM]
  | .typeDecl t md =>
      rw [Stmt.hoistLoopPrefixInitsM]
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInitsM` preserves `userBlockLabels` at any state. -/
theorem Block.hoistLoopPrefixInitsM_userBlockLabels {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.userBlockLabels (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.userBlockLabels ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.userBlockLabels]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.userBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.userBlockLabels_append,
          Stmt.hoistLoopPrefixInitsM_userBlockLabels s σ,
          Block.hoistLoopPrefixInitsM_userBlockLabels rest _]
  termination_by sizeOf ss
end

/-- Pure-wrapper corollary: `Block.hoistLoopPrefixInits` preserves
`userBlockLabels`. -/
theorem Block.hoistLoopPrefixInits_userBlockLabels {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (Block.hoistLoopPrefixInits ss) =
      Block.userBlockLabels ss := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_userBlockLabels]

/-! ## The discharger: source-side `userLabelsShapeNodup` survives the pipeline

`userLabelsShapeNodup` is a function only of the `userBlockLabels` list, so the
two preservation corollaries rewrite the transformed-body obligation back to the
source body. -/

/-- Source-side `userLabelsShapeNodup` is preserved through the pipeline prefix
`hoistLoopPrefixInits ∘ nondetElim`. This discharges the transformed-body
well-formedness obligation from the source-side condition. -/
theorem Block.userLabelsShapeNodup_pipeline_preserved {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasBool P] [HasSubstFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P)))
    (h : Block.userLabelsShapeNodup ss) :
    Block.userLabelsShapeNodup (Block.hoistLoopPrefixInits (Block.nondetElim ss)) := by
  unfold Block.userLabelsShapeNodup at h ⊢
  rw [Block.hoistLoopPrefixInits_userBlockLabels, Block.nondetElim_userBlockLabels]
  exact h

end Imperative

end -- public section
