/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.LiftInstanceProcedures

/-!
# Check Override Refinement (behavioral subtyping / Liskov)

A Laurel-to-Laurel pass that, for every method `m` declared on a composite `Child`
that an ancestor `Parent` also declares (i.e. `Child.m` OVERRIDES `Parent.m`),
emits synthetic *checker procedures* whose verification discharges the
behavioral-subtyping obligations:

* **precondition contravariance** — `Parent.pre ⇒ Child.pre` (the override may not
  demand MORE of callers than the parent's contract promised they must satisfy);
* **postcondition covariance** — `Child.post ⇒ Parent.post` (the override must
  deliver at least what the parent's contract promised callers).

These are exactly the conditions under which a call site that statically sees
`Parent.m` may soundly run *any* runtime override — i.e. the soundness
prerequisite for dynamic dispatch. Without them, a call assuming `Parent.m`'s
contract is sound only because dispatch is static; once dispatch is dynamic a
violating override silently breaks the caller's proof.

The checker procedures are ordinary top-level procedures with no callers. A
`requires` clause is *assumed*; an `assert` in the body is *checked*. So
`checker(params) requires Parent.pre opaque { assert Child.pre }` verifies iff
`Parent.pre ⇒ Child.pre`, and a failure surfaces as a normal
`assertion could not be proved` diagnostic pointing at the offending override.

This pass runs BEFORE `LiftInstanceProcedures` (methods are still attached to
their composites, the `extending` chain is intact) and is purely ADDITIVE — it
only appends checker procedures, never rewriting existing ones. It runs before monomorphization, so an
override on a generic composite gets its refinement checked per concrete
instantiation for free (the checkers monomorphize along with everything else).

`modifies`-subset is enforced as a SIDE EFFECT of the two-state-faithful post-checker
(see `refinementCheckers`): the post-checker carries the PARENT's modifies and proves
the parent post over a heap havoc'd per the CHILD's frame, so `ModifiesClauses` emits
the parent frame-`ensures` on the checker and an override that WIDENS the frame fails
to re-establish it (a frame-widening override is rejected at definition time — see
corpus `mixed_modifies_frame_widen_rejected`, caught here as well as at the dispatch
call site).
-/

namespace Strata.Laurel

/-- A method name appears on a composite's `instanceProcedures`. Find, among
    `Child`'s strict ancestors, EVERY ancestor that declares a method of the same
    name — the parent definitions this method overrides.

    ALL declaring ancestors, not just the first: under multiple inheritance
    (`C extends A, B`) an override must refine `A.m` AND `B.m`, so a single-parent
    check would skip refinement against every parent but the first — a Liskov
    soundness hole for a `B`-typed reference holding a `C`.
    Returning the full list makes the driver emit one checker set per parent.

    `computeAncestors` is self-first, so drop self before searching; it is `Except`
    (an unresolved chain ⇒ no overridden parents, a safe empty). Nearest-first order
    is preserved but does not matter — each parent is checked independently.

    A parent method is only an overridden parent of `childMethod` when it is a genuine
    OVERRIDE (`isOverrideOf`), not a same-name Java OVERLOAD. This keeps the Liskov
    gate in lockstep with `isVirtualDispatchMethod`/`descendantOverriders`: the exact same
    pairs form a family in both passes, so no overload is Liskov-checked as if it refined a
    parent (which would spuriously reject two unrelated methods) and no real override
    escapes the check. -/
def findOverriddenParents (model : SemanticModel) (childName : Identifier)
    (childMethod : Procedure) : List (Identifier × Procedure) :=
  let ancestors := ((computeAncestors model childName).toOption.getD []).drop 1
  ancestors.filterMap fun anc =>
    -- `isOverrideOf` is symmetric, so passing `childMethod` as the "base" argument here is
    -- equivalent to the (parent, child) orientation the other sites use — do NOT "fix" the
    -- argument order into an asymmetric call.
    (anc.instanceProcedures.find? (isOverrideOf childMethod ·)).map
      fun p => (anc.name, p)

/-- Conjoin the non-`free` conditions in `cs` into a single boolean `StmtExprMd`
    (`true` if none). -/
def conjoinConditions (src : FileRange) (cs : List Condition) : StmtExprMd :=
  conjoinAnd src ((nonFreeConditions cs).map (·.condition))

/-- Emit the refinement checker procedures for one override pair. `child` declares
    a method that overrides `parent`'s same-named method. Produces up to two
    checkers (pre, post); each is an ordinary opaque procedure whose verification
    is the refinement VC. Returns `[]` when there is nothing to check. -/
def refinementCheckers (model : SemanticModel) (childTypeName : Identifier)
    (childTypeArgs : List Identifier)
    (parentTypeName : Identifier) (parent child : Procedure) : List Procedure :=
  -- SIGNATURE GUARD: an override whose input count, or whose OUTPUT SIGNATURE (arity or a
  -- non-covariant return type), is incompatible with the parent is rejected as a clean
  -- `.userError` by `validateDispatchFamilies` (in `LiftInstanceProcedures`, which runs after
  -- this pass). Synthesizing a refinement checker for it would re-express the parent's contract
  -- in the child's parameter/output names via `renameProcLocals`: a parent condition mentioning
  -- a dropped parameter, or a parent post referencing an output whose child type is incompatible,
  -- has no well-typed child slot to rename into — it stays unresolved / ill-typed and
  -- re-resolution folds into an internal `.strataBug`, MASKING the clean diagnostic. Skip it
  -- here (using the SAME `outputSignatureCompatible` relation `validateDispatchFamilies` rejects
  -- on, so the skip and the reject stay in lockstep) and let the dedicated check report it.
  if parent.inputs.length != child.inputs.length
     || ! outputSignatureCompatible model parent child then []
  else
  let src := child.name.source
  -- Qualify every synthesized checker name by the PARENT type, so a method overriding
  -- more than one parent (multiple inheritance, `C extends A, B`) emits distinct
  -- `C$m$A$refines$pre` / `C$m$B$refines$pre` … rather than colliding on one name.
  let q (suffix : String) : String := s!"{parentTypeName.text}${suffix}"
  -- Re-express the PARENT's contract in the CHILD's parameter names (argument order matters:
  -- source = parent, target = child).
  let rename := renameProcLocals parent child
  -- A `ModifiesGroup`'s targets and guard are expression positions that can name the
  -- procedure's parameters, so the parent frame must be renamed into the child's parameter
  -- names too — otherwise an override that renames a parameter it `modifies` leaves an
  -- unresolved reference and re-resolution fails as an internal `.strataBug`. Mirrors the
  -- `sModifiesGroup` pattern in `MonomorphizeComposites`.
  let renameModifies (gs : List ModifiesGroup) : List ModifiesGroup :=
    gs.map (fun g => { g with targets := g.targets.map rename, guard := g.guard.map rename })
  let parentPres := nonFreeConditions parent.preconditions
  let childPres := nonFreeConditions child.preconditions
  let parentPosts := nonFreeConditions (bodyPostconditions parent.body)
  let childPosts := nonFreeConditions (bodyPostconditions child.body)
  let childModifies := bodyModifies child.body
  let parentModifies := bodyModifies parent.body
  -- The shared type-arg list every synthesized proc carries: the child composite's
  -- type params (+ any method-level ones) so a GENERIC override (`self : C<T>`) is
  -- indexed as a poly proc by `MonomorphizeComposites.indexGenerics` and monomorphized
  -- per instantiation — mirrors how lifted methods carry `ct.typeArgs ++ proc.typeArgs`.
  -- Empty for a non-generic family ⇒ those checkers carry no type args (non-poly).
  let allTypeArgs := childTypeArgs ++ child.typeArgs
  -- Liskov-specific diagnostic summaries, so a failed refinement VC names the override instead
  -- of a bare "postcondition could not be proved" on the synthetic checker. Stamped on the
  -- `summary` field ONLY (never the condition or its `source`), so no VC is split or re-anchored
  -- and `.failsExactly` counts are unchanged.
  let overriddenDesc := s!"'{parentTypeName.text}.{child.name.text}'"
  let preMsg := s!"override precondition no stronger than {overriddenDesc} (Liskov)"
  let postMsg := s!"override postcondition no weaker than {overriddenDesc} (Liskov)"
  let frameMsg := s!"override modifies no more than {overriddenDesc} (Liskov)"
  let preChecker : List Procedure :=
    if childPres.isEmpty then []  -- nothing the child demands ⇒ contravariance trivially holds
    else
      -- assume Parent.pre (renamed), assert each Child.pre. The pre-checker is
      -- single-state (preconditions never reference `old`/the post-heap), so it keeps
      -- the simple assert-in-body shape — no companion / heap threading needed.
      let assume := conjoinConditions src (parentPres.map
        (fun c => { c with condition := rename c.condition }))
      let assertStmts : List StmtExprMd :=
        (childPres.map (·.condition)).map (fun a => ⟨ .Assert a (some preMsg), src ⟩)
      [{ name := refinementProcName childTypeName child.name (q "refines$pre")
         typeArgs := allTypeArgs
         inputs := child.inputs
         outputs := []
         preconditions := [{ condition := assume }]
         decreases := none
         body := .Opaque [] (some ⟨ .Block assertStmts none, src ⟩) [] }]
  -- POST-checker (covariance), two-state-faithful (see the file header for why the companion is
  -- bodyless): emit a bodyless `$childspec` carrying the CHILD's post + modifies, have the checker
  -- CALL it, and prove the PARENT's post + frame via its own `ensures`/`modifies`. `CallElim`
  -- havocs `$heap` per the child frame and assumes Child.post; the checker re-establishes
  -- Parent.post over that heap — the same path that rejects frame-widening at dispatch call sites.
  -- The post-checker discharges BOTH covariance (re-establish Parent.post) AND modifies-subset
  -- (re-establish the Parent frame over the child-havoc'd heap). Those are independent
  -- obligations, so gate on EITHER being non-trivial: a parent that guarantees nothing AND frames
  -- nothing has neither to check, but a parent with a real `modifies` frame and NO postcondition
  -- (a framed void method) still imposes a frame the override must not widen — gating on
  -- `parentPosts` alone would skip it. `parentModifies` is `nothingChanges` (`[{targets := []}]`),
  -- never `[]`, for an opaque parent, so test whether any group actually names a target — the same
  -- shape `analyzeProc` uses to classify a heap-writer. (Frame-widening is also caught at the
  -- dispatch call site; this keeps the definition-time defense-in-depth honest for the post-less
  -- framed parent.)
  let parentFramesSomething := ! (parentModifies.all (·.targets.isEmpty))
  let postCheckers : List Procedure :=
    if parentPosts.isEmpty && ! parentFramesSomething then []
    else
      let specName := refinementProcName childTypeName child.name (q "childspec")
      let checkerName := refinementProcName childTypeName child.name (q "refines$post")
      -- Companion: child's signature, child's (renamed-to-itself = identity) post +
      -- modifies, NO implementation. `impl.isNone && !modif.isEmpty` ⇒ heap-writer.
      let companion : Procedure :=
        { name := specName
          typeArgs := allTypeArgs
          inputs := child.inputs
          outputs := child.outputs
          preconditions := []
          decreases := none
          body := .Opaque childPosts none childModifies }
      -- Checker body: call `$childspec(selfArgs...)` assigning the outputs, exactly like
      -- the dispatcher's `callTo`.
      let selfArgs : List (AstNode StmtExpr) :=
        child.inputs.map fun p => ⟨ .Var (.Local p.name), src ⟩
      let callStmt : AstNode StmtExpr := mkCallAssigningOutputs src specName selfArgs child.outputs
      let checker : Procedure :=
        { name := checkerName
          typeArgs := allTypeArgs
          inputs := child.inputs
          outputs := child.outputs
          -- ASSUME Parent.pre (renamed into child's names): post-covariance is
          -- `Parent.pre ⇒ (Child.post ⇒ Parent.post)` — a caller invoking the parent
          -- contract has already established Parent.pre, so a covariant override whose
          -- post implies the parent's only UNDER the parent precondition (e.g. parent
          -- `requires a >= 0 ensures r >= 0`, child `ensures r == a`) must be checked
          -- with Parent.pre in scope, else it is spuriously over-rejected. (Parent.pre,
          -- NOT Child.pre — Child.pre is contravariantly weaker; assuming it would be
          -- unsound. Parent.pre ⇒ Child.pre is enforced separately by the pre-checker.)
          preconditions := parentPres.map
            (fun c => { c with condition := rename c.condition })
          decreases := none
          body := .Opaque
                    (parentPosts.map (fun c => { c with condition := rename c.condition, summary := c.summary.orElse (fun _ => some postMsg) }))
                    (some ⟨ .Block [callStmt] none, src ⟩)
                    ((renameModifies parentModifies).map (fun g => { g with summary := g.summary.orElse (fun _ => some frameMsg) })) }
      [companion, checker]
  preChecker ++ postCheckers

/-- The pass: for every virtual-dispatch family member, append the refinement checker
    procedures to `program.staticProcedures`. Consumes `virtualDispatchFamilies` (the same
    enumerator the dispatcher generator uses — see its docstring for the gate-parity
    invariant that makes this sound). -/
def checkOverrideRefinement (model : SemanticModel) (program : Program) : Program :=
  let checkers : List Procedure :=
    (virtualDispatchFamilies model program).flatMap fun fam =>
      -- Emit a checker set for EVERY parent, not just the nearest (see `findOverriddenParents`).
      (findOverriddenParents model fam.owner.name fam.method).flatMap fun (parentName, parentProc) =>
        refinementCheckers model fam.owner.name fam.owner.typeArgs parentName parentProc fam.method
  if checkers.isEmpty then program
  else { program with staticProcedures := program.staticProcedures ++ checkers }

public section

def checkOverrideRefinementPass : LoweringPass where
  name := "CheckOverrideRefinement"
  needsResolves := true
  run := fun _ p m => (checkOverrideRefinement m p, [], {})
  documentation := "For every composite method that overrides an ancestor method, emits synthetic checker procedures that verify behavioral subtyping: the override's precondition is no stronger than the parent's (Parent.pre ⇒ Child.pre) and its postcondition is no weaker (Child.post ⇒ Parent.post). A failing checker is a Liskov violation. Purely additive; runs before LiftInstanceProcedures. This is the soundness prerequisite for dynamic dispatch."

end -- public section

end Strata.Laurel
