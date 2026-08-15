/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.EliminateValueInReturns
-- `term_by_mem` (the structural-recursion termination tactic used by `typeMatchesModuloTVars`)
-- is a meta macro; it is only re-exported transitively via a non-`public` import, so import it
-- directly for the `decreasing_by` proof to elaborate.
meta import Strata.Util.Tactics


/-!
# Lift Instance Procedures

A Laurel-to-Laurel pass that lifts every instance procedure (a procedure
defined inside a `composite` block) to a top-level static procedure with a
mangled name `<CompositeName>$<methodName>`, then rewrites every call site
that resolved to such an instance procedure to use the lifted name.

After this pass:
- `CompositeType.instanceProcedures` is empty for every composite.
- `program.staticProcedures` contains the lifted procedures.
- Every `InstanceCall` (from `obj#method(args)` surface syntax) points
  at the lifted name. For `InstanceCall`, the receiver is prepended to
  the argument list to match the lifted procedure's `self : <CompositeName>`
  parameter.
-/

namespace Strata.Laurel

/-! ## Lifting + call-site rewriting

Lift instance procedures to static scope (e.g., procedure `proc`
of composite type `T` will be lifted to `T$proc`).
Then, rewrite caller-side of `obj#proc` to call the lifted procedure

-/

/-- Rewrite a single node so that any callee resolving to an instance procedure
    is replaced by its lifted name. -/
private def rewriteCallNode (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .StaticCall callee args =>
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted args }
    | _ => expr
  | .InstanceCall target callee args =>
    -- `obj#method(args)` surface syntax parses to InstanceCall. Flatten it to
    -- a static call against the lifted name, prepending the receiver as the
    -- first argument to match the lifted procedure's `self` parameter.
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted (target :: args) }
    | _ => expr
  | _ => expr

/-! ## Dynamic dispatch: tag-switch dispatcher generation

When a method `m` declared on a composite `D` is OVERRIDDEN by a strict descendant,
the lifted `D$m` is generated as a runtime-tag DISPATCHER rather than `D`'s body
verbatim, so a call on a `D`-typed receiver holding a more-derived value runs the
derived override (matching Java/C# semantics). Concretely:

* every declaring type `T` in the family gets its real body lifted to `T$m$impl`;
* `D$m` becomes `if self is O₁ then O₁$m$impl(self as O₁, …) else … else D$m$impl(self, …)`
  over `D`'s descendant-overriders `Oᵢ` (most-derived first), carrying `D`'s own
  contract so callers see the static contract.

This is SOUND because the separate behavioral-subtyping (Liskov) checks
(`CheckOverrideRefinement`, run just before this pass) guarantee every override
refines its parent's contract, so each branch's impl postcondition implies `D`'s.
A method overridden nowhere gets the plain static lift `D$m = body` (no
dispatcher, no `$impl`), so the dispatch machinery adds nothing for
inheritance-free code. -/

-- The family predicates below are shared with `CheckOverrideRefinement` (the Liskov pass).
public section

/-- Structural type match where a type VARIABLE on EITHER side matches ANY type (otherwise
    `highEq`). This is the parameter relation for deciding OVERRIDE vs OVERLOAD, and it is a
    deliberate SOUND OVER-APPROXIMATION of "same type under the inheritance substitution":
    a genuine override's parameter type is the base's with the base type params substituted
    (`IntBox extends Box<int>` ⇒ `Box<T>.put(x:T)` becomes `put(x:int)`; `SBox<U> extends
    Box<U>` ⇒ `put(x:U)`), and substitution only changes positions where the base held a
    type var — so treating type vars as wildcards NEVER rejects a genuine override, while
    two unrelated CONCRETE types (`BB` vs `AA`, or `Pair<int,int>` vs `Pair<int,bool>`) still
    fail to match. Wildcards only ever ADD matches, so this stays within the old name-only
    membership (which was sound): `genuine-overrides ⊆ this ⊆ same-name`, hence it can no
    more false-ACCEPT than name-only did, and it never drops a real override. -/
def typeMatchesModuloTVars (a b : HighTypeMd) : Bool :=
  match _a: a.val, _b: b.val with
  | .TVar _, _ => true
  | _, .TVar _ => true
  | .Applied ba aargs, .Applied bb bargs =>
      typeMatchesModuloTVars ba bb && aargs.length == bargs.length &&
        (aargs.attach.zip bargs |>.all (fun (x, y) => typeMatchesModuloTVars x.1 y))
  | .TSet ea, .TSet eb => typeMatchesModuloTVars ea eb
  | .TMap ka va, .TMap kb vb => typeMatchesModuloTVars ka kb && typeMatchesModuloTVars va vb
  -- `.Intersection` has no surface grammar production (it is only synthesized internally, e.g.
  -- Resolution's multi-bound types), so no method parameter is ever intersection-typed and this
  -- arm is unexercised by any corpus case; kept structural for parity with the other arms.
  | .Intersection ta, .Intersection tb =>
      ta.length == tb.length && (ta.attach.zip tb |>.all (fun (x, y) => typeMatchesModuloTVars x.1 y))
  | _, _ => highEq a b
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    . cases x; term_by_mem
    . cases x; term_by_mem

/-- Whether `baseM` and `ovM` share a non-`self` INPUT signature. Both must have a RECEIVER
    (a first input, `inputs[0]`, each declarer's own composite) to be a dispatch-family member:
    a receiver-less instance method can never be virtually dispatched (there is no value to
    `self is O` tag-test), so if either side has no first input this returns `false` — which
    also avoids the silent `[].drop 1 = []` truncation that would otherwise conflate two
    receiver-less same-named methods into a family and crash dispatcher generation. Given
    receivers, the rest of the inputs are compared by `typeMatchesModuloTVars`.

    This is only the SIGNATURE half of override detection — `isOverrideOf` adds the name
    check — and is what distinguishes a genuine OVERRIDE from a Java OVERLOAD (a same-named
    method with a different parameter list): a real override — concrete (`Box<int>`), type-param
    RENAMED (`SBox<U>`), or verbatim — matches and stays in the dispatch family (where the
    RENAMED-TYPE-PARAMS guard can still reject the shapes the dispatcher cannot lower), while
    an overload with an unrelated concrete parameter type (`val(b:BB)` vs `val(a:AA)`) does
    NOT match and is never conflated into a virtual family. Symmetric (`typeMatchesModuloTVars`
    is), so callers may pass the two methods in either order. (Outputs are NOT part of this
    membership signature — Java, like Laurel here, does not use the return type in the overload
    signature. Output arity AND output covariance are enforced by `validateDispatchFamilies`'
    OUTPUT-SIGNATURE guard: an override must return the same type as, or a subtype of, the
    overridden method's output; a backwards or unrelated return is rejected there with a clean
    userError.) -/
def sameNonSelfSignature (baseM ovM : Procedure) : Bool :=
  match baseM.inputs, ovM.inputs with
  | _ :: bt, _ :: ot =>
      let bts := bt.map (·.type)
      let ots := ot.map (·.type)
      bts.length == ots.length && (bts.zip ots).all (fun (a, b) => typeMatchesModuloTVars a b)
  | _, _ => false

/-- The dispatch-family membership atom: `ovM` overrides `baseM` iff same name and same
    non-`self` input signature (`sameNonSelfSignature`). All family-membership checks use this
    predicate (via `virtualDispatchFamilies`), keeping the dispatcher and Liskov checker in sync.
    Symmetric in its arguments. -/
def isOverrideOf (baseM ovM : Procedure) : Bool :=
  ovM.name.text == baseM.name.text && sameNonSelfSignature baseM ovM

def findOverrideIn (ct : CompositeType) (baseM : Procedure) : Option Procedure :=
  ct.instanceProcedures.find? (isOverrideOf baseM ·)

def declaresOverrideOf (baseM : Procedure) (ct : CompositeType) : Bool :=
  ct.instanceProcedures.any (isOverrideOf baseM ·)

/-- The strict descendants of `ancestorName` that OVERRIDE `baseM` (declare a same-name,
    same-non-self-signature method), i.e. the overrides visible through an
    `ancestorName`-typed receiver. Ordered most-derived first (deeper `ancestors`-distance
    first), so the generated `is`-chain tests the most specific type before its supertypes
    — required because a value `is` all of its ancestors. -/
def descendantOverriders (model : SemanticModel) (program : Program)
    (ancestorName : Identifier) (baseM : Procedure) : List CompositeType :=
  let composites := program.types.filterMap fun td =>
    match td with | .Composite ct => some ct | _ => none
  let tagged := composites.filterMap fun t =>
    if t.name.text == ancestorName.text then none
    else if declaresOverrideOf baseM t then
      -- `computeAncestors` is `Except`; an unresolved chain ⇒ no dispatch (safe empty).
      let anc := ((computeAncestors model t.name).toOption.getD []).map (·.name.text)
      if anc.contains ancestorName.text
      then some (t, anc.length)  -- deeper subtype ⇒ longer ancestor chain
      else none
    else none
  -- Most-derived (longest ancestor chain) first, with a name tiebreaker so equal-distance
  -- siblings sort deterministically rather than by `qsort`'s (unstable) source-order artifact.
  -- Order is a determinism concern, not soundness (the MI case is handled by `dispatcherPosts`).
  (tagged.toArray.qsort (fun a b =>
    if a.2 > b.2 then true
    else if a.2 < b.2 then false
    else a.1.name.text < b.1.name.text)).toList.map (·.1)

/-! ### Dynamic-dispatch family predicates -/

/-- Some strict ancestor of `declarerName` declares a method that `baseM` overrides —
    i.e. `baseM` is itself an override (the ancestor direction of family membership).
    Membership is by name AND signature (`isOverrideOf`), not name alone. -/
def declaredByAncestor (model : SemanticModel) (declarerName : Identifier)
    (baseM : Procedure) : Bool :=
  (((computeAncestors model declarerName).toOption.getD []).drop 1).any (fun anc =>
    anc.instanceProcedures.any (isOverrideOf baseM ·))

/-- `baseM` declared on `declarerName` is overridden within its inheritance family:
    some strict descendant OVERRIDES it, OR some strict ancestor declares an override of
    it. Membership is by name AND signature (`isOverrideOf`), not name alone, so a Java
    OVERLOAD (same name, different parameter types) sharing an ancestry is NOT treated as a
    virtual family — which would otherwise conflate two unrelated methods into one
    dispatcher and spuriously reject (or, for incompatible types, `.strataBug`). -/
def isOverriddenMethod (model : SemanticModel) (program : Program)
    (declarerName : Identifier) (baseM : Procedure) : Bool :=
  (! (descendantOverriders model program declarerName baseM).isEmpty)
  || declaredByAncestor model declarerName baseM

/-- The predicate defining a virtually-dispatched method: overridden by a strict
    descendant, or itself an override of an ancestor. `virtualDispatchFamilies` folds this
    into the single family list all passes consume (see its docstring for the gate-parity
    invariant this predicate exists to serve).

    Generic inheriting families ARE supported: the dispatcher's `is`/`as` tag-tests use
    the applied form (`appliedTagType`, so `self is SBox<T>` not bare `SBox`), and the
    Liskov checker carries the composite's type params so it monomorphizes per
    instantiation. So any overridden method — generic or not — is virtual + checked. -/
def isVirtualDispatchMethod (model : SemanticModel) (program : Program)
    (declarerName : Identifier) (baseM : Procedure) : Bool :=
  isOverriddenMethod model program declarerName baseM

/-- A virtual-dispatch family: a composite declaring a virtual method, and the
    descendant composites that override it (most-derived-first, possibly empty for
    a leaf override that is itself an override of an ancestor but has no further
    descendants overriding it). -/
structure DispatchFamily where
  owner : CompositeType
  method : Procedure
  /-- Strict descendants of `owner` that override `method`, sorted most-derived-first
      (see `descendantOverriders`). Empty for a leaf override whose only virtual
      relation is the ancestor direction. -/
  overriders : List CompositeType

/-- The set of virtual-dispatch families in the program.

    This is the SINGLE ENUMERATOR that all dispatch-related passes consume:
    * `CheckOverrideRefinement` emits Liskov-checker procedures for each family;
    * `validateDispatchFamilies` checks each family for unlowerable shapes;
    * `liftInstanceProcedures` generates a dispatcher + `$impl` for each family.

    Gate-parity is structural: all three passes range over the same list rather than
    independently re-walking `program.types` and gating on `isVirtualDispatchMethod`, so
    they cannot drift into an unsound "dispatcher without checker" state. Each family's
    `overriders` are precomputed once and reused, rather than recomputed per consumer.

    The program is assumed closed-world: every subtype and every override is present
    in `program.types`. If an overrider were invisible to this scan, the dispatcher's
    guarded-fallthrough post would claim `D.post` on a branch that actually runs the
    unenumerated override. Resolution rejects an `extends` onto a type outside the
    program, so ancestry cannot silently escape `program.types`; this scan is therefore
    exhaustive for the authored program. -/
def virtualDispatchFamilies (model : SemanticModel) (program : Program)
    : List DispatchFamily :=
  program.types.flatMap fun td =>
    match td with
    | .Composite ct =>
      ct.instanceProcedures.filterMap fun m =>
        -- Virtuality is exactly `isOverriddenMethod` (descendant OR ancestor direction),
        -- but computed here so the descendant `overriders` — needed anyway — are reused
        -- instead of recomputed by the gate. The ancestor branch (`declaredByAncestor`)
        -- keeps a leaf override virtual: its dispatcher dispatches only to its own `$impl`
        -- (empty `overriders`) but must exist for a parent-typed reference to find it.
        let overriders := descendantOverriders model program ct.name m
        if !overriders.isEmpty || declaredByAncestor model ct.name m
        then some { owner := ct, method := m, overriders }
        else none
    | _ => []

/-- Whether an override's return type at one output position is COMPATIBLE with the base's:
    the same type (reflexive; also the generic `returns (r: T)` case, via the tvar-wildcard),
    OR a COVARIANT subtype — the child returns a composite whose ancestor chain includes the
    base's return composite. The dispatcher's branch assigns the child `$impl` result into the
    BASE's output slot, so a subtype (widen) is sound like an upcast; a supertype (narrow) or
    unrelated type is not. The subtype branch peels the child return's base name (`highBaseName?`
    handles both a bare `.UserDefined` and an `.Applied` instantiation like `Box<int>`) and keys
    on the base return being a bare `.UserDefined`, so `.Applied`-vs-`.Applied` stays INVARIANT
    (`Box<Dog>` does NOT refine `Box<Animal>` — that falls to the exact-match branch and fails).
    The `computeAncestors` name-walk is a sound UNDER-approximation of the verifier's `isSubtype`
    (it treats generic args invariantly and can only reject-a-sound-case, never admit-an-unsound
    one), so structural admission here never lets an unsound narrowing verify downstream.

    SHARED by BOTH passes: `validateDispatchFamilies` (below) rejects an incompatible output with
    a clean `.userError`, and `CheckOverrideRefinement.refinementCheckers` skips synthesizing a
    post-checker for such an override (which would otherwise re-express the parent post over the
    wrong-typed output and fold into an internal `.strataBug` before this reject fires). One
    predicate keeps the skip and the reject in lockstep. -/
def outputSignatureCompatible (model : SemanticModel) (baseM ovM : Procedure) : Bool :=
  baseM.outputs.length == ovM.outputs.length &&
    (baseM.outputs.zip ovM.outputs).all (fun (parentOut, childOut) =>
      typeMatchesModuloTVars parentOut.type childOut.type ||
        (match parentOut.type.val with
         | .UserDefined pn =>
           match highBaseName? childOut.type.val with
           | some cn => ((computeAncestors model cn).toOption.getD []).any (·.name.text == pn.text)
           | none => false
         | _ => false))

/-- Validate every dispatch family for shapes the dispatcher cannot lower, emitting a
    CLEAN `.userError` (which halts the pipeline before the synthetic if-chain reaches a
    later pass and hard-fails as an internal `.strataBug`). Four shapes, each a real
    program the dispatcher/Liskov machinery cannot yet handle:

    * ASYMMETRIC-THROWS — a family whose declarers disagree on whether the method
      `throws` (some declare `throws (e:E)`, some don't). `EliminateExceptions` (which
      runs AFTER dispatch generation) rewrites a throwing method into a `$heap`-threaded
      `Result` return but leaves a non-throwing sibling plain, so the dispatcher's
      synthetic `if self is O then O$m$impl(..) else T$m$impl(..)` fails to type-join
      ("incompatible types '(Heap,τ)' and 'τ'"). Until a throws-status unification across
      the family exists, reject it up front.
    * RENAMED-TYPE-PARAMS — an overrider whose declared `typeArgs` are not the SAME
      names (in order) as the base declarer's. `appliedTagType` emits the overrider's own
      param names in the `is`/`as` tag-test, which the dispatcher's scope (carrying the
      base's params) cannot relate — a re-resolution `.strataBug`. The idiomatic
      same-named form (`SBox<T> extends Box<T>`) is fine; a renamed one is unsupported.
    * OUTPUT-SIGNATURE — an overrider that shares the base's non-`self` INPUT signature (so
      it IS a family member) but has an incompatible OUTPUT signature: a different number of
      outputs, or a return that is neither the same type as nor a subtype of the base's
      (`outputSignatureCompatible` rejects both; a covariant subtype return IS admitted). The
      dispatcher's branch call `O$m$impl(self as O, rest…)` assigns the base method's output
      list, so a mismatched arity or a non-covariant return yields a re-resolution
      `.strataBug`. (An INPUT-signature difference is not checked here: it makes the two
      methods Java OVERLOADS, which `isOverrideOf` keeps out of the family entirely — they
      lift as independent methods, never conflated into one dispatcher.)
    * EXTERNAL-IN-FAMILY — an overridden method (base or override) whose body is `external`
      (body-less). The dispatcher's if-chain needs a real `$impl` on every branch and a
      fallthrough; an external endpoint has none, so the lifted `T$m` would stay a plain
      `.External` proc while a receiver-passing branch call is synthesized against it — a
      re-resolution `.strataBug`. Reject the family; a NON-overridden external method still
      lifts unchanged (`.External => .External` in the generator).

    Consumes `virtualDispatchFamilies` — the single enumerator shared by the
    Liskov checker and the dispatcher generator, so the three passes range over
    exactly the same families by construction. -/
private def validateDispatchFamilies (model : SemanticModel) (families : List DispatchFamily)
    : List Message :=
  families.foldl (init := []) fun acc fam =>
        let ct := fam.owner; let baseM := fam.method
        -- Only the OWNER's own declaration drives one family's checks; each overrider is
        -- compared against THIS base. (A method declared on several levels is inspected
        -- once per declaring level, but the emitted diagnostics dedup by identical text
        -- rarely and are harmless — the first non-warning halts the pipeline regardless.)
        let overriders := fam.overriders
        overriders.foldl (init := acc) fun acc3 ov =>
          match findOverrideIn ov baseM with
          | none => acc3
          | some ovM =>
            let src := ovM.name.source
            -- Each guard emits a single clean `.userError` (diagnosticFromSource's default
            -- kind) when its shape is violated, else nothing — keeping the three arms uniform
            -- so none can drift onto a non-error kind (which would be soundness-relevant: a
            -- warning would not halt the pipeline before the synthetic if-chain hard-fails).
            let guardErr (cond : Bool) (msg : String) : List Message :=
              if cond then [diagnosticFromSource src msg] else []
            -- ASYMMETRIC-THROWS: throws-status must agree across the family.
            let d2 : List Message :=
              guardErr (baseM.throwsType.isSome != ovM.throwsType.isSome)
                  s!"dynamic dispatch does not yet support a family with mismatched `throws` clauses: '{ct.name.text}.{baseM.name.text}' {if baseM.throwsType.isSome then "declares" else "does not declare"} `throws` but its override on '{ov.name.text}' {if ovM.throwsType.isSome then "does" else "does not"}. Make the throws clauses uniform across the overriding family."
            -- RENAMED-TYPE-PARAMS: a generic base's overrider must repeat its type params verbatim
            -- (see the docstring); a renamed/concrete overrider is rejected. Non-generic base exempt.
            let d3 : List Message :=
              guardErr (!ct.typeArgs.isEmpty && ov.typeArgs.map (·.text) != ct.typeArgs.map (·.text))
                  s!"dynamic dispatch does not yet support an override of a generic method whose type parameters differ from the base: '{ov.name.text}' declares type parameters [{String.intercalate ", " (ov.typeArgs.map (·.text))}] but the overridden generic '{ct.name.text}' declares [{String.intercalate ", " (ct.typeArgs.map (·.text))}]. An overriding composite must repeat the base's type parameters verbatim (e.g. `SBox<T> extends Box<T>`)."
            -- OUTPUT-SIGNATURE: reject a differing output arity or a non-covariant return cleanly;
            -- a covariant return (subtype of the base's) is sound and admitted. See
            -- `outputSignatureCompatible`.
            let d4 : List Message :=
              guardErr (! outputSignatureCompatible model baseM ovM)
                  s!"override '{ov.name.text}.{ovM.name.text}' has an output signature incompatible with the method it overrides on '{ct.name.text}': each output must have the same type as, or a subtype of, the overridden method's corresponding output ({ovM.outputs.length} output(s) vs {baseM.outputs.length})."
            -- EXTERNAL-IN-FAMILY: an `external` (body-less) endpoint has no `$impl` for the
            -- dispatcher to call; reject either-endpoint-external (see docstring).
            let d5 : List Message :=
              guardErr (baseM.body.isExternal || ovM.body.isExternal)
                  s!"dynamic dispatch does not support an `external` method in an overriding family: '{if baseM.body.isExternal then ct.name.text else ov.name.text}.{baseM.name.text}' is `external` and has no body to dispatch. An overridden method and its overrides must all have bodies."
            acc3 ++ d2 ++ d3 ++ d4 ++ d5

end -- public section (shared family predicates)

/-- The type used in a dispatcher's `is`/`as` tag-test for branch type `ct`: a bare
    `.UserDefined` for a non-generic composite, but an applied `.Applied ct<T…>` for a
    generic one (a bare un-applied generic head is rejected by re-resolution's
    `Synth.isType`). The generic branch applies `ct` to its OWN declared params as
    `.TVar`s. For the idiomatic same-named override (`SBox<T> extends Box<T>`) these are
    exactly the dispatcher's params, so the tag-test resolves; a RENAMED override
    (`SBox<U> extends Box<U>`) would emit a param the dispatcher doesn't carry and is
    rejected fail-loud at re-resolution (never mis-verified). The dispatcher body and its
    tag-conditioned posts share this one constructor so they cannot dispatch on and test
    different types. -/
private def appliedTagType (src : FileRange) (ct : CompositeType) : HighTypeMd :=
  if ct.typeArgs.isEmpty then ⟨ .UserDefined ct.name, src ⟩
  else ⟨ .Applied ⟨ .UserDefined ct.name, src ⟩
        (ct.typeArgs.map (fun a => (⟨ .TVar a, src ⟩ : HighTypeMd))), src ⟩

/-- The dispatcher's receiver name: the method's first input. Shared by the dispatcher body
    and its tag-conditioned posts so the `is`/`as` branches and the `self is Oi ==> Oi.post`
    posts cannot drift onto different receiver names. The `mkId "self"` fallback is unreachable
    on the dispatch path — `sameNonSelfSignature` keeps a receiver-less method out of every
    dispatch family — and exists only to keep the function total. -/
private def dispatchSelfName (method : Procedure) : Identifier :=
  (method.inputs.head?.map (·.name)).getD (mkId "self")

/-- Build the dispatcher body for `method` on `ownerType`, branching over
    `overriders` (most-derived first) and falling through to `ownerType`'s own
    impl. Each branch casts `self` to the branch type (sound: guarded by the
    preceding `is`), then calls that type's `$impl`. Mirrors the hand-verified
    `if self is Sub then (self as Sub)#m_impl else …` dispatcher shape. -/
private def buildDispatcherBody (ownerType : Identifier) (method : Procedure)
    (overriders : List CompositeType) : AstNode StmtExpr :=
  let src := method.name.source
  let selfName := dispatchSelfName method
  let restArgs : List (AstNode StmtExpr) :=
    (method.inputs.drop 1).map fun p => ⟨ .Var (.Local p.name), src ⟩
  let callTo (target : Identifier) (recv : AstNode StmtExpr) : AstNode StmtExpr :=
    mkCallAssigningOutputs src target (recv :: restArgs) method.outputs
  -- the else (fallthrough): owner's own impl, self uncast (already : ownerType).
  -- Wrapped in a `.Block` so it is STRUCTURALLY symmetric with the `then` branches
  -- (which are blocks): an `if` synthesizes+joins both branch types, and a bare call
  -- vs a block-wrapped call can synthesize different types for a void heap-writer
  -- (whose `$heap`-threaded call resolves to `Heap` bare but `void` as a block tail),
  -- producing a spurious "'if' branches have incompatible types 'Heap' and 'void'".
  let fallthrough : AstNode StmtExpr :=
    ⟨ .Block [callTo (implProcName ownerType method.name) ⟨ .Var (.Local selfName), src ⟩] none, src ⟩
  -- fold the overriders into a most-derived-first `is`/`as` chain
  overriders.foldr (init := fallthrough) fun ov acc =>
    let ovTy : HighTypeMd := appliedTagType src ov
    let isCheck : AstNode StmtExpr := ⟨ .IsType ⟨ .Var (.Local selfName), src ⟩ ovTy, src ⟩
    let castName := dispatchCastName ov.name
    let castDecl : AstNode StmtExpr :=
      ⟨ .Assign [⟨ .Declare ⟨castName, ovTy⟩, src ⟩]
        ⟨ .AsType ⟨ .Var (.Local selfName), src ⟩ ovTy, src ⟩, src ⟩
    let branchCall := callTo (implProcName ov.name method.name) ⟨ .Var (.Local castName), src ⟩
    let thenBlock : AstNode StmtExpr := ⟨ .Block [castDecl, branchCall] none, src ⟩
    ⟨ .IfThenElse isCheck thenBlock (some acc), src ⟩

/-- The postconditions of `D$m`'s dispatcher, tag-conditioned so each holds on the
    branch that runs. Because `m` is opaque, callers reason against these (not the body):

    * owner `D`'s own posts, guarded `(!(self is O₁) & … & !(self is Oₙ)) ==> D.post` —
      they hold on the fallthrough path. The guard is NOT needed for provability: an
      UNguarded `D.post` is also discharged on every branch, because each override refines
      `D` (guaranteed by `CheckOverrideRefinement`), so `Oᵢ.post ⟹ D.post`. The guard is a
      DECOUPLING + PRECISION choice: it makes the dispatcher's own verification independent
      of the refinement check (a non-refining override then fails loudly in
      `CheckOverrideRefinement`, at the override, rather than here as an opaque
      `D$m$impl$post` failure), and it lets the per-tag clauses below carry the stronger
      per-override guarantee without the weaker `D.post` masking them. (The guard uses
      ancestor-membership `is`; since branches are checked most-derived-first the body still
      picks the right impl.)
    * each overrider `Oᵢ`'s posts, `(self is Oᵢ) ==> Oᵢ.post` — so a caller that knows
      the runtime tag (after `is`/`as`, or via a more-derived static type) recovers the
      override's STRONGER guarantee through a `D`-typed reference.

    SOUND: each clause is discharged by the matching dispatcher branch, whose `$impl`
    postcondition is exactly that type's post. (Cross-branch `is`-overlap — a deeper
    descendant `is` a shallower one — is handled by the body order and the guard; a
    Liskov-valid hierarchy keeps the clauses mutually consistent, since `Oᵢ.post ⟹ Oⱼ.post`
    whenever `Oᵢ <: Oⱼ`.) Overrider posts are renamed (self+outputs, positionally). -/
private def dispatcherPosts (ownerPosts : List Condition) (method : Procedure)
    (overriders : List CompositeType) : List Condition :=
  let src := method.name.source
  let selfName := dispatchSelfName method
  let isOf (ct : CompositeType) : StmtExprMd :=
    ⟨ .IsType ⟨ .Var (.Local selfName), src ⟩ (appliedTagType src ct), src ⟩
  let overriderPosts : List Condition := overriders.filterMap fun ov =>
    -- Pick the genuine override (an overrider may ALSO declare a same-name overload; only
    -- the signature-matching method is the one this dispatcher branch runs).
    match findOverrideIn ov method with
    | none => none
    | some ovProc =>
      let rename := renameProcLocals ovProc method
      match nonFreeConditions (bodyPostconditions ovProc.body) with
      | [] => none
      | ovPosts =>
        let conj := conjoinAnd src (ovPosts.map (fun c => rename c.condition))
        some { condition := impliesMd src (isOf ov) conj }
  let notAnyOverrider : StmtExprMd := conjoinAnd src (overriders.map (fun ov => notMd src (isOf ov)))
  let guardedOwnerPosts : List Condition := (nonFreeConditions ownerPosts).map fun c =>
    { c with condition := impliesMd src notAnyOverrider c.condition }
  guardedOwnerPosts ++ overriderPosts

public section

/--
Lift every `proc ∈ ct.instanceProcedures` to a top-level static procedure
named via `liftedProcName`, rewrite call sites that resolved to an instance
procedure, and clear `instanceProcedures` on every composite.
-/
def liftInstanceProcedures (model : SemanticModel) (program : Program) : Program × List Message :=
  -- Compute the virtual-dispatch families ONCE. Every downstream step — validation,
  -- Liskov checking (via the pass that shares this function), and dispatcher generation —
  -- consumes the same list, so the gate-parity invariant is structural and the per-family
  -- `descendantOverriders` call happens exactly once (previously 4× per virtual method).
  let families := virtualDispatchFamilies model program
  -- Step 0: reject dispatch families the generator cannot lower (asymmetric throws,
  -- renamed type params, arity mismatch) with a CLEAN diagnostic — the pipeline halts
  -- here rather than letting the synthetic if-chain hard-fail downstream as a StrataBug.
  let familyDiags := validateDispatchFamilies model families
  if familyDiags.any (·.kind != .warning) then (program, familyDiags) else
  -- Step 1: collect lifted clones. The lifted proc's type params are the composite's
  -- followed by the method's own: `get(self: Box<T>)` on `composite Box<T>` becomes
  -- `Box$get<T>(self: Box<T>)`, and `id2<U>(self: Box<T>)` becomes `Box$id2<T,U>`. The
  -- result is an ordinary polymorphic procedure with a generic-composite param — the
  -- shape the procedure monomorphizer (running AFTER this pass) already handles, so no
  -- new machinery is needed. A non-generic composite contributes `[]`, leaving a
  -- non-generic method's `typeArgs` unchanged.
  --
  -- A method in a virtual-dispatch family (looked up in the precomputed `families`) lifts to a
  -- dispatcher `T$m` + body `T$m$impl`; any other method is a plain static lift (see the section
  -- docstring). Keyed on the method's resolution `uniqueId` — NOT its text name, which same-
  -- composite overloads share (an unresolved method, no `uniqueId`, falls to the plain lift).
  let familyMap : Std.HashMap Nat DispatchFamily :=
    families.foldl (init := {}) fun m fam =>
      match fam.method.name.uniqueId with
      | some uid => m.insert uid fam
      | none => m
  let liftedProcs : List Procedure :=
    program.types.flatMap fun td =>
      match td with
      | .Composite ct =>
        ct.instanceProcedures.flatMap fun proc =>
          let tyArgs := ct.typeArgs ++ proc.typeArgs
          match proc.name.uniqueId.bind familyMap.get? with
          | none =>
            -- non-virtual method ⇒ plain static lift (unchanged behavior)
            [{ proc with name := liftedProcName ct.name proc.name, typeArgs := tyArgs }]
          | some fam =>
            -- virtual: real body → `T$m$impl`; `T$m` → dispatcher (same contract).
            let overriders := fam.overriders
            let impl := { proc with name := implProcName ct.name proc.name, typeArgs := tyArgs }
            let dispatcherBody : Body := match proc.body with
              | .Transparent _ => .Transparent (buildDispatcherBody ct.name proc overriders)
              | .Opaque posts _ modif =>
                  .Opaque (dispatcherPosts posts proc overriders)
                    (some (buildDispatcherBody ct.name proc overriders)) modif
              | .Abstract posts =>
                  .Opaque (dispatcherPosts posts proc overriders)
                    (some (buildDispatcherBody ct.name proc overriders)) []
              -- Unreachable for an OVERRIDDEN method: `validateDispatchFamilies`'
              -- EXTERNAL-IN-FAMILY guard rejects a family with an external endpoint before
              -- generation runs. Kept total for the match; an external body has nothing to
              -- dispatch, so it would stay external.
              | .External => .External
            let dispatcher := { proc with name := liftedProcName ct.name proc.name,
                                          typeArgs := tyArgs, body := dispatcherBody }
            [impl, dispatcher]
      | _ => []

  if liftedProcs.isEmpty then (program, []) else

  -- Step 2: move the lifted procs to static scope and clear instanceProcedures
  -- on every composite, so the whole program is in its final shape.
  let program := { program with
    staticProcedures := program.staticProcedures ++ liftedProcs
    types := program.types.map fun td =>
      match td with
      | .Composite ct => .Composite { ct with instanceProcedures := [] }
      | _ => td }

  -- Step 3: rewrite call sites everywhere expressions can appear (procedure
  -- bodies and contracts, constrained-type constraint/witness, constant
  -- initializers).
  (mapProgramStmtExpr (rewriteCallNode model) program, [])

end -- public section

/-- Pipeline pass: lift instance procedures to top-level static procedures
    and rewrite call sites to use the lifted names. -/
public def liftInstanceProceduresPass : LoweringPass where
  name := "LiftInstanceProcedures"
  documentation := "Lifts every procedure declared inside a `composite` block to a top-level static procedure named `<CompositeName>$<methodName>` and rewrites call sites resolved to an instance procedure (including `obj#method(args)` surface syntax) to point at the lifted name. Clears `instanceProcedures` on every composite. Must run before HeapParameterization."
  needsResolves := true
  run := fun _ p m => let (p', diags) := liftInstanceProcedures m p; (p', diags, {})
  comesBefore := [⟨ eliminateValueInReturnsPass.meta, "eliminateValueInReturns only applies to static methods, hence all instance methods must have been lifted before." ⟩]

end Strata.Laurel
