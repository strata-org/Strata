/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.LaurelTypes

/-!
# Monomorphize generic composites

Lowers user-level generic composites (`composite Box<T> { val: T }`) by emitting
one concrete composite per *used* instantiation (`Box<int>` → `Box$a1$int` with
`val: int`) and rewriting every `Box<int>` type reference — and the matching
`new Box` allocation — to the monomorphic name. After this pass no
`HighType.Applied` (over a generic composite) and no generic composite definition
remain, so all downstream passes (HeapParameterization, translation) see only
ordinary monomorphic composites.

Runs after resolution, before `HeapParameterization`. `needsResolves := true`
re-resolves the injected concrete composites.

Instantiations are collected from every type position (fields, datatype ctor args,
constants, static fields, procedure signatures, and body + contract statements) and
from `new C<τ>` allocation sites, then driven to a fixpoint by a depth-capped worklist
that also clones poly procedures materializing a generic composite. The pipeline reads,
top to bottom: `indexGenerics` → `collectSeeds` → fixpoint drain (`processWorklistItem`)
→ uncalled-proc witnesses → `topoSortMonomorphs` → rewrite all type/`new` positions.
-/

namespace Strata.Laurel

public section

/-- Tag for a `HighType` used as a type argument, or `none` if the type is one
    this monomorphizer can't yet name. Returning `none` (rather than a `_`
    catch-all) is important: an untaggable arg has no stable name to embed.

    NOT injective in general: the underlying `instTagCommon` joins nested arg tags
    with a bare `$`, which is injective only if no leaf name contains `$` — but `$`
    is a legal identifier char, so a user type literally named like a generated tag
    (`Box$a1$int`) or a `$` migrating across a comma (`Pair<X$Y,Z>` vs `Pair<X,Y$Z>`)
    can collapse two distinct instantiations to one tag. When that happens the
    worklist emits only the FIRST (dedup at `monomorphizeComposites`), so the second
    would silently reuse the first's field layout — EXCEPT the post-pass re-resolution
    net (`needsResolves := true`; see `LaurelCompilationPipeline.runLaurelPasses`)
    catches the divergent layout as a duplicate-definition / type error, failing loud
    rather than mis-verifying. Soundness here is therefore enforced downstream, not by
    this tag's injectivity; making the tag injective ($-escaping) is a possible
    hardening. See the injectivity caveat on `instTagCommon`. -/
partial def tyTag : HighType → Option String
  | .TVoid => some "void"           -- monomorphization accepts `void`; `.TCore` it does NOT
  | ty => instTagCommon tyTag ty    -- shared arms (incl. TMap/TSet); `none` on TVar/Pure/TCore/… (unsupported)

/-- Max nesting depth of a `HighType` (a flat type is depth 1; `Box<int>` is 2;
    `Box<Box<int>>` is 3). Used to detect a DIVERGENT recursive generic
    (`L<T>{ next: L<L<T>> }`), whose instantiations grow in depth without bound —
    so we cut them off with a real diagnostic at a shallow depth rather than
    grinding to a name-length limit while emitting dozens of dead monomorphs. -/
partial def tyDepth : HighType → Nat
  | .Applied b as => 1 + max (tyDepth b.val) ((as.map (fun a => tyDepth a.val)).foldl Nat.max 0)
  | .TSet vt | .Pure vt => 1 + tyDepth vt.val
  | .TMap kt vt => 1 + max (tyDepth kt.val) (tyDepth vt.val)
  | .Intersection ts => 1 + (ts.map (fun t => tyDepth t.val)).foldl Nat.max 0
  | _ => 1

/-- Structurally match a DECLARED type (which may mention type variables `.TVar`)
    against an ACTUAL type, accumulating bindings `tv ↦ actual`. This is the
    type-argument inference for procedure monomorphization: matching the declared
    param `Box<T>` against an arg of type `Box<int>` yields `T ↦ int`.

    Matching, not unification (binds a `.TVar` only on the DECLARED side): we infer one
    procedure's type args from a single call's arg types, so no two-sided `F<X>` vs `F<Y>`
    constraint ever arises. The actual side is NOT always ground — a pristine poly body's
    internal call can pass `b : Box<T>` — so matching may bind `T ↦ .TVar T`; that bogus
    binding isn't special-cased here but rejected by `inferProcInst`'s concreteness gate
    (every inferred arg must be `tyTag`-taggable), deferring the call until cloning makes
    the arg concrete. (The occurs-check analogue — a divergent recursive generic — is the
    worklist depth cap's job.)

    Returns the extended binding map, or `none` on a structural mismatch (different
    head constructors / arities) or an INCONSISTENT binding (a `tv` matched to two
    different types — a genuine type error the caller surfaces loudly).
    `acc` threads bindings across multiple parameters. -/
partial def matchTypeArg (declared actual : HighType)
    (acc : Std.HashMap String HighType) : Option (Std.HashMap String HighType) :=
  match declared with
  | .TVar tv =>
    match acc.get? tv.text with
    | some prev => if highEq ⟨prev, none⟩ ⟨actual, none⟩ then some acc else none  -- inconsistent
    | none => some (acc.insert tv.text actual)
  | .Applied db dargs =>
    match actual with
    | .Applied ab aargs =>
      if dargs.length != aargs.length then none
      -- SELF-GUARD: two `.UserDefined` heads with different base names must NOT match.
      -- The head recursion below binds nothing for `.UserDefined`/`.UserDefined` (it hits
      -- the catch-all), so without this `Box<T>` would structurally match `Pair<int>` on
      -- arity alone (MatchTypeArgTest case 5). No live wrong-accept today — the earlier
      -- gradual-assignability gate rejects such args — but this makes monomorphization
      -- self-guarding rather than trusting an upstream pass. Only the both-named-mismatch
      -- case is constrained; every other head shape keeps the prior behavior.
      else if (match db.val, ab.val with
               | .UserDefined dn, .UserDefined an => dn.text != an.text
               | _, _ => false) then none
      else
        -- match the head, then each arg positionally, threading `acc`
        match matchTypeArg db.val ab.val acc with
        | none => none
        | some acc1 =>
          (dargs.zip aargs).foldl (fun acc? (d, a) =>
            acc?.bind (fun m => matchTypeArg d.val a.val m)) (some acc1)
    | _ => none
  | .TSet dv => match actual with | .TSet av => matchTypeArg dv.val av.val acc | _ => none
  | .Pure dv => match actual with | .Pure av => matchTypeArg dv.val av.val acc | _ => none
  | .TMap dk dv => match actual with
    | .TMap ak av => (matchTypeArg dk.val ak.val acc).bind (fun m => matchTypeArg dv.val av.val m)
    | _ => none
  -- A concrete declared type (no tyvar) need only be consistent with the actual;
  -- we don't constrain it (any mismatch is a separate type error, not our concern).
  | _ => some acc

/-- Mangled monomorphic name for `C` instantiated at `args`, e.g. `Box$a1$int`,
    or `none` if any arg can't be tagged injectively. Identifier-legal only
    (these become Core/SMT sort names — no `«»`/`,`). -/
def monoName? (base : String) (args : List HighType) : Option String := do
  let tags ← args.mapM tyTag
  some s!"{base}$a{tags.length}${String.intercalate "$" tags}"

/-- Total version for call sites that have already validated the args (or for
    diagnostics). Falls back to a clearly-bogus name on un-taggable input so a
    missing validation surfaces downstream rather than silently colliding. -/
def monoName (base : String) (args : List HighType) : String :=
  (monoName? base args).getD s!"{base}$UNTAGGABLE"

-- `substTypeVars` moved to LaurelAST.lean (so `isSubtype` can reuse it for remap-aware
-- generic upcast without an import cycle). Re-exported transitively; callers here unchanged.

/-- Clear `uniqueId`s throughout a `HighType` so re-resolution assigns fresh ones.
    The generated composite's field types were resolved against the *generic*
    definition (with `.TVar` carrying ids); after substitution they must look
    unresolved to the post-pass `resolve`. -/
partial def clearTyIds (ty : HighTypeMd) : HighTypeMd :=
  let clr (i : Identifier) : Identifier := { i with uniqueId := none }
  let v := match ty.val with
    | .UserDefined n => .UserDefined (clr n)
    | .TVar n => .TVar (clr n)
    | .TSet et => .TSet (clearTyIds et)
    | .TMap kt vt => .TMap (clearTyIds kt) (clearTyIds vt)
    | .Applied base args => .Applied (clearTyIds base) (args.map clearTyIds)
    | .Pure b => .Pure (clearTyIds b)
    | .Intersection ts => .Intersection (ts.map clearTyIds)
    | other => other
  { val := v, source := ty.source }

/-- The instantiation key: `(generic composite name, concrete arg types)`. -/
abbrev Inst := String × List HighType

private def instKey (i : Inst) : String := monoName i.1 i.2

/-- A procedure instantiation: `(procName, typeArgs-in-declaration-order)`. Named
    with the same `monoName` scheme as composites (`idp$a1$int`), so a poly
    procedure `f<T>` called at `int` becomes the monomorphic proc `f$a1$int`. -/
abbrev ProcInst := String × List HighType

private def procInstKey (p : ProcInst) : String := monoName p.1 p.2

/-- The SINGLE source of truth for the instantiation an explicit `new C<τ…>`
    denotes. Returns `some (C, args)` exactly when the `new` carries explicit type
    args, `C` is a generic composite, and the args are taggable (else `none` →
    left generic, fails LOUD at re-resolution rather than silently coalescing).
    Both the COLLECT path (`collectInStmt`) and the REWRITE path (`rewriteStmt`'s
    `.New` arm) consume this one function, so they cannot drift on which monomorph
    a `new<>` denotes: collect turns the `Inst` into `instKey = monoName C args`,
    rewrite turns the same `Inst` into `mkId (monoName C args)`. -/
private def newInst? (genComposites : Std.HashMap String (List Identifier))
    (c : Identifier) (typeArgs : List HighTypeMd) : Option Inst :=
  if typeArgs.isEmpty then none
  else if genComposites.contains c.text then
    let argVals := typeArgs.map (·.val)
    (monoName? c.text argVals).map (fun _ => (c.text, argVals))
  else none

/-- Collect all `.Applied (UserDefined C) args` instantiations appearing in a
    `HighType`, where `C` is a generic composite in `genComposites`. -/
private partial def collectInTy (genComposites : Std.HashMap String (List Identifier))
    (ty : HighTypeMd) : List Inst :=
  let here : List Inst := match ty.val with
    | .Applied base args =>
      match base.val with
      | .UserDefined n =>
        let argVals := args.map (·.val)
        -- Only record instantiations we can name injectively. An un-taggable arg
        -- (Map/Set/TVar/…) is left as `.Applied` and fails LOUD at re-resolution
        -- (dangling generic), never silently coalesced into a shared mono name.
        if genComposites.contains n.text && (monoName? n.text argVals).isSome
        then [(n.text, argVals)] else []
      | _ => []
    | _ => []
  let nested : List Inst := match ty.val with
    | .Applied base args => collectInTy genComposites base ++ args.flatMap (collectInTy genComposites)
    | .TSet vt | .Pure vt => collectInTy genComposites vt
    | .TMap kt vt => collectInTy genComposites kt ++ collectInTy genComposites vt
    | .Intersection ts => ts.flatMap (collectInTy genComposites)
    | _ => []
  here ++ nested

/-- Does `ty` materialize a generic composite at one of the type variables in
    `tvSet`? (An `.Applied (UserDefined C) args` over a generic composite `C` where
    some arg is a `.TVar tv` with `tv ∈ tvSet`, searched recursively.) A pure type
    predicate; the caller (`mentionsGenericComposite`) applies it across a procedure's
    signature types, body type slots, and `new`-site types to decide the proc must be
    monomorphized rather than freshened (a generic composite has no uniform Core
    representation the freshening path can use). -/
private partial def tyHasGenCompAtTVar (genComposites : Std.HashMap String (List Identifier))
    (tvSet : Std.HashSet String) (ty : HighType) : Bool :=
  match ty with
  | .Applied base args =>
    let hereHit :=
      (match base.val with | .UserDefined n => genComposites.contains n.text | _ => false)
        && args.any (fun a => match a.val with | .TVar tv => tvSet.contains tv.text | _ => false)
    hereHit || tyHasGenCompAtTVar genComposites tvSet base.val
      || args.any (fun a => tyHasGenCompAtTVar genComposites tvSet a.val)
  | .TSet vt | .Pure vt => tyHasGenCompAtTVar genComposites tvSet vt.val
  | .TMap kt vt => tyHasGenCompAtTVar genComposites tvSet kt.val || tyHasGenCompAtTVar genComposites tvSet vt.val
  | .Intersection ts => ts.any (fun t => tyHasGenCompAtTVar genComposites tvSet t.val)
  | _ => false

/-- Rewrite a `HighType`: every `.Applied (UserDefined C) args` over a generic
    composite becomes `.UserDefined (monoName C args)`. -/
private partial def rewriteTy (genComposites : Std.HashMap String (List Identifier))
    (ty : HighTypeMd) : HighTypeMd :=
  let v := match ty.val with
    | .Applied base args =>
      match base.val with
      | .UserDefined n =>
        -- Only rewrite taggable instantiations (those collection emitted a
        -- composite for). Un-taggable ones stay `.Applied` → loud resolution
        -- failure, not a dangling `UNTAGGABLE` reference.
        match (if genComposites.contains n.text then monoName? n.text (args.map (·.val)) else none) with
        | some mn => .UserDefined (mkId mn)
        | none => .Applied (rewriteTy genComposites base) (args.map (rewriteTy genComposites))
      | _ => .Applied (rewriteTy genComposites base) (args.map (rewriteTy genComposites))
    | .TSet et => .TSet (rewriteTy genComposites et)
    | .TMap kt vt => .TMap (rewriteTy genComposites kt) (rewriteTy genComposites vt)
    | .Pure b => .Pure (rewriteTy genComposites b)
    | .Intersection ts => .Intersection (ts.map (rewriteTy genComposites))
    | other => other
  { val := v, source := ty.source }

/-- The `HighType` annotation slots carried *directly* by a single `StmtExpr`
    node (NOT its sub-expressions — `mapStmtExpr` recurses into those and visits
    every node, so this need only report the node's own type slots). This is the
    one place the set of statement-level type positions is enumerated; both
    `collectInStmt` and `rewriteStmt` are derived from it, so they cannot drift
    apart and silently miss a position. -/
private def stmtTypeSlots (e : StmtExprMd) : List HighTypeMd :=
  match e.val with
  | .Assign targets _ =>
    targets.filterMap fun t => match t.val with
      | .Declare param => some param.type
      | _ => none
  -- A standalone declaration with no initializer (`var b: Box<int>;`) parses to
  -- `.Var (.Declare …)`, distinct from the initialized `.Assign [.Declare …] e` above.
  | .Var (.Declare param) => [param.type]
  | .AsType _ ty => [ty]
  | .IsType _ ty => [ty]
  | .Quantifier _ param _ _ => [param.type]
  | .Hole _ (some ty) => [ty]
  -- `new C<τ…>` is an instantiation site too, but it is NOT a type *slot*: its
  -- instantiation is derived by the shared `newInst?` helper (consumed by both
  -- `collectInStmt` and `rewriteStmt`), not via a synthesized `.Applied` type.
  | _ => []

/-- Rewrite types and `new` sites inside a single `StmtExpr` node (applied
    bottom-up by `mapStmtExpr`). Rewrites every type slot reported by
    `stmtTypeSlots` (Declare-target types, `as`/`is` type operands, quantifier
    binder types, inferred hole types), and additionally correlates the
    `var b: Box<int> := new Box` allocation: an `Assign` whose sole target is a
    `Declare` with an `.Applied(C)` type and whose RHS is `new C` — rewrite the
    RHS to `new (monoName C args)` so the allocation matches the declared type. -/
private def rewriteStmt (genComposites : Std.HashMap String (List Identifier))
    (e : StmtExprMd) : StmtExprMd :=
  let rw := rewriteTy genComposites
  -- Rewrite a generic `new C<τ…>` to the monomorphic `new C$…` using the
  -- allocation site's OWN explicit type arguments. Position-independent: works
  -- wherever a `new` appears (field write, return, call arg, …) without
  -- recovering the instantiation from surrounding context. Returns `none` if the
  -- `new` is not a generic composite or its args can't be tagged (→ left as-is;
  -- a bare generic `new C` with no args is caught downstream / by the legacy
  -- Declare-correlation below). -/
  let rewriteNew (c : Identifier) (typeArgs : List HighTypeMd) : Option Identifier :=
    (newInst? genComposites c typeArgs).map (fun i => mkId (monoName i.1 i.2))
  -- NOTE: this rewrites `new C<τ>` to its monomorph using the args AT THE SITE. The
  -- args-vs-declared-type mismatch `var b: Box<bool> := new Box<int>` is caught EAGERLY
  -- by #1121's gradual checker at resolution (before this pass runs), so it never reaches
  -- here. See the "ASSIGNABILITY" note in Resolution.lean. (Only the bare `new C` form,
  -- which carries no args to mismatch, stays permissive by design.)
  let val' := match e.val with
    | .New c typeArgs =>
      match rewriteNew c typeArgs with
      | some mn => .New mn []
      | none => e.val
    | .Assign targets value =>
      let targets' := targets.map fun t =>
        match t.val with
        | .Declare param => { t with val := .Declare { param with type := rw param.type } }
        | _ => t
      -- Legacy backward-compat: a BARE `new C` (no explicit args) as the RHS of a
      -- single `var x: C<τ> := new C` recovers `τ` from the declared type. With
      -- explicit `new C<τ>` syntax this is handled by the `.New` case above; this
      -- keeps pre-existing arg-less programs working.
      let value' :=
        match targets, value.val with
        | [⟨.Declare param, _⟩], .New c [] =>
          match param.type.val with
          | .Applied base args =>
            match base.val with
            | .UserDefined n =>
              match (if genComposites.contains n.text && n.text == c.text
                     then monoName? n.text (args.map (·.val)) else none) with
              | some mn => { value with val := .New (mkId mn) [] }
              | none => value
            | _ => value
          | _ => value
        | _, _ => value
      .Assign targets' value'
    | .Var (.Declare param) => .Var (.Declare { param with type := rw param.type })
    | .AsType target ty => .AsType target (rw ty)
    | .IsType target ty => .IsType target (rw ty)
    | .Quantifier mode param trigger body =>
      .Quantifier mode { param with type := rw param.type } trigger body
    | .Hole det (some ty) => .Hole det (some (rw ty))
    | other => other
  { e with val := val' }

/-- Collect instantiations from a single `StmtExpr` node's embedded types. Driven
    off `stmtTypeSlots` for type-annotation positions, PLUS the `new C<τ…>`
    allocation site via the shared `newInst?` helper — the SAME function
    `rewriteStmt`'s `.New` arm consumes, so collect and rewrite cannot disagree on
    which monomorph a `new<>` denotes (the anti-drift guarantee). -/
private def collectInStmt (genComposites : Std.HashMap String (List Identifier))
    (e : StmtExprMd) : List Inst :=
  let fromSlots := (stmtTypeSlots e).flatMap (collectInTy genComposites)
  let fromNew := match e.val with
    | .New c typeArgs => (newInst? genComposites c typeArgs).toList
    | _ => []
  fromSlots ++ fromNew

/-! ### Procedure monomorphization — clone a poly proc at a concrete inst -/

/-- Specialize ONE `StmtExpr` node for a clone: (1) apply the type-var substitution
    to its type slots (Declare types, `as`/`is`, quantifier binder, hole, `new C<τ>`
    args), AND (2) CLEAR the uniqueIds on its binders/references (Local, Field name,
    Declare name, StaticCall callee, quantifier param). The id-clear is LOAD-BEARING:
    re-resolution KEEPS an existing uniqueId rather than reassigning, so two clones
    of one source that retain the original ids cross-link — `unbox$a1$int`'s `r`
    merges with `unbox$a1$bool`'s `r`, "Impossible to unify bool with int". Clearing
    forces re-resolution to rebuild each clone's ids independently. Recursion into
    sub-expressions is handled by `mapStmtExpr`. -/
private def substTypeVarsInStmtNode (subst : Std.HashMap String HighTypeMd)
    (e : StmtExprMd) : StmtExprMd :=
  let s := substTypeVars subst
  let clr (i : Identifier) : Identifier := { i with uniqueId := none }
  let clrParam (p : Parameter) : Parameter := { p with name := clr p.name }
  let val' := match e.val with
    | .New c typeArgs => .New (clr c) (typeArgs.map s)
    | .Var (.Local n) => .Var (.Local (clr n))
    | .Var (.Field tgt fn) => .Var (.Field tgt (clr fn))
    | .StaticCall callee args => .StaticCall (clr callee) args
    | .Assign targets value =>
      let targets' := targets.map fun t =>
        match t.val with
        | .Declare param => { t with val := .Declare (clrParam { param with type := s param.type }) }
        | .Local n => { t with val := .Local (clr n) }
        | .Field tgt fn => { t with val := .Field tgt (clr fn) }
      .Assign targets' value
    | .AsType target ty => .AsType target (s ty)
    | .IsType target ty => .IsType target (s ty)
    | .Quantifier mode param trigger body =>
      .Quantifier mode (clrParam { param with type := s param.type }) trigger body
    | .Hole det (some ty) => .Hole det (some (s ty))
    | other => other
  { e with val := val' }

/-- Specialize a `StmtExpr` (proc body / contract / measure) to a concrete
    instantiation: substitute type vars in every node's type slots. (uniqueIds are
    cleared on the cloned proc's signature types via `cloneProcAt`; the body keeps
    its structure, and `needsResolves` re-resolves the clone.) -/
private def substTypeVarsInBody (subst : Std.HashMap String HighTypeMd)
    (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (substTypeVarsInStmtNode subst) e

/-- Clone a polymorphic `Procedure` at a concrete type-arg substitution: substitute
    through inputs, outputs, preconditions, decreases, and the body; rename to
    `newName`; set `typeArgs := []` (now monomorphic). Clears uniqueIds on the
    substituted signature types so the clone re-resolves independently — LOAD-BEARING
    (two clones sharing ids cross-link at re-resolution). -/
private def cloneProcAt (proc : Procedure) (subst : Std.HashMap String HighTypeMd)
    (newName : String) : Procedure :=
  let sTy (t : HighTypeMd) : HighTypeMd := clearTyIds (substTypeVars subst t)
  -- clear the param NAME's id too (not just the type's), so each clone's formals
  -- re-resolve independently (see substTypeVarsInStmtNode's id-clear rationale).
  let sParam (p : Parameter) : Parameter := { p with name := { p.name with uniqueId := none }, type := sTy p.type }
  let sCond (c : Condition) : Condition := { c with condition := substTypeVarsInBody subst c.condition }
  let body' : Body := match proc.body with
    | .Transparent b => .Transparent (substTypeVarsInBody subst b)
    | .Opaque posts impl mods =>
      .Opaque (posts.map sCond) (impl.map (substTypeVarsInBody subst)) (mods.map (substTypeVarsInBody subst))
    | .Abstract posts => .Abstract (posts.map sCond)
    | .External => .External
  { proc with
    name := mkId newName,
    typeArgs := [],
    inputs := proc.inputs.map sParam,
    outputs := proc.outputs.map sParam,
    preconditions := proc.preconditions.map sCond,
    decreases := proc.decreases.map (substTypeVarsInBody subst),
    -- `invokeOn` carries type vars too; substitute + id-clear it like the other
    -- expression positions (else `proc with` would keep the un-substituted original).
    invokeOn := proc.invokeOn.map (substTypeVarsInBody subst),
    body := body' }

/-- Infer a procedure instantiation from a call site: match each declared input
    type against the corresponding argument's type (via `matchTypeArg`), then order
    the resulting type-var bindings by the procedure's declared `typeArgs`. Returns
    `none` if a binding is missing/inconsistent or arities differ — the call then
    can't be monomorphized and is left for the loud downstream failure. `argTys` are
    the actual argument types (from `computeExprType` at the call).

    CONCRETENESS GATE: every inferred type arg must be `tyTag`-taggable (fully
    concrete — no `.TVar`). This is load-bearing for the step-4 fixpoint: scanning a
    poly proc's PRISTINE body sees its own internal poly calls over still-abstract
    args (`outer<T>`'s body calls `inner(b)` with `b : Box<T>`), and `matchTypeArg`
    would bind `T := .TVar T` — a bogus instantiation that clones an `inner$UNTAGGABLE`
    whose signature still carries `Box<T>`, surviving to Core ("generic type
    application reached Core translation"). Rejecting un-taggable bindings here means
    those abstract internal calls are discovered ONLY when concrete — i.e. during
    cloning, by `discoverRewritePolyCalls`, after `subst` makes the arg concrete. -/
private def inferProcInst (proc : Procedure) (argTys : List HighTypeMd)
    : Option ProcInst :=
  if proc.inputs.length != argTys.length then none
  else
    let bindings? := (proc.inputs.zip argTys).foldl
      (fun acc? (param, aty) => acc?.bind (fun m => matchTypeArg param.type.val aty.val m))
      (some (∅ : Std.HashMap String HighType))
    bindings?.bind fun bindings =>
      let ordered := proc.typeArgs.map (fun tv => bindings.get? tv.text)
      if ordered.all (·.isSome) && (ordered.filterMap id).all (fun t => (tyTag t).isSome)
      then some (proc.name.text, ordered.filterMap id) else none

/-- Discover and rewrite polymorphic-procedure CALLS inside a (pristine, resolved)
    procedure's StmtExpr slots — preconditions, decreases, invokeOn, and body — under
    a concrete `subst`. This is the procedure→procedure edge of the fixpoint (step 4):
    a cloned `outer<T>`'s body may call another poly proc `inner<T>(b: Box<T>)`.

    For each `StaticCall` to an indexed poly procedure, infer the callee's
    instantiation from the call's argument types. Those types are computed against the
    PRISTINE body via `computeExprType model` — this MUST happen before cloning, since
    the clone's ids are cleared and absent from `model` — then pushed through `subst`,
    so an abstract `Box<T>` argument inside `outer`'s generic body resolves to the
    concrete `Box<int>` once `outer` is cloned at int. Returns the procedure with each
    such callee rewritten to its monomorph name (`procInstKey`), plus the discovered
    `ProcInst`s for the worklist to clone.

    A call whose args don't yield a concrete binding — e.g. a poly-call RESULT passed
    straight into another poly call, which bottom-up traversal has already renamed so
    its output type is no longer model-resolvable — is LEFT unchanged and NOT
    discovered. It then fails LOUD downstream (dangling poly callee at translation)
    rather than silently mis-monomorphizing. This is the step-4 scope boundary; the
    common shape (the inner call's arg is a parameter or declared local) is handled. -/
private def discoverRewritePolyCalls (model : SemanticModel)
    (polyProcDefs : Std.HashMap String Procedure)
    (subst : Std.HashMap String HighTypeMd) (pproc : Procedure)
    : Procedure × List ProcInst :=
  let nodeFn (e : StmtExprMd) : StateM (List ProcInst) StmtExprMd := do
    match e.val with
    | .StaticCall callee args =>
      match polyProcDefs.get? callee.text with
      | some calleeDef =>
        let argTys := args.map (fun a => substTypeVars subst (computeExprType model a))
        match inferProcInst calleeDef argTys with
        | some pinst =>
          modify (· ++ [pinst])
          pure { e with val := .StaticCall (mkId (procInstKey pinst)) args }
        | none => pure e
      | none => pure e
    | _ => pure e
  (mapProcedureM (mapStmtExprM nodeFn) pproc).run []

/-- Collect generic-composite instantiations from a procedure's body StmtExpr type
    slots (Declare types, `as`/`is`, quantifier binders, `new C<τ>`). Purely
    structural (no `model`), so it runs on a CLONED proc whose ids are cleared —
    closing the gap where a poly body declaring `var x: Box<T>` would, after cloning
    at int, need `Box$int` emitted (the keystone seeded only from clone signatures). -/
private def procBodyCompInsts (genComposites : Std.HashMap String (List Identifier))
    (proc : Procedure) : List Inst :=
  ((mapProcedureM (m := StateM (List Inst))
    (mapStmtExprM (fun e => do modify (· ++ collectInStmt genComposites e); pure e)) proc).run []).2

/-- Mutable state threaded through the monomorphization worklist drain: the emitted
    monomorphs/clones, the dedup sets, accumulated diagnostics, and the pending worklist. -/
structure MonoState where
  monoComposites : List TypeDefinition
  procClones     : List Procedure
  emitted        : Std.HashSet String     -- composite instKeys already emitted
  clonedProcs    : Std.HashSet String     -- procInstKeys already cloned
  clonedBases    : Std.HashSet String     -- base proc NAMES that produced ≥1 clone
  diags          : List DiagnosticModel
  rejectedBases  : Std.HashSet String     -- bases already diagnosed (dedup)
  worklist       : List (Sum Inst ProcInst)

/-- Process ONE worklist item (a composite instantiation `.inl` or a procedure
    instantiation `.inr`): if its type-arg depth exceeds `maxInstDepth` reject it loud
    (once per base); otherwise emit the monomorph / clone and enqueue any new
    instantiations its substituted fields / signature / body reach. Shared by both
    worklist drains (the main drain and the post-witness drain), which differ only in
    what they seed. Returns the updated state. -/
def processWorklistItem (genComposites : Std.HashMap String (List Identifier))
    (genDefs : Std.HashMap String CompositeType) (polyProcDefs : Std.HashMap String Procedure)
    (model : SemanticModel) (maxInstDepth : Nat) (item : Sum Inst ProcInst) (s : MonoState)
    : MonoState := Id.run do
  let tooDeep (args : List HighType) : Bool := (args.map tyDepth).foldl Nat.max 0 > maxInstDepth
  let rejectDiag (base kind : String) : DiagnosticModel :=
    diagnosticFromSource none
      s!"recursive generic {kind} '{base}' is not supported: its instantiations grow without bound (depth exceeds {maxInstDepth})"
      DiagnosticType.NotYetImplemented
  let mut s := s
  match item with
  | .inl (cname, args) =>
    if tooDeep args then
      unless s.rejectedBases.contains cname do
        s := { s with rejectedBases := s.rejectedBases.insert cname,
                      diags := s.diags ++ [rejectDiag cname "composite"] }
    else unless s.emitted.contains (monoName cname args) do
      s := { s with emitted := s.emitted.insert (monoName cname args) }
      match genDefs.get? cname with
      | some ct =>
        let subst : Std.HashMap String HighTypeMd :=
          (ct.typeArgs.zip args).foldl (fun m (tv, a) => m.insert tv.text ⟨a, none⟩) {}
        let fields' := ct.fields.map fun f =>
          { name := { f.name with uniqueId := none }, isMutable := f.isMutable,
            type := clearTyIds (rewriteTy genComposites (substTypeVars subst f.type)) }
        -- Feedback edge: SUBSTITUTED field types are where new composite instantiations
        -- hide; enqueue any not-yet-emitted one (depth checked on dequeue).
        for f in ct.fields do
          for inst in collectInTy genComposites (substTypeVars subst f.type) do
            unless s.emitted.contains (monoName inst.1 inst.2) do
              s := { s with worklist := s.worklist ++ [.inl inst] }
        -- `extending`: substitute the child's type args into each parent, then rewrite
        -- generic instantiations to their mono name (concrete `Base` unchanged; generic
        -- `Base<T>` → `Base$int`). Also collect the substituted parent inst so `Base$int`
        -- is emitted (and topo-ordered before this child).
        let extending' := ct.extending.map fun p =>
          clearTyIds (rewriteTy genComposites (substTypeVars subst p))
        for p in ct.extending do
          for inst in collectInTy genComposites (substTypeVars subst p) do
            unless s.emitted.contains (monoName inst.1 inst.2) do
              s := { s with worklist := s.worklist ++ [.inl inst] }
        s := { s with monoComposites := s.monoComposites ++ [.Composite {
          name := mkId (monoName cname args), typeArgs := [], extending := extending',
          fields := fields', instanceProcedures := [] }] }
      | none => pure ()
  | .inr (pname, targs) =>
    if tooDeep targs then
      unless s.rejectedBases.contains pname do
        s := { s with rejectedBases := s.rejectedBases.insert pname,
                      diags := s.diags ++ [rejectDiag pname "procedure"] }
    else unless s.clonedProcs.contains (procInstKey (pname, targs)) do
      s := { s with clonedProcs := s.clonedProcs.insert (procInstKey (pname, targs)),
                    clonedBases := s.clonedBases.insert pname }
      match polyProcDefs.get? pname with
      | some pproc =>
        let subst : Std.HashMap String HighTypeMd :=
          (pproc.typeArgs.zip targs).foldl (fun m (tv, a) => m.insert tv.text ⟨a, none⟩) {}
        -- proc→proc edge: discover+rewrite poly calls in the PRISTINE body (model intact),
        -- enqueueing each callee instantiation; then clone the rewritten proc.
        let (pproc', discovered) := discoverRewritePolyCalls model polyProcDefs subst pproc
        let clone := cloneProcAt pproc' subst (monoName pname targs)
        s := { s with procClones := s.procClones ++ [clone] }
        for di in discovered do
          unless s.clonedProcs.contains (procInstKey di) do
            s := { s with worklist := s.worklist ++ [.inr di] }
        -- composite instantiations from the clone's signature AND body.
        for p in pproc.inputs ++ pproc.outputs do
          for inst in collectInTy genComposites (substTypeVars subst p.type) do
            unless s.emitted.contains (monoName inst.1 inst.2) do
              s := { s with worklist := s.worklist ++ [.inl inst] }
        for inst in procBodyCompInsts genComposites clone do
          unless s.emitted.contains (monoName inst.1 inst.2) do
            s := { s with worklist := s.worklist ++ [.inl inst] }
      | none => pure ()
  return s

/-- Drain the worklist to a fixpoint, processing one item per step via
    `processWorklistItem`, up to `fuel` steps. `fuel` is a coarse backstop; the real
    divergence guard is `maxInstDepth` (checked inside the helper). Returns the final
    state — a non-empty `worklist` means fuel ran out (the caller fails loud). Both
    drains in `monomorphizeComposites` (the main drain and the post-witness drain) go
    through this, so they can't drift. -/
def drainWorklist (genComposites : Std.HashMap String (List Identifier))
    (genDefs : Std.HashMap String CompositeType) (polyProcDefs : Std.HashMap String Procedure)
    (model : SemanticModel) (maxInstDepth : Nat) : Nat → MonoState → MonoState
  | 0, s => s
  | fuel+1, s =>
    match s.worklist with
    | [] => s
    | item :: rest =>
      drainWorklist genComposites genDefs polyProcDefs model maxInstDepth fuel
        (processWorklistItem genComposites genDefs polyProcDefs model maxInstDepth item { s with worklist := rest })

/-- Topologically order monomorph composites by the `extends` relation so a monomorph
    PARENT precedes its monomorph CHILD. The worklist is FIFO and a child enqueues its
    parent AFTER itself (child-before-parent), but re-resolution builds a composite's
    inherited field-scope by reading the parent's already-built scope in `program.types`
    LIST ORDER — so a monomorph parent must come first. Stable DFS post-order over the
    intra-`mono` `extending` edges; a `visiting` guard makes a malformed cycle terminate
    rather than hang (valid programs are acyclic). Concrete parents live elsewhere
    (emitted before all monomorphs), so only monomorph→monomorph edges matter here. -/
def topoSortMonomorphs (mono : List TypeDefinition) : List TypeDefinition := Id.run do
  -- Index every composite by name to look up a parent for ORDERING. NOTE: when the input
  -- is the WHOLE type list (concrete `types'` ++ `monoComposites`), a USER composite can
  -- share a name with a monomorph (`composite Box$a1$int` vs the `Box<int>` monomorph — the
  -- `$`-tag non-injectivity). That name-collision MUST be preserved as TWO entries so the
  -- re-resolution net reports the duplicate-definition; so emission is tracked by LIST INDEX,
  -- not by name. `monoByName` (last-write-wins on a dup) is used only to pick *a* parent to
  -- order before — harmless, since both collided entries land adjacent regardless.
  let arr := mono.toArray
  let monoNames : Std.HashSet String :=
    arr.foldl (fun s td => match td with | .Composite c => s.insert c.name.text | _ => s) {}
  let firstIdxByName : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for h : i in [0:arr.size] do
      match arr[i] with
      | .Composite c => unless m.contains c.name.text do m := m.insert c.name.text i
      | _ => pure ()
    return m
  let mut out : List TypeDefinition := []
  let mut placed : Std.HashSet Nat := {}        -- emitted entries, by INDEX (so dups both emit)
  -- visit the entry at `idx`, emitting its in-list parents (by name → first index) first
  let rec visit (fuel : Nat) (visiting : Std.HashSet Nat)
      (idx : Nat) (acc : List TypeDefinition × Std.HashSet Nat)
      : List TypeDefinition × Std.HashSet Nat :=
    match fuel with
    | 0 => acc
    | fuel'+1 =>
      let (out, placed) := acc
      if placed.contains idx || visiting.contains idx then (out, placed)
      else match arr[idx]? with
        | some (.Composite c) =>
          let acc' := c.extending.foldl (fun a p =>
            match highBaseName? p.val with
            | some pn =>
              if monoNames.contains pn.text then
                match firstIdxByName.get? pn.text with
                | some pIdx => visit fuel' (visiting.insert idx) pIdx a
                | none => a
              else a
            | none => a) (out, placed)
          let (out', placed') := acc'
          (out' ++ [.Composite c], placed'.insert idx)
        | some other => (out ++ [other], placed.insert idx)
        | none => (out, placed)
  let fuel := arr.size + 1
  for h : i in [0:arr.size] do
    let (out', placed') := visit fuel {} i (out, placed)
    out := out'; placed := placed'
  return out

/-- Index the program's generic entities: the generic composites (name → type params,
    name → definition), and the poly procedures that MATERIALIZE a generic composite at
    one of their own type vars — in the SIGNATURE (`f<T>(b: Box<T>)`) OR the BODY
    (`var t: Box<T>`). Those monomorphize per call site; a poly proc touching no generic
    composite at its typevar (`idp<T>(x:T)`) stays on the CallElim freshening path (the
    hybrid). The body case is load-bearing: a body-local `Box<T>` on the freshening path
    has no Core representation, so its field write would survive un-lowered (a StrataBug). -/
def indexGenerics (program : Program) (model : SemanticModel)
    : Std.HashMap String (List Identifier) × Std.HashMap String CompositeType × Std.HashMap String Procedure :=
  Id.run do
  let mut genComposites : Std.HashMap String (List Identifier) := {}
  let mut genDefs : Std.HashMap String CompositeType := {}
  for td in program.types do
    match td with
    | .Composite ct => if !ct.typeArgs.isEmpty then
        genComposites := genComposites.insert ct.name.text ct.typeArgs
        genDefs := genDefs.insert ct.name.text ct
    | _ => pure ()
  let mentionsGenericComposite (p : Procedure) : Bool :=
    let tvSet : Std.HashSet String := p.typeArgs.foldl (fun s tv => s.insert tv.text) {}
    let hitsTV (ty : HighTypeMd) : Bool := tyHasGenCompAtTVar genComposites tvSet ty.val
    let inSig := (p.inputs ++ p.outputs).any (fun param => hitsTV param.type)
    -- Body: any statement TYPE SLOT, OR a `new C<τ…>` site. We get the `new` site's
    -- instantiation for free from `computeExprType` — a `.New` node's type IS
    -- `.Applied (UserDefined C) typeArgs` (LaurelTypes.lean) — so the SAME `hitsTV`
    -- predicate covers slots and `new` uniformly, with no inline re-derivation of what
    -- a `new` denotes (avoids drift from the `stmtTypeSlots`/`newInst?` split).
    let inBody := ((mapProcedureM (m := StateM Bool)
      (mapStmtExprM (fun e => do
        let slotHit := (stmtTypeSlots e).any hitsTV
        let newHit := match e.val with | .New .. => hitsTV (computeExprType model e) | _ => false
        if slotHit || newHit then modify (fun _ => true)
        pure e)) p).run false).2
    inSig || inBody
  let mut polyProcDefs : Std.HashMap String Procedure := {}
  for proc in program.staticProcedures do
    if !proc.typeArgs.isEmpty && mentionsGenericComposite proc then
      polyProcDefs := polyProcDefs.insert proc.name.text proc
  return (genComposites, genDefs, polyProcDefs)

/-- Collect the SEED instantiations to start the worklist from: every COMPOSITE
    instantiation in a type position (composite fields, datatype ctor args, constants,
    static fields, proc params/outputs, and body+contract statement types), keyed by
    `instKey`; plus every PROCEDURE instantiation at a call site to an indexed poly proc,
    inferred from the arg types via `inferProcInst`, keyed by `procInstKey`. -/
def collectSeeds (program : Program) (model : SemanticModel)
    (genComposites : Std.HashMap String (List Identifier))
    (polyProcDefs : Std.HashMap String Procedure)
    : Std.HashMap String Inst × Std.HashMap String ProcInst := Id.run do
  let mut insts : Std.HashMap String Inst := {}
  let recordInsts (is : List Inst) (m : Std.HashMap String Inst) : Std.HashMap String Inst :=
    is.foldl (fun m i => m.insert (instKey i) i) m
  -- field types of all composites + datatype constructor arg types
  for td in program.types do
    match td with
    | .Composite ct =>
        for f in ct.fields do insts := recordInsts (collectInTy genComposites f.type) insts
        -- `extending`: a (typically non-generic) composite that extends a generic
        -- INSTANTIATION (`IntBox extends Box<int>`) needs that parent monomorph
        -- (`Box$a1$int`) emitted — else the rewritten `extends` reference dangles.
        -- (For a GENERIC composite being cloned, the substituted-parent seed is enqueued
        -- inside the worklist; this is the SEED for the non-cloned, concrete case.)
        for p in ct.extending do insts := recordInsts (collectInTy genComposites p) insts
    | .Datatype dt =>
        for ctor in dt.constructors do
          for arg in ctor.args do insts := recordInsts (collectInTy genComposites arg.type) insts
    | _ => pure ()
  -- top-level constants and global (static) fields
  for c in program.constants do insts := recordInsts (collectInTy genComposites c.type) insts
  for f in program.staticFields do insts := recordInsts (collectInTy genComposites f.type) insts
  -- procedure params/outputs
  for proc in program.staticProcedures do
    for p in proc.inputs do insts := recordInsts (collectInTy genComposites p.type) insts
    for p in proc.outputs do insts := recordInsts (collectInTy genComposites p.type) insts
  -- body + contract statements: `mapProcedureM` covers the body AND
  -- preconditions/decreases/invokeOn (so a generic in a contract is seeded too); it
  -- applies its function to each statement ROOT, so wrap in `mapStmtExprM` to recurse
  -- into every node (the var-decl `Assign`/`Declare` lives inside the body Block).
  for proc in program.staticProcedures do
    let (_, insts') := (mapProcedureM (m := StateM (Std.HashMap String Inst))
      (fun root => mapStmtExprM
        (fun e => do modify (recordInsts (collectInStmt genComposites e)); pure e) root) proc).run insts
    insts := insts'
  -- procedure instantiations from call sites to an indexed poly procedure.
  let mut procInsts : Std.HashMap String ProcInst := {}
  for proc in program.staticProcedures do
    -- `mapProcedureM` (not body-only `mapProcedureBodiesM`): a poly-proc call can appear in a
    -- precondition/decreases/invokeOn too, and the final rewrite renames such calls to their
    -- monomorph — so they must be seeded for cloning here, else that rename dangles.
    let (_, pi') := (mapProcedureM (m := StateM (Std.HashMap String ProcInst))
      (fun root => mapStmtExprM
        (fun e => do
          match e.val with
          | .StaticCall callee args =>
            match polyProcDefs.get? callee.text with
            | some pproc =>
              match inferProcInst pproc (args.map (computeExprType model)) with
              | some pinst => modify (·.insert (procInstKey pinst) pinst)
              | none => pure ()
            | none => pure ()
          | _ => pure ()
          pure e) root) proc).run procInsts
    procInsts := pi'
  return (insts, procInsts)

/-- The monomorphization transform over a whole program. Returns the rewritten
    program plus any diagnostics (e.g. a divergent recursive generic that exceeds
    the instantiation-depth bound). -/
def monomorphizeComposites (program : Program) (model : SemanticModel)
    : Program × List DiagnosticModel := Id.run do
  -- 1. Index the generic composites + the poly procs that materialize them.
  let (genComposites, genDefs, polyProcDefs) := indexGenerics program model
  if genComposites.isEmpty then return (program, [])

  -- 2. Collect the seed composite + procedure instantiations from every type position.
  let (insts, procInsts) := collectSeeds program model genComposites polyProcDefs

  -- 3. UNIFIED FIXPOINT — emit monomorph composites AND clone poly
  -- procedures from ONE fueled, depth-capped worklist over `Sum Inst ProcInst`. The two
  -- kinds interleave and feed each other:
  --   • a COMPOSITE item (`.inl`) emits the monomorph and enqueues instantiations in its
  --     substituted fields (`Box<int>` reachable only through `Pair<int>{b:Box<T>}`);
  --   • a PROCEDURE item (`.inr`) clones the poly proc and enqueues composite insts from its
  --     signature AND body, plus proc insts from poly calls in the body (the proc→proc edge),
  --     discovered against the PRISTINE body (the clone's cleared ids aren't in `model`).
  -- TERMINATION: a divergent recursive generic grows type-arg DEPTH; `maxInstDepth` refuses
  -- to enqueue past the cap, recording ONE `NotYetImplemented` per base so divergence fails
  -- LOUD (and gates translation, suppressing downstream Core noise).
  -- The bound (8) is a pragmatic ceiling: realistic generic nesting (e.g. `Pair<Box<int>, …>`)
  -- is only a few levels deep, while a divergent `L<L<T>>` blows past it within a handful of
  -- iterations — so 8 rejects divergence promptly without over-rejecting hand-written code. A
  -- legitimate program that genuinely needs depth > 8 would be rejected (a known limitation);
  -- raise the cap if one ever appears.
  let maxInstDepth : Nat := 8
  let mut witnessComposites : List TypeDefinition := []  -- fresh opaque sorts for uncalled procs
  -- Worklist state (emitted monomorphs/clones, dedup sets, diags, pending items). Seed:
  -- composites from all collected type positions (.inl) + procs from call sites (.inr).
  let mut st : MonoState := {
    monoComposites := [], procClones := [], emitted := {}, clonedProcs := {},
    clonedBases := {}, diags := [], rejectedBases := {},
    worklist := (insts.toList.map (fun kv => Sum.inl kv.2)) ++ (procInsts.toList.map (fun kv => Sum.inr kv.2)) }
  -- Drain to a fixpoint (see `drainWorklist`).
  let fuel : Nat := 1024
  st := drainWorklist genComposites genDefs polyProcDefs model maxInstDepth fuel st

  -- 3b. (gap: uncalled monomorphized poly procs) An indexed poly proc absent from
  -- `clonedBases` is genuinely UNCALLED (the proc→proc edge cloned every reachable proc,
  -- so `clonedBases` is the exact called-set). It would be dropped at emission with its
  -- contract UNCHECKED. (A value-`T` poly proc — one touching no generic composite — is
  -- instead KEPT verbatim and lowered to a polymorphic Core procedure; its contract is
  -- checked when CALLED via CallElim freshening, AND even uncalled its own body VC is emitted
  -- and discharged — a false postcondition there fails loud — so it is never silently
  -- unchecked, by a different path than this witness.) To close the gap HERE, synthesize a
  -- WITNESS: bind each type var to a FRESH OPAQUE composite (`$Witness$<proc>$<i>`) — an
  -- uninterpreted sort of arbitrary cardinality, NOT a singleton, so a false-in-general
  -- contract (`a#val == b#val`) still fails; distinct type vars get distinct witnesses. Then
  -- drain the worklist again.
  for (pname, pproc) in polyProcDefs.toList do
    unless st.clonedBases.contains pname do
      let witnessArgs : List HighType := (List.range pproc.typeArgs.length).map (fun i =>
        HighType.UserDefined (mkId s!"$Witness${pname}${i}"))
      for wty in witnessArgs do
        match wty with
        | .UserDefined wn => witnessComposites := witnessComposites ++ [.Composite {
            name := wn, typeArgs := [], extending := [], fields := [], instanceProcedures := [] }]
        | _ => pure ()
      st := { st with worklist := st.worklist ++ [.inr (pname, witnessArgs)] }
  -- Second drain: same per-item processing, now over the witness proc instantiations (and
  -- the composite instantiations they spawn). Witness args are concrete `.UserDefined`, so
  -- they monomorphize like any other concrete type.
  st := drainWorklist genComposites genDefs polyProcDefs model maxInstDepth fuel st

  -- Unpack the worklist state into local accumulators for the assembly below.
  let mut monoComposites : List TypeDefinition := st.monoComposites
  let procClones : List Procedure := st.procClones
  let mut diags : List DiagnosticModel := st.diags

  -- FUEL-EXHAUSTION GUARD (fail loud, never silently truncate). The `fuel` backstop
  -- (1024 per drain) is coarser than the `maxInstDepth` depth cap, which is the real
  -- divergence guard: divergent recursion grows DEPTH and is rejected by `tooDeep` long
  -- before fuel matters. But a pathological program with >1024 DISTINCT bounded-depth
  -- instantiations could drain fuel with the worklist still non-empty — leaving a
  -- HALF-monomorphized program. Without this guard the loops would just stop and emit it
  -- silently (relying on Core to later choke on a dangling monomorph ref). Emit a clear
  -- diagnostic instead, so a fuel wall fails loud at the pass, like the depth cap does.
  unless st.worklist.isEmpty do
    diags := diags ++ [diagnosticFromSource none
      s!"monomorphization did not converge within {1024} instantiation steps (worklist still has {st.worklist.length} items): too many distinct generic instantiations. This is a tool limit, not a program error — report it if the program is reasonable."
      DiagnosticType.NotYetImplemented]

  -- 3c. (Ordering is now done over the WHOLE type list at assembly — see step 4.)

  -- 4. Rewrite all type positions + drop generic composites.
  let types' : List TypeDefinition := program.types.filterMap fun td =>
    match td with
    | .Composite ct => if !ct.typeArgs.isEmpty then none
        else some (.Composite { ct with
          fields := ct.fields.map (fun f => { f with type := rewriteTy genComposites f.type }),
          -- rewrite the `extending` list too, so a non-generic composite that extends a
          -- generic instantiation (`IntBox extends Box<int>`) points at the monomorph
          -- (`Box$a1$int`) rather than the dropped generic head (`Box`). Seeded in
          -- `collectSeeds` so that monomorph is emitted.
          extending := ct.extending.map (rewriteTy genComposites) })
    | .Datatype dt => some (.Datatype { dt with constructors := dt.constructors.map (fun ctor =>
        { ctor with args := ctor.args.map (fun p => { p with type := rewriteTy genComposites p.type }) }) })
    | other => some other
  -- Static procedures: DROP the indexed poly procedures (replaced by their clones,
  -- like generic composites are dropped), keep+rewrite the rest, append the clones
  -- (also rewritten for any generic composites in their now-concrete signatures).
  let rwProcSig (proc : Procedure) : Procedure :=
    { proc with
      inputs := proc.inputs.map (fun p => { p with type := rewriteTy genComposites p.type }),
      outputs := proc.outputs.map (fun p => { p with type := rewriteTy genComposites p.type }) }
  let keptProcs := program.staticProcedures.filter (fun p => !polyProcDefs.contains p.name.text)
  let staticProcs' := (keptProcs ++ procClones).map rwProcSig
  let constants' := program.constants.map (fun c => { c with type := rewriteTy genComposites c.type })
  let staticFields' := program.staticFields.map (fun f => { f with type := rewriteTy genComposites f.type })
  -- Ordering: re-resolution builds each composite's field-inheritance typeScope in type-LIST
  -- order (`resolveTypeDefinition`), reading its parent's already-built scope — so every
  -- composite must come AFTER its parents, or an inherited field resolves to nothing
  -- ("'tag' is not defined" → un-lowered access → StrataBug). Topo-sort the WHOLE composite
  -- list (concrete `types'` + `monoComposites`) together, not just the monomorphs: a
  -- monomorph child extends a concrete parent (`Box$a1$int extends Base`), AND — since a
  -- non-generic composite may extend a generic INSTANTIATION (`IntBox extends Box<int>`,
  -- rewritten to `Box$a1$int`) — a CONCRETE child may extend a MONOMORPH parent. Sorting
  -- only the monomorphs (the old approach) handled the first but not the second. `topoSort­
  -- Monomorphs` is a general stable DFS post-order: it passes non-composites through and
  -- places every composite after its named parents at every hop. Witnesses are
  -- zero-field/no-extends → position-independent, appended after.
  let program := { program with
                     types := topoSortMonomorphs (types' ++ monoComposites) ++ witnessComposites,
                     staticProcedures := staticProcs',
                     constants := constants', staticFields := staticFields' }
  -- 5. Rewrite statement-level types + new sites (`rewriteStmt`), AND rewrite
  -- StaticCall callees that target a monomorphized poly procedure to the monomorph
  -- name matching that call's inferred instantiation.
  let rewriteCall (e : StmtExprMd) : StmtExprMd :=
    match e.val with
    | .StaticCall callee args =>
      match polyProcDefs.get? callee.text with
      | some pproc =>
        match inferProcInst pproc (args.map (computeExprType model)) with
        | some pinst => { e with val := .StaticCall (mkId (procInstKey pinst)) args }
        | none => e
      | none => e
    | _ => e
  let stmtRewrite (e : StmtExprMd) : StmtExprMd := rewriteCall (rewriteStmt genComposites e)
  -- Rewrite via `mapProcedureM` (not `mapProgram`/`mapProcedureBodiesM`) so the rewrite
  -- reaches preconditions/decreases/invokeOn too — a generic in a contract (e.g. a
  -- quantifier binder type in a precondition) would otherwise survive un-lowered to Core.
  let program' := { program with
    staticProcedures := program.staticProcedures.map
      (fun proc => mapProcedureM (m := Id) (fun root => mapStmtExpr stmtRewrite root) proc) }
  return (program', diags)

/-- Pipeline pass: monomorphize generic composites. -/
def monomorphizeCompositesPass : LoweringPass where
  name := "MonomorphizeComposites"
  needsResolves := true
  documentation := "Lowers generic composites (`composite Box<T>`) by emitting one concrete composite per used instantiation and rewriting `Box<int>` type references and `new Box` allocations to the monomorphic name. Runs before heap parameterization."
  run := fun _ p m => let (p', diags) := monomorphizeComposites p m; (p', diags, {})

end -- public section
end Strata.Laurel
