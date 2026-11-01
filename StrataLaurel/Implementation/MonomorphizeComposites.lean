/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.LaurelTypes
import Strata.Util.Tactics

/-!
# Monomorphize generic composites

Lowers user-level generic composites (`composite Box<T> { val: T }`) by emitting
one concrete composite per *used* instantiation (`Box<int>` → `Box$a1$int` with
`val: int`) and rewriting every `Box<int>` type reference — and the matching
`new Box` allocation — to the monomorphic name. After this pass no
`HighType.Applied` (over a generic composite) and no generic composite definition
remain, so all downstream passes (HeapParameterization, translation) see only
monomorphic composites. A generic composite leaves a field-free family parent
(`genericFamilyPrefix`), which its instantiations extend.

Runs after resolution, before `HeapParameterization`. `needsResolves := true`
re-resolves the injected concrete composites.

Instantiations are collected from every type position the shared type walks visit, `new C<τ>`
allocation sites included, then driven to a fixpoint by a depth-capped worklist that also clones
poly procedures materializing a generic composite.
The pipeline reads, top to bottom: `indexGenerics` and `indexOpenCallers` → `collectSeeds`, call
settling (`settleCallNode`) and renaming (`rewritePolyCallNode`) → fixpoint drain
(`processWorklistItem`) → uncalled-proc witnesses → rewrite all type positions.
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
private def tyTag (ty : HighType) : Option String :=
  -- The extra leaf beyond `instTagCommon`'s shared arms: monomorphization accepts `void`.
  -- All shared arms (incl. TMap/TSet) come from `instTagCommon`; `none` on TVar.
  instTagCommon (fun | .TVoid => some "void" | _ => none) ty

/-- Max nesting depth of a `HighType` (a flat type is depth 1; `Box<int>` is 2;
    `Box<Box<int>>` is 3). Used to detect a DIVERGENT recursive generic
    (`L<T>{ next: L<L<T>> }`), whose instantiations grow in depth without bound —
    so we cut them off with a real diagnostic at a shallow depth rather than
    grinding to a name-length limit while emitting dozens of dead monomorphs. -/
private def tyDepth : HighType → Nat
  | .Applied b as => 1 + max (tyDepth b.val) ((as.attach.map (fun ⟨a, _⟩ => tyDepth a.val)).foldl Nat.max 0)
  | .TSet vt => 1 + tyDepth vt.val
  | .TMap kt vt => 1 + max (tyDepth kt.val) (tyDepth vt.val)
  | .Intersection ts => 1 + (ts.attach.map (fun ⟨t, _⟩ => tyDepth t.val)).foldl Nat.max 0
  | _ => 1
  termination_by ty => ty
  decreasing_by ast_recursion_decreasing

/-- Mangled monomorphic name for `C` instantiated at `args`, e.g. `Box$a1$int`,
    or `none` if any arg can't be tagged. Identifier-legal only
    (these become Core/SMT sort names — no `«»`/`,`). -/
private def monoName? (base : String) (args : List HighType) : Option String := do
  let tags ← args.mapM tyTag
  some s!"{base}$a{tags.length}${String.intercalate "$" tags}"

/-- Total version for call sites that have already validated the args (or for
    diagnostics). Falls back to a clearly-bogus name on un-taggable input so a
    missing validation surfaces downstream rather than silently colliding. -/
private def monoName (base : String) (args : List HighType) : String :=
  (monoName? base args).getD s!"{base}$UNTAGGABLE"

private def clearId (i : Identifier) : Identifier := { i with uniqueId := none }

private def clearParamId (p : Parameter) : Parameter := { p with name := clearId p.name }

/-- `ty` at the type arguments `subst`, its `uniqueId`s cleared so re-resolution assigns fresh
    ones: a monomorph's or a clone's types were resolved against the *generic* definition (with
    `.TVar` carrying ids). -/
private def instantiateTy (subst : Std.HashMap String HighTypeMd) (ty : HighTypeMd) : HighTypeMd :=
  mapHighTypeNames (fun ctor n => ctor (clearId n)) (substTypeVars subst ty)

/-- The instantiation key: `(generic composite name, concrete arg types)`. -/
private abbrev Inst := String × List HighType

private def instKey (i : Inst) : String := monoName i.1 i.2

/-- A procedure instantiation: `(procName, typeArgs-in-declaration-order)`. Named
    with the same `monoName` scheme as composites, so a poly procedure `f<T>`
    called at `int` becomes the monomorphic proc `f$a1$int`. -/
private abbrev ProcInst := String × List HighType

private def procInstKey (p : ProcInst) : String := monoName p.1 p.2

/-- The types a shared type walk visits: `typesIn (mapProcedureHighTypesM · proc)` lists every type
    in `proc`. -/
private def typesIn (walk : (HighTypeMd → StateM (Array HighTypeMd) HighTypeMd) →
    StateM (Array HighTypeMd) α) : List HighTypeMd :=
  ((walk fun ty => do modify (·.push ty); pure ty).run #[]).2.toList

/-- Collect all `.Applied (UserDefined C) args` instantiations appearing in a
    `HighType`, where `C` is a generic composite in `genComposites`. -/
private def collectInTy (genComposites : Std.HashMap String (List Identifier))
    (ty : HighTypeMd) : List Inst :=
  let here : List Inst := match ty.val with
    | .Applied base args =>
      match base.val with
      | .UserDefined n =>
        let argVals := args.map (·.val)
        -- Only record instantiations whose args are all `tyTag`-taggable. An un-taggable
        -- arg (`.TVar`; Map/Set ARE taggable) leaves the type `.Applied`,
        -- failing LOUD at re-resolution — never silently coalesced into a shared mono name.
        if genComposites.contains n.text && (monoName? n.text argVals).isSome
        then [(n.text, argVals)] else []
      | _ => []
    | _ => []
  let nested : List Inst := match _h : ty.val with
    | .Applied base args =>
      collectInTy genComposites base ++ args.attach.flatMap (fun ⟨a, _⟩ => collectInTy genComposites a)
    | .TSet vt => collectInTy genComposites vt
    | .TMap kt vt => collectInTy genComposites kt ++ collectInTy genComposites vt
    | .Intersection ts => ts.attach.flatMap (fun ⟨t, _⟩ => collectInTy genComposites t)
    | _ => []
  here ++ nested
  termination_by ty
  decreasing_by ast_recursion_decreasing

/-- Does `ty` mention a generic composite instantiated at a type variable in `tvSet` —
    an `.Applied (UserDefined C) args` (`C` a generic composite) some of whose args is a
    `.TVar tv`, `tv ∈ tvSet`, searched recursively. The caller `mentionsGenericComposite`
    uses it to decide the proc must be monomorphized rather than freshened: a generic
    composite has no uniform Core representation the freshening path can use. -/
private def tyHasGenCompAtTVar (genComposites : Std.HashMap String (List Identifier))
    (tvSet : Std.HashSet String) (ty : HighType) : Bool :=
  anyHighType (fun
    | .Applied ⟨.UserDefined n, _⟩ args =>
      genComposites.contains n.text
        && args.any fun a => match a.val with | .TVar tv => tvSet.contains tv.text | _ => false
    | _ => false) ty

/-- Rewrite a generic-composite instantiation in a `HighType` to its monomorph name
    (see the taggability caveat inline below). -/
private def rewriteTy (genComposites : Std.HashMap String (List Identifier))
    (ty : HighTypeMd) : HighTypeMd :=
  let v := match _h : ty.val with
    | .Applied base args =>
      match base.val with
      | .UserDefined n =>
        -- Only rewrite taggable instantiations (those collection emitted a
        -- composite for). Un-taggable ones stay `.Applied` → loud resolution
        -- failure, not a dangling `UNTAGGABLE` reference.
        match (if genComposites.contains n.text then monoName? n.text (args.map (·.val)) else none) with
        | some mn => .UserDefined (mkId mn)
        | none => .Applied (rewriteTy genComposites base) (args.attach.map (fun ⟨a, _⟩ => rewriteTy genComposites a))
      | _ => .Applied (rewriteTy genComposites base) (args.attach.map (fun ⟨a, _⟩ => rewriteTy genComposites a))
    | .TSet et => .TSet (rewriteTy genComposites et)
    | .TMap kt vt => .TMap (rewriteTy genComposites kt) (rewriteTy genComposites vt)
    | .Intersection ts => .Intersection (ts.attach.map (fun ⟨t, _⟩ => rewriteTy genComposites t))
    | other => other
  { val := v, source := ty.source }
  termination_by ty
  decreasing_by ast_recursion_decreasing

/-! ### Procedure monomorphization — clone a poly proc at a concrete inst -/

/-- Clear the uniqueIds of the binders and references in ONE node of a clone; `cloneProcAt` clears
    those of its types, a `new`'s class included. Re-resolution keeps an existing uniqueId, so two
    clones that kept the original ids would cross-link: `unbox$a1$int`'s `r` would merge with
    `unbox$a1$bool`'s, "Impossible to unify bool with int". -/
private def clearIdsInStmtNode (e : StmtExprMd) : StmtExprMd :=
  let clrDeclParam (p : Parameter?) : Parameter? := { p with name := clearId p.name }
  let clrVarTarget (v : VariableMd) : VariableMd :=
    match v.val with
    | .Declare param => { v with val := .Declare (clrDeclParam param) }
    | .Local n => { v with val := .Local (clearId n) }
    | .Field tgt fn => { v with val := .Field tgt (clearId fn) }
  let val' := match e.val with
    | .Var (.Local n) => .Var (.Local (clearId n))
    | .Var (.Field tgt fn) => .Var (.Field tgt (clearId fn))
    | .Var (.Declare param) => .Var (.Declare (clrDeclParam param))
    | .StaticCall callee args tyArgs => .StaticCall (clearId callee) args tyArgs
    | .Assign targets value => .Assign (targets.map clrVarTarget) value
    -- `IncrDecr`/`CompoundAssign` carry a `Variable` target too; clear its id like `.Assign`
    -- so a per-instantiation `.Field` target does not cross-link clones (it survives to clone
    -- time — mono runs before EliminateIncrDecrAndCompoundAssign).
    | .IncrDecr mode op target => .IncrDecr mode op (clrVarTarget target)
    | .CompoundAssign op target rhs => .CompoundAssign op (clrVarTarget target) rhs
    -- `PureFieldUpdate`'s `fieldName` resolves per-instantiation, so its id must be cleared
    -- too (target/newValue sub-expressions are handled by the `mapStmtExpr` recursion).
    | .PureFieldUpdate target fn newValue => .PureFieldUpdate target (clearId fn) newValue
    | .Quantifier mode param trigger body => .Quantifier mode (clearParamId param) trigger body
    | other => other
  { e with val := val' }

/-- Clone a polymorphic `Procedure` at a concrete type-arg substitution: substitute through
    every type position; rename to `newName`; set `typeArgs := []` (now monomorphic). The ids of
    its types, parameters, channel bindings, `throws` binding and nodes (`clearIdsInStmtNode`) are
    cleared, so that it re-resolves apart from the other clones. -/
private def cloneProcAt (proc : Procedure) (subst : Std.HashMap String HighTypeMd)
    (newName : String) : Procedure :=
  let proc := mapProcedureHighTypesM (m := Id) (instantiateTy subst) proc
  let proc := mapProcedureM (m := Id) (mapStmtExpr clearIdsInStmtNode) proc
  { proc with
    name := mkId newName,
    typeArgs := [],
    inputs := proc.inputs.map clearParamId,
    outputs := proc.outputs.map clearParamId,
    contracts := proc.contracts.withClauses
      (yields := proc.yields.map clearParamId) (resumes := proc.resumes.map clearParamId),
    throwsBinding := proc.throwsBinding.map clearId }

/-- The two instantiations at which `actual` reaches a declared parameter's head
    (`ancestorLiftCandidates`), if they differ up to `highEq`: a `D<int>` extending both
    `Base<bool>` and `Base<int>` gives an inherited method of `Base` no single type argument.

    `none` while `actual` mentions a type variable (`D<S>` in a pristine generic body): an ancestor
    may carry it (`Base<S>`), so no conflict is real yet, and the clone that makes `actual` concrete
    decides the same call again. Deferring on `actual` rather than on the ancestors found keeps a
    concrete conflict listed before an abstract parent from being reported twice.

    `none`, too, for a `declared` that mentions no type variable (`GBaseG<bool>`): it fixes no
    type argument, so the diamond is passed by an upcast. -/
private def diamondConflict? (ctx : TypeLattice) (declared actual : HighType)
    : Option (String × HighType × HighType) := do
  let head ← highBaseName? declared
  guard (tyTag actual).isSome
  guard !(tvarIdents declared).isEmpty
  let hit :: rest := ancestorLiftCandidates ctx declared actual | none
  let other ← rest.find? (fun a => !highEq a hit)
  return (head.text, hit.val, other.val)

/-- The type of call argument `a`, located at `a`, as `Resolution` typed it. A field is typed at
    its holder's instantiation (`h#d` with `h: H<int>` and `d: DG<X>` is a `DG<int>`): typed as
    declared, the receiver would look abstract and the diamond check would skip it. -/
private def argType (ctx : TypeLattice) (model : SemanticModel) (a : StmtExprMd) : HighTypeMd :=
  let fieldTypeAt := fun fieldName holderTy => match model.get fieldName with
    | .field declType fld => ctx.fieldTypeAt declType fld.type holderTy
    | _ => none
  { computeExprTypeWith (some fieldTypeAt) model a with source := a.source }

/-- Report a call one of whose arguments is a diamond for its parameter (`diamondConflict?`), since
    `Resolution` records such a call at whatever the expected type supplies. Both sides are
    `unfold`ed, as `Resolution` matches them, so a constrained type over the diamond is refused too.

    In a clone, then rebind the record to what the arguments bind under `subst`, the record
    supplying the rest, as `Resolution` lets an argument's binding win over the expected type. A
    record made in a generic body need not suit a clone: an argument typed at the body's own type
    variable binds nothing there, so the expected type decided it. Outside a clone the record
    stands. A binding that mentions a type variable is dropped, and an argument type that mentions
    one other than `binders`, as a catch binding's thrower's, is not substituted: `subst` replaces
    by name, and that variable may be spelled like one of `binders`.

    Run before any call is renamed, so that `model` types a nested call by its record, as settled
    already, and never over a clone's body, whose ids are cleared. -/
private def settleCallNode (model : SemanticModel) (ctx : TypeLattice)
    (polyProcDefs : Std.HashMap String Procedure) (binders : List Identifier)
    (subst : Std.HashMap String HighTypeMd) (e : StmtExprMd) : StateM (List Message) StmtExprMd := do
  let .StaticCall callee args tyArgs := e.val | return e
  let some calleeDef := polyProcDefs.get? callee.text | return e
  let params := calleeDef.inputs.map (·.type)
  let argTys := args.map fun a =>
    let t := argType ctx model a
    if (tvarIdents t.val).all fun v => binders.any (·.uniqueId == v.uniqueId) then
      substTypeVars subst t
    else t
  let conflict? := (params.zip argTys).findSome? fun (param, aty) =>
    (diamondConflict? ctx (ctx.unfold param).val (ctx.unfold aty).val).map (aty, ·)
  if let some (aty, headName, t1, t2) := conflict? then
    -- `formatHighTypeVal` is the SAME renderer the grammar back-translation uses, so the
    -- upcast hint (`var b: <t1> := …`) is real surface syntax rather than a hand-rolled
    -- approximation that could print an uncompilable `_` on a shape it didn't special-case.
    let fmt := fun (t : HighType) => toString (formatHighTypeVal t)
    modify (· ++ [diagnosticFromSource aty.source
      s!"ambiguous type argument for inherited method: '{fmt aty.val}' reaches \
         '{headName}' at both '{fmt t1}' and '{fmt t2}', so the type \
         argument cannot be determined. Upcast the receiver to the intended one \
         (e.g. `var b: {fmt t1} := …`) to disambiguate."
      MessageKind.userError])
  if binders.isEmpty then return e
  let argSubst := (callSiteTypeSubst ctx (fun _ => false) params argTys).1
  let settled := (calleeDef.typeArgs.zip tyArgs).map fun (tv, t) => argSubst.getD tv.text t
  return { e with val := .StaticCall callee args settled }

/-- Threaded through a poly-call rewrite traversal. -/
private structure RewriteState where
  /-- The instantiation of every call this traversal renamed. -/
  renamed  : List ProcInst := []
  /-- Whether a call was left unrenamed, its instantiation missing or not concrete. -/
  leftOpen : Bool := false

/-- Rewrite ONE node: a `StaticCall` to an indexed poly procedure becomes a call to the monomorph at
    the instantiation `Resolution` recorded on it, as `settleCallNode` left it, so that the clone
    re-resolves as the call did, and the instantiation is kept in `renamed`. `subst` makes an
    enclosing clone's abstract type arguments concrete (`T` inside `outer<T>` cloned at int becomes
    `int`); it is empty outside a clone body.

    A call whose instantiation is missing or not concrete is LEFT unchanged and NOT discovered:
    inside a generic body the clone discovers it once `subst` is concrete, and anywhere else it
    fails loud downstream (dangling poly callee at re-resolution) rather than silently
    mis-monomorphizing. -/
private def rewritePolyCallNode (polyProcDefs : Std.HashMap String Procedure)
    (subst : Std.HashMap String HighTypeMd) (e : StmtExprMd) : StateM RewriteState StmtExprMd := do
  let .StaticCall callee args tyArgs := e.val | return e
  let some calleeDef := polyProcDefs.get? callee.text | return e
  let targs := tyArgs.map (substTypeVars subst · |>.val)
  unless targs.length == calleeDef.typeArgs.length && targs.all (tyTag · |>.isSome) do
    modify fun st => { st with leftOpen := true }
    return e
  let pinst := (calleeDef.name.text, targs)
  modify fun st => { st with renamed := st.renamed ++ [pinst] }
  -- `procInstKey` bakes the instantiation into the name, so the type arguments are dropped.
  return { e with val := .StaticCall (mkId (procInstKey pinst)) args [] }

/-- Discover and rewrite polymorphic-procedure CALLS inside a (pristine, resolved)
    procedure's StmtExpr slots — preconditions, decreases, invokeOn, and body — under
    a concrete `subst`. This is the procedure→procedure edge of the fixpoint (step 3):
    a cloned `outer<T>`'s body may call another poly proc `inner<T>(b: Box<T>)`.

    Argument types are computed against the PRISTINE body, which is why this must run before
    cloning: a clone's ids are cleared and absent from `model`. Returns the rewritten procedure,
    the instantiations for the worklist and the diamond diagnostics. -/
private def discoverRewritePolyCalls (model : SemanticModel)
    (ctx : TypeLattice)
    (polyProcDefs : Std.HashMap String Procedure)
    (subst : Std.HashMap String HighTypeMd) (pproc : Procedure)
    : Procedure × List ProcInst × List Message :=
  let (settled, diags) :=
    (mapProcedureM (mapStmtExprM (settleCallNode model ctx polyProcDefs pproc.typeArgs subst))
      pproc).run []
  let (pproc', st) :=
    (mapProcedureM (mapStmtExprM (rewritePolyCallNode polyProcDefs subst)) settled).run {}
  (pproc', st.renamed, diags)

/-- Mutable state threaded through the monomorphization worklist drain: the emitted
    monomorphs/clones, the dedup sets, accumulated diagnostics, and the pending worklist. -/
private structure MonoState where
  monoComposites : List TypeDefinition
  procClones     : List Procedure
  emitted        : Std.HashSet String
  clonedProcs    : Std.HashSet String
  clonedBases    : Std.HashSet String     -- base proc NAMES (not instKeys) that produced ≥1 clone
  diags          : List Message
  rejectedBases  : Std.HashSet String     -- bases already diagnosed (dedup, so each errors once)
  worklist       : List (Sum Inst ProcInst)

/-- Process ONE worklist item (a composite instantiation `.inl` or a procedure
    instantiation `.inr`): if its type-arg depth exceeds `maxInstDepth` reject it loud
    (once per base); otherwise emit the monomorph / clone and enqueue any new
    instantiations its substituted types reach. Shared by both
    worklist drains (the main drain and the post-witness drain), which differ only in
    what they seed. Returns the updated state. -/
private def processWorklistItem (genComposites : Std.HashMap String (List Identifier))
    (genDefs : Std.HashMap String CompositeType) (ctx : TypeLattice) (polyProcDefs : Std.HashMap String Procedure)
    (model : SemanticModel) (maxInstDepth : Nat) (item : Sum Inst ProcInst) (s : MonoState)
    : MonoState := Id.run do
  let tooDeep (args : List HighType) : Bool := (args.map tyDepth).foldl Nat.max 0 > maxInstDepth
  let rejectDiag (base kind : String) : Message :=
    diagnosticFromSource .unknown
      s!"recursive generic {kind} '{base}' is not supported: its instantiations grow without bound (depth exceeds {maxInstDepth})"
      MessageKind.notYetImplemented
  -- Enqueue the not-yet-emitted composite instantiations that `tys` name.
  let enqueue (tys : List HighTypeMd) (s : MonoState) : MonoState :=
    (tys.flatMap (collectInTy genComposites)).foldl (init := s) fun s inst =>
      if s.emitted.contains (instKey inst) then s
      else { s with worklist := s.worklist ++ [.inl inst] }
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
          (ct.typeArgs.zip args).foldl (fun m (tv, a) => m.insert tv.text ⟨a, .unknown⟩) {}
        -- Every instantiation also extends its family parent (`genericFamilyPrefix`).
        let family : HighTypeMd := ⟨.UserDefined (mkId (genericFamilyPrefix ++ cname)), .unknown⟩
        -- The generic definition at `args`, its field ids cleared so that it re-resolves apart from
        -- its siblings. Its field initializers are dropped: they never reach Core, and a call in
        -- one would still name a procedure replaced by its clones. Its types are rewritten with the
        -- rest of the program.
        let mono : TypeDefinition :=
          mapTypeDefinitionHighTypesM (m := Id) (instantiateTy subst)
          (.Composite { ct with
            name := mkId (monoName cname args), typeArgs := [], instanceProcedures := []
            extending := ct.extending ++ [family]
            fields := ct.fields.map fun f =>
              { f with name := clearId f.name, initializer := none } })
        -- Feedback edge: the substituted field and parent types are where new composite
        -- instantiations hide (depth checked on dequeue).
        s := enqueue (typesIn (mapTypeDefinitionHighTypesM · mono)) s
        s := { s with monoComposites := s.monoComposites ++ [mono] }
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
          (pproc.typeArgs.zip targs).foldl (fun m (tv, a) => m.insert tv.text ⟨a, .unknown⟩) {}
        -- proc→proc edge: discover+rewrite poly calls in the PRISTINE body (model intact),
        -- enqueueing each callee instantiation; then clone the rewritten proc.
        let (pproc', discovered, ambigDiags) := discoverRewritePolyCalls model ctx polyProcDefs subst pproc
        let clone := cloneProcAt pproc' subst (monoName pname targs)
        -- A diamond that does not depend on `subst` was reported by the seeding check already, or
        -- by an earlier clone's.
        s := { s with procClones := s.procClones ++ [clone],
                      diags := s.diags ++ ambigDiags.filter (!s.diags.contains ·) }
        for di in discovered do
          unless s.clonedProcs.contains (procInstKey di) do
            s := { s with worklist := s.worklist ++ [.inr di] }
        -- composite instantiations from every type position of the clone.
        s := enqueue (typesIn (mapProcedureHighTypesM · clone)) s
      | none => pure ()
  return s

/-- Drain the worklist to a fixpoint, processing one item per step via
    `processWorklistItem`, up to `fuel` steps. `fuel` is a coarse backstop; the real
    divergence guard is `maxInstDepth` (checked inside the helper). Returns the final
    state — a non-empty `worklist` means fuel ran out (the caller fails loud). Both
    drains in `monomorphizeComposites` (the main drain and the post-witness drain) go
    through this, so they can't drift. -/
private def drainWorklist (genComposites : Std.HashMap String (List Identifier))
    (genDefs : Std.HashMap String CompositeType) (ctx : TypeLattice) (polyProcDefs : Std.HashMap String Procedure)
    (model : SemanticModel) (maxInstDepth : Nat) : Nat → MonoState → MonoState
  | 0, s => s
  | fuel+1, s =>
    match s.worklist with
    | [] => s
    | item :: rest =>
      drainWorklist genComposites genDefs ctx polyProcDefs model maxInstDepth fuel
        (processWorklistItem genComposites genDefs ctx polyProcDefs model maxInstDepth item { s with worklist := rest })

/-- Index the program's generic entities: the generic composites (name → type params,
    name → definition), and the poly procedures that MATERIALIZE a generic composite at
    one of their own type vars — in the SIGNATURE (`f<T>(b: Box<T>)`) OR the BODY
    (`var t: Box<T>`). Those monomorphize per call site; a poly proc touching no generic
    composite at its typevar (`idp<T>(x:T)`) stays on the CallElim freshening path (the
    hybrid), unless it calls one that does at its typevar (`indexOpenCallers`). The body case
    matters: a body-local `Box<T>` on the freshening path has no Core representation, so its
    field write would survive un-lowered (a StrataBug). -/
private def indexGenerics (program : LaurelProgram)
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
    (typesIn (mapProcedureHighTypesM · p)).any (tyHasGenCompAtTVar genComposites tvSet ·.val)
  let mut polyProcDefs : Std.HashMap String Procedure := {}
  for proc in program.staticProcedures do
    if !proc.typeArgs.isEmpty && mentionsGenericComposite proc then
      polyProcDefs := polyProcDefs.insert proc.name.text proc
  return (genComposites, genDefs, polyProcDefs)

/-- Add to `polyProcDefs`, to a fixpoint, every poly proc that leaves a call to one of them
    unrenamed, as one at an instantiation its own type variables leave open (`f<S>(x: S)` calling
    `id2(x)`, `id2` materializing a `Box<T>`). Such a call is renamed only in a clone of its caller,
    where `S` is concrete, so the caller must be monomorphized too: on the freshening path it is
    kept verbatim while its callee is replaced by clones, and the call dangles. A call without a
    record dangles either way. -/
private def indexOpenCallers (program : LaurelProgram)
    (polyProcDefs : Std.HashMap String Procedure) : Std.HashMap String Procedure := Id.run do
  let leavesOpen (defs : Std.HashMap String Procedure) (proc : Procedure) : Bool :=
    ((mapProcedureM (mapStmtExprM (rewritePolyCallNode defs {})) proc).run {}).2.leftOpen
  let mut defs := polyProcDefs
  -- Each round but the last indexes another procedure, so there are at most as many as procedures.
  for _ in program.staticProcedures do
    let callers := program.staticProcedures.filter fun proc =>
      !proc.typeArgs.isEmpty && !defs.contains proc.name.text && leavesOpen defs proc
    if callers.isEmpty then break
    defs := callers.foldl (fun m proc => m.insert proc.name.text proc) defs
  return defs

/-- Collect the SEED instantiations to start the worklist from: every composite instantiation
    in any type position of the program, through the walk the final rewrite uses, so that every
    type it renames has a monomorph. -/
private def collectSeeds (program : LaurelProgram)
    (genComposites : Std.HashMap String (List Identifier)) : Std.HashMap String Inst :=
  ((typesIn (mapLaurelProgramHighTypesM · program)).flatMap (collectInTy genComposites)).foldl
    (fun m i => m.insert (instKey i) i) {}

/-- The monomorphization transform over a whole program. Returns the rewritten
    program plus any diagnostics (e.g. a divergent recursive generic that exceeds
    the instantiation-depth bound). -/
def monomorphizeComposites (program : LaurelProgram) (model : SemanticModel)
    : LaurelProgram × List Message := Id.run do
  -- 1. Index the generic composites + the poly procs that materialize them.
  let (genComposites, genDefs, polyProcDefs) := indexGenerics program
  if genComposites.isEmpty then return (program, [])
  -- 1b. Index, too, the poly procs that call an indexed one at their own type variables.
  let polyProcDefs := indexOpenCallers program polyProcDefs

  -- The type lattice over the whole program, for settling calls and typing fields. Built once
  -- here (from `program.types`) and threaded through, so the ancestor walk sees the FULL `extends`
  -- chain (concrete hops included) rather than only the generic composites `genDefs` records.
  let ctx := TypeLattice.ofTypes program.types

  -- 2. Seed the composite instantiations from every type position, and the procedure ones by
  -- renaming every call to an indexed poly proc in the program as resolved, so seeding and renaming
  -- cannot disagree. The diamond check runs first, while `model` still types every argument.
  let insts := collectSeeds program genComposites
  let seedDiags := ((mapLaurelProgramStmtExprM (m := StateM (List Message))
    (settleCallNode model ctx polyProcDefs [] {}) program).run []).2
  let (program, seeded) := (mapLaurelProgramStmtExprM (m := StateM RewriteState)
    (rewritePolyCallNode polyProcDefs {}) program).run {}
  let procInsts : Std.HashMap String ProcInst :=
    seeded.renamed.foldl (fun m pinst => m.insert (procInstKey pinst) pinst) {}

  -- 3. UNIFIED FIXPOINT — one fueled, depth-capped worklist over `Sum Inst ProcInst` that
  -- emits monomorph composites AND clones poly procedures; the two kinds feed each other:
  --   • a COMPOSITE (`.inl`) emits the monomorph and enqueues insts in its substituted types
  --     (`Box<int>` reachable only through `Pair<int>{b:Box<T>}`);
  --   • a PROCEDURE (`.inr`) clones the poly proc and enqueues composite insts from its
  --     types plus proc insts from poly calls (the proc→proc edge), discovered against
  --     the PRISTINE body (the clone's cleared ids aren't in `model`).
  -- TERMINATION: a divergent recursive generic grows type-arg DEPTH; `maxInstDepth` refuses to
  -- enqueue past the cap, recording ONE `NotYetImplemented` per base so divergence fails LOUD.
  -- 8 is a pragmatic ceiling: real nesting is a few levels, divergent `L<L<T>>` blows past it
  -- fast; a program genuinely needing depth > 8 is rejected (raise the cap if one appears).
  let maxInstDepth : Nat := 8
  let mut witnessComposites : List TypeDefinition := []  -- fresh opaque sorts for uncalled procs
  -- Worklist state (emitted monomorphs/clones, dedup sets, diags, pending items). Seed:
  -- composites from all collected type positions (.inl) + procs from call sites (.inr).
  let mut st : MonoState := {
    monoComposites := [], procClones := [], emitted := {}, clonedProcs := {},
    clonedBases := {}, diags := seedDiags, rejectedBases := {},
    worklist := (insts.toList.map (fun kv => Sum.inl kv.2)) ++ (procInsts.toList.map (fun kv => Sum.inr kv.2)) }
  -- Drain to a fixpoint (see `drainWorklist`).
  let fuel : Nat := 1024
  st := drainWorklist genComposites genDefs ctx polyProcDefs model maxInstDepth fuel st

  -- 3b. (gap: uncalled monomorphized poly procs) An indexed poly proc absent from
  -- `clonedBases` is genuinely UNCALLED (the proc→proc edge cloned every reachable one), so it
  -- would be dropped at emission with its contract UNCHECKED. To close the gap, synthesize a
  -- WITNESS: bind each type var to a FRESH composite (`$Witness$<proc>$<i>`), so the contract is
  -- checked somewhere rather than nowhere. Then drain again.
  -- MEASURED LIMIT — this is NOT a sort of arbitrary cardinality. `LowerComposite` flattens every
  -- composite to `datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }`, so a witness
  -- is no smaller than `int`: infinite, and in particular `exists y z : T. y != z` is PROVABLE at it (measured). A
  -- false-in-general contract therefore fails here only if it is false at an infinite type; one
  -- that holds at every type of size >= 2 but fails at a singleton is accepted. Real call sites
  -- are unaffected — each is monomorphized at its own concrete type and checked there — so the
  -- gap is confined to an UNCALLED procedure's contract being held to a weaker standard than
  -- "for all T". Genuinely arbitrary cardinality requires the encoder to mint a fresh
  -- uninterpreted sort, which is exactly what a witness cannot do from the Laurel side. Distinct
  -- type vars get distinct witness NAMES, but those names flatten to the same sort.
  -- (A value-`T` poly proc touching no generic composite, nor leaving a call to one of these
  -- unrenamed, is instead kept verbatim as a polymorphic Core proc, its body VC always emitted —
  -- checked by a different path.)
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
  st := drainWorklist genComposites genDefs ctx polyProcDefs model maxInstDepth fuel st

  let monoComposites : List TypeDefinition := st.monoComposites
  let procClones : List Procedure := st.procClones
  let mut diags : List Message := st.diags

  -- FUEL-EXHAUSTION GUARD (fail loud, never silently truncate). `maxInstDepth` is the real
  -- divergence guard; the coarser `fuel` backstop only bites a pathological program with >1024
  -- DISTINCT bounded-depth instantiations, which would otherwise leave a HALF-monomorphized
  -- program emitted silently. Diagnose instead, so a fuel wall fails loud like the depth cap.
  unless st.worklist.isEmpty do
    diags := diags ++ [diagnosticFromSource .unknown
      s!"monomorphization did not converge within {1024} instantiation steps (worklist still has {st.worklist.length} items): too many distinct generic instantiations. This is a tool limit, not a program error — report it if the program is reasonable."
      MessageKind.notYetImplemented]

  -- 4. Replace the generic composites and indexed poly procedures by their monomorphs and clones,
  -- and rewrite every type position. A generic composite leaves its family parent, which the
  -- monomorphs emitted for it extend.
  let kept := { program with
    types := program.types.map (fun
      | .Composite ct => if ct.typeArgs.isEmpty then .Composite ct else .Composite {
          name := mkId (genericFamilyPrefix ++ ct.name.text), typeArgs := [], extending := [],
          fields := [], instanceProcedures := [] }
      | td => td) ++ monoComposites ++ witnessComposites
    staticProcedures :=
      program.staticProcedures.filter (!polyProcDefs.contains ·.name.text) ++ procClones }
  let rewritten := mapLaurelProgramHighTypes (rewriteTy genComposites) kept
  -- Flag a USER identifier that collides with a generated monomorph name (`Box$a1$int`):
  -- `$` and the `$aN$` tag shape are legal in source, and `instTagCommon` is non-injective,
  -- so a user type can share a monomorph's name. Point the diagnostic at the user's own
  -- declaration (`td.name.source`) BEFORE re-resolution reports it against the source-less
  -- synthetic name. Compares against the names emission actually produced (no tag re-derivation);
  -- the re-resolution net still backstops collisions from other passes (`$heap`, dispatch `$impl`).
  let monoNames := monoComposites.map (·.name.text)
  diags := diags ++ program.types.filterMap fun td =>
    if monoNames.contains td.name.text then
      some (diagnosticFromSource td.name.source
        s!"'{td.name.text}' collides with a name generated for a generic-composite instantiation; \
           rename it (identifiers with the '$aN$' instantiation-tag shape can clash)"
        MessageKind.userError)
    else none

  return (rewritten, diags)

/-- Pipeline pass: monomorphize generic composites. -/
def monomorphizeCompositesPass : LaurelPass := .onUnordered {
  name := "MonomorphizeComposites"
  unsupported := [
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  creates := [NodeKind.TypeDefinition.Composite]
  -- Only the generic composite *definitions* are gone program-wide. `HighType.Applied` and
  -- `HighType.TVar` survive over generic datatypes and polymorphic procedures, which this
  -- pass leaves alone, so neither can be declared here.
  removes := [NodeKind.CompositeType.typeArgs.cons]
  needsResolves := true
  documentation := "Lowers generic composites (`composite Box<T>`) by emitting one concrete composite per used instantiation and rewriting `Box<int>` type references and `new Box` allocations to the monomorphic name. Each instantiation extends a field-free family parent that names their shared heap fields. Runs before heap parameterization." }
  fun _ p m => let (p', diags) := monomorphizeComposites p m; (p', diags, {})

end -- public section
end Strata.Laurel
