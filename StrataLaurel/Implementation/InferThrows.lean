/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages
public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.SemanticModel
public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LiftInstanceProcedures

/-! ### Inferred `throws` clauses

A procedure whose `throws` clause is marked inferred (`throws (e: inferred)`, or
`throws (e: T inferred)` to keep a declared part) gets as its thrown type the join
of its declared type and every exception type that may escape its body uncaught.
"May escape" is `exceptionEscapesWith`, the same over-approximation that checks a
declared `throws` against the body, so the inferred type always passes that check.

A call to an inferred procedure contributes the type inferred for it, so the
types are computed together as a fixpoint over the call graph, bounded by fuel.

Each procedure is inferred from its own body only, so its type does not depend on
its overrides. An override (`virtualDispatchFamilies`) is capped at the type of the
method it overrides, as a checked `throws` is in Java: a call through the base never
sees more than the base's type. An override may throw less than its base, or
nothing. What escapes an override beyond its cap is asserted not to happen by
`EliminateExceptions`, which is why the filled-in clause stays marked inferred.

The result fills in the clause with the inferred type, or removes it when nothing
escapes. It is an error when the escaping types have no common supertype, when an
escaping type mentions a type variable, when an inferred procedure has no body (its
type must be declared), when a procedure states `throwsOn` cases but nothing can
escape its body, and when a procedure states `throwsOn` cases for its declared type
but inference would widen that type (the cases' binding would then have the wider
type).

Inference needs a resolved program (callees and expression types), but the
resolution checks that read `throws` (escape bounds, `catch` binding types, the
lowering guards) must see the inferred types, so `resolveWithInferredThrows` runs
inference between resolutions.
-/

namespace Strata.Laurel

public section

/-- Key identifying a procedure across the program and the semantic model: its
    definition id once resolved, its name otherwise. -/
private def procKey (p : Procedure) : String :=
  match p.name.uniqueId with
  | some id => s!"#{id}"
  | none => p.name.text

private def procBody? (proc : Procedure) : Option StmtExprMd :=
  match proc.body with
  | .Transparent b => some b
  | .Opaque _ (some impl) _ => some impl
  | _ => none

/-- Every procedure that can carry a `throws` clause, in program order (static
    procedures, then each composite's instance procedures), with the name shown in
    diagnostics. -/
private def namedProcedures (program : LaurelProgram) : List (String × Procedure) :=
  program.staticProcedures.map (fun p => (p.name.text, p)) ++
  program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures.map fun p => (s!"{ct.name.text}.{p.name.text}", p)
    | _ => []

/-- Inferred thrown types, keyed by `procKey`. `none` means nothing escapes. -/
private abbrev InferredThrows := Std.HashMap String (Option HighTypeMd)

private def optHighEq : Option HighTypeMd → Option HighTypeMd → Bool
  | some a, some b => highEq a b
  | none, none => true
  | _, _ => false

/-- A callee's thrown type: the type inferred so far for an inferred procedure,
    the declared one otherwise. -/
private def currentThrowsOf (current : InferredThrows) (q : Procedure) : Option HighTypeMd :=
  if q.throwsInferred then (current.get? (procKey q)).join else q.throwsType

/-- The types that may leave `proc` on its own: its declared type (`declaredOf`)
    plus the body's escapes, reading callee types from `current`. -/
private def ownLeavingTypes (model : SemanticModel) (lattice : TypeLattice)
    (declaredOf : Procedure → Option HighTypeMd) (current : InferredThrows) (proc : Procedure)
    : List HighTypeMd :=
  let escapes := match procBody? proc with
    | some body => (exceptionEscapesWith model lattice (currentThrowsOf current) body (atCallTypeArgs := true)).map Prod.fst
    | none => []
  (declaredOf proc).toList ++ escapes

/-- The methods each procedure overrides, keyed by `procKey`: for every dispatch
    family, the family's method is a base of each overrider's override. -/
private def overriddenBases (model : SemanticModel) (program : LaurelProgram)
    : Std.HashMap String (List Procedure) :=
  (virtualDispatchFamilies model program).foldl (init := {}) fun acc fam =>
    fam.overriders.foldl (init := acc) fun acc' ov =>
      match findOverrideIn ov fam.method with
      | some o =>
        let k := procKey o
        acc'.insert k (fam.method :: (acc'.get? k).getD [])
      | none => acc'

/-- Whether a thrown type `a` fits under `b` (`none` is "throws nothing"). -/
private def fitsUnder (lattice : TypeLattice) : Option HighTypeMd → Option HighTypeMd → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => isSubtype lattice a b

/-- A procedure's own type: the join of its leaving types (`some none` when nothing
    leaves it), or `none` when they have no common supertype. -/
private def ownType (lattice : TypeLattice) (tys : List HighTypeMd) : Option (Option HighTypeMd) :=
  match tys with
  | [] => some none
  | _ => (lattice.commonAncestorType tys).map some

/-- `own`, capped by the thrown types of the methods it overrides (`caps`): `own`
    when it fits under every cap, otherwise the narrowest cap that fits under all
    the others (`none` when there is none). What escapes beyond the result is
    asserted not to happen by `EliminateExceptions`. -/
private def capped (lattice : TypeLattice) (own : Option HighTypeMd)
    (caps : List (Option HighTypeMd)) : Option HighTypeMd :=
  if caps.all (fitsUnder lattice own ·) then own
  else (caps.find? fun c => caps.all (fitsUnder lattice c ·)).join

/-- One round of the fixpoint: recompute every inferred procedure from `current`.
    A procedure whose own types have no join keeps its previous value; the error is
    reported once the iteration has settled. -/
private def inferRound (model : SemanticModel) (lattice : TypeLattice)
    (declaredOf : Procedure → Option HighTypeMd) (bases : Std.HashMap String (List Procedure))
    (procs : List Procedure) (current : InferredThrows) : InferredThrows :=
  procs.foldl (init := current) fun acc p =>
    match ownType lattice (ownLeavingTypes model lattice declaredOf current p) with
    | none => acc
    | some own =>
      let caps := ((bases.get? (procKey p)).getD []).map (currentThrowsOf current)
      acc.insert (procKey p) (capped lattice own caps)

private def inferFixpoint (model : SemanticModel) (lattice : TypeLattice)
    (declaredOf : Procedure → Option HighTypeMd) (bases : Std.HashMap String (List Procedure))
    (procs : List Procedure) : Nat → InferredThrows → InferredThrows
  | 0, current => current
  | fuel + 1, current =>
    let next := inferRound model lattice declaredOf bases procs current
    if procs.all (fun p => optHighEq (next.get? (procKey p)).join (current.get? (procKey p)).join)
    then current
    else inferFixpoint model lattice declaredOf bases procs fuel next

private def typeNames (tys : List HighTypeMd) : String :=
  ", ".intercalate (tys.map fun t => s!"'{formatHighTypeVal t.val}'")

/-- Infer the `throws` type of every inferred procedure of a resolved program.
    Returns, in `namedProcedures` order, `none` for a procedure to leave as it is
    (not inferred, or inference failed with a diagnostic) and `some ty?` for the
    inferred type (`some none` when nothing escapes), plus the diagnostics.

    `declared`, in `namedProcedures` order, gives each procedure's declared type
    when `program` carries an earlier guess in its inferred clauses' `throwsType`
    (see `resolveWithInferredThrows`); by default it is read from `program`. -/
def inferThrows (model : SemanticModel) (program : LaurelProgram)
    (declared : Option (List (Option HighTypeMd)) := none)
    : List (Option (Option HighTypeMd)) × List Message :=
  let lattice := TypeLattice.ofTypes program.types
  let named := namedProcedures program
  let declaredMap : Std.HashMap String (Option HighTypeMd) :=
    match declared with
    | some ds => (named.zip ds).foldl (init := {}) fun acc ((_, p), d) => acc.insert (procKey p) d
    | none => {}
  let declaredOf (p : Procedure) : Option HighTypeMd :=
    (declaredMap.get? (procKey p)).getD p.throwsType
  let displayNames : Std.HashMap String String :=
    named.foldl (init := {}) fun acc (n, p) => acc.insert (procKey p) n
  let displayName (p : Procedure) : String := (displayNames.get? (procKey p)).getD p.name.text
  let procs := (named.map (·.2)).filter (·.throwsInferred)
  let bases := overriddenBases model program
  -- A procedure's own type only widens as callee types widen, and its cap only
  -- widens with its base's, so each type changes at most about once per type in
  -- the hierarchy.
  let fuel := procs.length * (program.types.length + 2) + 1
  let initial : InferredThrows := procs.foldl (init := {}) fun acc p =>
    acc.insert (procKey p) (declaredOf p)
  let final := inferFixpoint model lattice declaredOf bases procs fuel initial
  -- An escape whose type mentions a type variable is not concrete until
  -- monomorphization, so no type can be inferred for it.
  let tvarDiags := procs.filterMap fun proc =>
    let escapes := match procBody? proc with
      | some body => exceptionEscapesWith model lattice (currentThrowsOf final) body (keepTVars := true) (atCallTypeArgs := true)
      | none => []
    (escapes.find? (mentionsTVar ·.1.val)).map fun (ty, _) =>
      (procKey proc, diagnosticFromSource proc.name.source
        s!"cannot infer the `throws` type of procedure '{displayName proc}': the exception type '{formatHighTypeVal ty.val}' that may escape it mentions a type variable. Declare the `throws` type instead.")
  let joinDiags := procs.filterMap fun proc =>
    let tys := ownLeavingTypes model lattice declaredOf final proc
    if (ownType lattice tys).isNone then
      some (procKey proc, diagnosticFromSource proc.name.source
        s!"cannot infer the `throws` type of procedure '{displayName proc}': the exceptions that may escape it ({typeNames tys}) have no common supertype")
    else none
  -- A procedure without a body has nothing to infer from, so its type must be
  -- stated: inferring it from its overrides would make its contract depend on them.
  let bodilessDiags := procs.filterMap fun proc =>
    if (procBody? proc).isNone then
      some (procKey proc, diagnosticFromSource proc.name.source
        s!"cannot infer the `throws` type of procedure '{displayName proc}': it has no body. Declare the `throws` type instead.")
    else none
  let joinFailed : Std.HashSet String :=
    (tvarDiags ++ joinDiags ++ bodilessDiags).foldl (init := {}) fun acc (k, _) => acc.insert k
  let procDiags := procs.flatMap fun proc =>
    let inferred := (final.get? (procKey proc)).join
    -- `inferred` is also `none` when inference failed above; that failure is
    -- already reported, and something does escape.
    let noEscape :=
      if inferred.isNone && !proc.throwsOn.isEmpty && !joinFailed.contains (procKey proc) then
        [(procKey proc, diagnosticFromSource proc.name.source
          s!"procedure '{displayName proc}' states `throwsOn` cases, but no exception can escape its body, so it has no inferred `throws` type")]
      else []
    let widened := match declaredOf proc, inferred with
      | some declared, some ty =>
        if !proc.throwsOn.isEmpty && !highEq declared ty then
          [(procKey proc, diagnosticFromSource proc.name.source
            s!"cannot infer the `throws` type of procedure '{displayName proc}': its `throwsOn` cases are stated for the declared type '{formatHighTypeVal declared.val}', but other exceptions may escape too, which would widen the type to '{formatHighTypeVal ty.val}'. Catch the other exceptions in the body, or remove the `throwsOn` cases.")]
        else []
      | _, _ => []
    noEscape ++ widened
  let diags := bodilessDiags ++ tvarDiags ++ joinDiags ++ procDiags
  let failed : Std.HashSet String := diags.foldl (init := {}) fun acc (k, _) => acc.insert k
  let results := named.map fun (_, p) =>
    if p.throwsInferred && !failed.contains (procKey p) then some (final.get? (procKey p)).join
    else none
  (results, diags.map (·.2))

/-- Fill in each inferred clause of `program` with its inferred type, taking the
    results in `namedProcedures` order. An empty inference removes the clause; a
    `none` result leaves the procedure unchanged. A filled-in clause stays marked
    inferred: `EliminateExceptions` asserts that what escapes beyond its type (an
    override's escapes beyond its cap) does not happen, in place of resolution's
    subtype check.

    With `asGuess`, the clauses stay inferred and only their `throwsType` is set,
    so a resolution of the result types `catch` bindings from the inferred types
    while its checks still skip the clauses. -/
private def applyInferredThrows (program : LaurelProgram) (results : List (Option (Option HighTypeMd)))
    (asGuess : Bool := false) : LaurelProgram :=
  let step (proc : Procedure) : StateM (List (Option (Option HighTypeMd))) Procedure := do
    let result := (← get).head?.join
    modify List.tail
    return match result with
      | none => proc
      | some ty? =>
        if asGuess then { proc with throwsType := ty? }
        else match ty? with
          | some ty => { proc with throwsType := some ty }
          | none => { proc with throwsType := none, throwsBinding := none, throwsInferred := false }
  let run : StateM (List (Option (Option HighTypeMd))) LaurelProgram := do
    let statics ← program.staticProcedures.mapM step
    let types ← program.types.mapM fun
      | .Composite ct => do
        pure (.Composite { ct with instanceProcedures := ← ct.instanceProcedures.mapM step })
      | td => pure td
    pure { program with staticProcedures := statics, types := types }
  (run.run' results : Id LaurelProgram)

/-- Whether any procedure of `program` has an inferred `throws` clause. -/
private def hasInferredThrows (program : LaurelProgram) : Bool :=
  (namedProcedures program).any (·.2.throwsInferred)

private def sameResults (a b : List (Option (Option HighTypeMd))) : Bool :=
  a.length == b.length && (a.zip b).all fun
    | (some x, some y) => optHighEq x y
    | (none, none) => true
    | _ => false

/-- Repeat inference until its results stop changing. Each round resolves
    `program` with the previous results as guesses (`applyInferredThrows` with
    `asGuess`), so a `catch` binding around a call to an inferred procedure has
    the type inferred for it, and a rethrow of that binding contributes it. -/
private def inferUntilStable (resolveFresh : LaurelProgram → ResolutionResult)
    (program : LaurelProgram) (declared : List (Option HighTypeMd))
    : Nat → List (Option (Option HighTypeMd)) × List Message
      → List (Option (Option HighTypeMd)) × List Message
  | 0, last => last
  | fuel + 1, (results, _) =>
    let r := resolveFresh (applyInferredThrows program results (asGuess := true))
    let next := inferThrows r.model r.program (declared := some declared)
    if sameResults next.1 results then next
    else inferUntilStable resolveFresh program declared fuel next

/-- Resolve `program`, first inferring any inferred `throws` clauses, then write the
    inferred types into the *unresolved* program and resolve that from scratch, so
    every resolution check sees ordinary `throws` clauses. A program without
    inferred clauses is resolved once. The arguments are `resolve`'s.

    Inference first runs on the plain resolution of `program`, where a `catch`
    binding around a call to an inferred procedure has no type yet. It then repeats
    on resolutions that carry the inferred types (`inferUntilStable`) until they
    stop changing; when no `catch` binding is rethrown that takes one extra
    resolution.

    Only the final resolution's errors are reported: the earlier ones can come from
    the missing inferred types, and the others recur there. A procedure whose
    inference failed keeps its inferred clause, which the resolution checks skip, so
    only the inference diagnostic is reported for it. -/
def resolveWithInferredThrows (program : LaurelProgram)
    (gradualTypes : Std.HashSet String := {})
    (realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none)
    (toBool : Option (HighType → StmtExprMd → StmtExprMd) := none)
    (reservedNames : Std.HashSet String := {}) : ResolutionResult :=
  let resolveFresh (p : LaurelProgram) :=
    resolve p (gradualTypes := gradualTypes) (realizeCoercion := realizeCoercion)
      (toBool := toBool) (reservedNames := reservedNames)
  let first := resolveFresh program
  if !hasInferredThrows program then first
  else
    let declared := (namedProcedures first.program).map (·.2.throwsType)
    -- A round that changes the results widens some procedure's type, which
    -- happens at most this often (as for the fuel in `inferThrows`).
    let fuel := (namedProcedures program).length * (program.types.length + 2) + 1
    let (results, diags) := inferUntilStable resolveFresh program declared fuel
      (inferThrows first.model first.program)
    let second := resolveFresh (applyInferredThrows program results)
    { second with errors := second.errors ++ diags.toArray }

end

end Strata.Laurel
