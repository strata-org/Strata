/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Laurel.Checked.Raw
public meta import Lean.Elab.Command
meta import Lean.Meta.Eval

/-!
# Generating checked combinators from Laurel declarations

`derive_laurel_ops P [keep f]` reads the Laurel program `P` at elaboration time and, for
the declarations whose name satisfies `f : String → Bool` (or *all* declarations when the
`keep` clause is omitted), generates type-safe Lean operations for constructing Laurel
expressions.

This does not support overloaded names and composite fields/constructors.  The Lean
definitions are not generated.

The Laurel declarations are the single source of truth; the generated combinators call
the same wrapper names, so lowering to Core is whatever the Laurel prelude already
arranges (e.g. `coreSetOpName?` / `coreSeqOpName?`).
-/

open Lean Lean.Elab Lean.Elab.Command
open Lean.Parser.Term (bracketedBinder bracketedBinderF)
open Strata Strata.Laurel
meta section

namespace Strata.Laurel.Checked

/-- Generate operations from the selected declarations of a Laurel program.
    `derive_laurel_ops <program> [keep <String → Bool>]`. The `keep` clause is an
    optional filter on what types are emitted. -/
syntax (name := deriveLaurelOps) "derive_laurel_ops " term:max (" keep " term)? : command

/-- The Lean-identifier characters of a Laurel name — drops `$` and anything else illegal in
    a Lean identifier (`isIdRest`). -/
def sanitizedName (name : String) : String :=
  name.foldl (init := "") fun s c => if Lean.isIdRest c then s.push c else s

/-- Translate a Laurel `HighType` to a `Ty` term. Type variables map to the generated
    def's `Ty` binders; named/applied types to the generated `Ty` constructors. -/
def laurelHighTypeToTyStx (tyVars knownTypes : Std.HashSet String) (ty : AstNode HighType) : Except String Term :=
  let ⟨tyv, _⟩ := ty
  match tyv with
  | .Applied ⟨base, _⟩ args => do
    let .UserDefined n := base
      | .error  "derive_laurel_ops: unsupported applied base type"
    if n.text ∉ tyVars ∧ n.text ∉ knownTypes then
      .error s!"references type '{n.text}', which was not generated"
    let argStxs ← args.toArray.attach.mapM fun ⟨a, _⟩ => laurelHighTypeToTyStx tyVars knownTypes a
    pure <| Syntax.mkApp (mkIdent (Name.mkSimple (sanitizedName n.text))) argStxs
  | .TBool => pure (mkIdent ``Ty.bool)
  | .TInt => pure (mkIdent ``Ty.int)
  | .TVar n => do
    if n.text ∉ tyVars then
      .error s!"derive_laurel_ops: missing type variable."
    pure <| mkIdent (Name.mkSimple n.text)
  | .TMap ktp vtp => do
    pure <| Syntax.mkApp (mkIdent ``Ty.totalMap) #[
      ← laurelHighTypeToTyStx tyVars knownTypes ktp,
      ← laurelHighTypeToTyStx tyVars knownTypes vtp
    ]
  | .TBv w =>
    pure (Syntax.mkApp (mkIdent ``Ty.bv) #[quote w])
  | .TReal =>
    pure (mkIdent ``Ty.real)
  | .TSet ktp => do
    pure <| Syntax.mkApp (mkIdent ``Ty.set) #[
      ← laurelHighTypeToTyStx tyVars knownTypes ktp
    ]
  | .TString =>
    pure (mkIdent ``Ty.string)
  | .UserDefined n =>
    -- Check name is a known type or var.
    if n.text ∈ tyVars ∨ n.text ∈ knownTypes then
      pure (mkIdent (Name.mkSimple (sanitizedName n.text)))
    else
      .error s!"references type '{n.text}', which was not generated"
  | .MultiValuedExpr _ | .Intersection _ | .Unknown  | .TFloat64 | .TVoid =>
    .error s!"derive_laurel_ops: unsupported Laurel type {repr tyv}"

/-- A Lean-identifier-safe form of a Laurel name: drops `$`, which is legal in a Laurel
    name but not in a Lean identifier. -/
def leanIdentOf (name : String) : CommandElabM Ident := do
  -- The result must still begin with an `isIdFirst` character.
  let filtered := sanitizedName name
  let some first := filtered.startPos.get?
    | throwError s!"derive_laurel_ops: name '{name}' has no identifier-legal characters"
  unless Lean.isIdFirst first do
    throwError s!"derive_laurel_ops: name '{name}' sanitizes to '{filtered}', which does not start with a legal identifier character"
  pure <| mkIdent <| Name.mkSimple filtered

/--
This maps Laurel names that are declared in the core prelude that require a
specialized Ty constructor (and do not use `Ty.named`).
-/
def builtinTyCtors : Std.HashMap String Name :=
  .ofList [("Set", ``Ty.set)]

/-- Generate Lean declaration for a declared type. -/
def genTypeCtor (laurelName : Identifier) (typeArgs : List Identifier) : CommandElabM Unit := do
  let nameId ← leanIdentOf laurelName.text
  let argIds := typeArgs.toArray.map fun ta => mkIdent (Name.mkSimple ta.text)
  let binders ← argIds.mapM fun id => `(bracketedBinder| ($id : Ty))
  let rhs : Term ← match builtinTyCtors[laurelName.text]? with
    | some ctor => pure (Syntax.mkApp (mkIdent ctor) argIds)
    | none => ``(Ty.named $(quote laurelName.text) [$argIds,*])
  elabCommand <| ← `(def $nameId $binders* : Ty := $rhs)

/--
Record `name`'s sanitized (Lean) form in `names`, returning `true` if the name is new, or
`false` if the sanitized name was already recorded (in which case the caller skips it with a
`logInfo`).
-/
def recordName (names : IO.Ref (Std.HashSet String)) (name : String) : CommandElabM Bool := do
  let present ← names.modifyGet (·.containsThenInsert (sanitizedName name))
  return !present

/--
Generate a datatype's checked combinators:
1. the `Ty` constructor (via `genTypeCtor`),
2. for each constructor a value constructor (`Good value…`) and a tester (`D.isGood`), and
3. a getter per field (`D.value`).

The datatype's type parameters become implicit `{a : Ty}` binders on every combinator.
-/
def genDatatype (names : IO.Ref (Std.HashSet String)) (knownTypes : Std.HashSet String)
    (dt : DatatypeDefinition) : CommandElabM Unit := do
  genTypeCtor dt.name dt.typeArgs
  let leanD := sanitizedName dt.name.text
  let dIdent ← leanIdentOf dt.name.text
  let tyArgIds := dt.typeArgs.toArray.map fun ta => mkIdent (Name.mkSimple ta.text)
  let implBinders ← tyArgIds.mapM fun id => `(bracketedBinder| { $id : Ty })
  -- The applied handle type `D a…` (bare `D` when monomorphic).
  let handleTy : Term ← if tyArgIds.isEmpty then `($dIdent) else pure (Syntax.mkApp dIdent tyArgIds)
  let tyVars : Std.HashSet String := dt.typeArgs.foldl (init := {}) fun s ta => s.insert ta.text
  let fieldTy (p : Parameter) : CommandElabM Term := do
    match laurelHighTypeToTyStx tyVars knownTypes p.type with
    | .ok t => pure t
    | .error e => throwError e
  let xId := mkIdent `x
  -- Getters are keyed by field name across all constructors. Laurel forbids two fields of the
  -- same name anywhere in a datatype, so conflicts cannot occur.
  let mut emittedGetters : Std.HashSet String := {}
  for c in dt.constructors do
    -- Skip colliding constructor names.
    if !(← recordName names c.name.text) then
      logInfo s!"derive_laurel_ops: skipping constructor '{c.name.text}': name collides with an already-generated definition"
      continue
    -- Value constructor: `def Good {a…} (value : Expr Val) : Expr (D a…) := rawCall "Good" […]`.
    let ctorId ← leanIdentOf c.name.text
    let mut valBinders : Array (TSyntax ``bracketedBinder) := #[]
    let mut valArgs : Array Term := #[]
    for p in c.args do
      let fId := mkIdent (Name.mkSimple p.name.text)
      valBinders := valBinders.push (← `(bracketedBinder| ($fId : Expr $(← fieldTy p))))
      valArgs := valArgs.push (← `(Expr.node $fId))
    elabCommand <| ← `(def $ctorId $(implBinders ++ valBinders)* : Expr $handleTy :=
      Expr.rawCall $(quote c.name.text) [$valArgs,*])
    -- Tester: `def D.isGood {a…} (x : Expr (D a…)) : Expr .bool := rawCall "D..isGood" [x.node]`.
    let testerId := mkIdent ((Name.mkSimple leanD).str s!"is{sanitizedName c.name.text}")
    elabCommand <| ← `(def $testerId $implBinders* ($xId : Expr $handleTy) : Expr .bool :=
      Expr.rawCall $(quote s!"{dt.name.text}..is{c.name.text}") [Expr.node $xId])
    -- Field getters: `def D.value {a…} (x : Expr (D a…)) : Expr Val := rawCall "D..value" [x.node]`.
    for p in c.args do
      let key := sanitizedName p.name.text
      if key ∈ emittedGetters then
        continue
      emittedGetters := emittedGetters.insert key
      let getterId := mkIdent ((Name.mkSimple leanD).str key)
      elabCommand <| ← `(def $getterId $implBinders* ($xId : Expr $handleTy) : Expr $(← fieldTy p) :=
        Expr.rawCall $(quote s!"{dt.name.text}..{p.name.text}") [Expr.node $xId])

/-- Generate a checked combinator for the procedure `p`, named after `p.name`. A
    procedure with no output is a statement-like call; its result type is `Ty.none` (void).
    Procedures whose signature references an ungenerated type, or that have multiple outputs,
    are skipped with a `logInfo`. -/
def genExternalProc (names : IO.Ref (Std.HashSet String)) (knownTypes : Std.HashSet String)
    (p : Procedure) : CommandElabM Unit := do
  let skip (reason : String) : CommandElabM Unit :=
    logInfo s!"derive_laurel_ops: skipping procedure '{p.name.text}': {reason}"
  let tyVars : Std.HashSet String := p.typeArgs.foldl (init := {}) fun s ta => s.insert ta.text
  let tyBinders ← p.typeArgs.toArray.mapM fun ta =>
    `(bracketedBinderF| { $(mkIdent (Name.mkSimple ta.text)) : Ty })
  let inputCount := p.inputs.length
  let mut valBinders : Array (TSyntax ``bracketedBinder) := .mkEmpty (c := inputCount)
  let mut argMds : Array Term := .mkEmpty (c := inputCount)
  for inp in p.inputs do
    match laurelHighTypeToTyStx tyVars knownTypes inp.type with
    | .error e => return ← skip e
    | .ok ty =>
      let id := mkIdent (Name.mkSimple inp.name.text)
      valBinders := valBinders.push (← `(bracketedBinderF| ($id : Expr $ty)))
      argMds := argMds.push (← `(Expr.node $id))
  -- A combinator returns a single `Expr R`: no output ⇒ `Ty.none` (void), exactly one ⇒ its
  -- type. Multiple outputs have no single result type, so skip.
  let retTy : Term ← match p.outputs with
      | [] => `(Ty.none)
      | [output] =>
        match laurelHighTypeToTyStx tyVars knownTypes output.type with
        | .ok ty => pure ty
        | .error e => return ← skip e
      | _ => return ← skip s!"has {p.outputs.length} outputs; only single-output procedures are supported"
  let nameId ← leanIdentOf p.name.text
  unless ← recordName names p.name.text do
    return ← skip "name collides with an already-generated definition"
  let binders := tyBinders ++ valBinders
  elabCommand (← `(def $nameId $binders:bracketedBinder* : Expr $retTy := Expr.rawCall $(quote p.name.text) [$argMds,*]))

@[command_elab deriveLaurelOps]
public def elabDeriveLaurelOps : CommandElab := fun stx => do
  match stx with
  | `(command| derive_laurel_ops $progStx $[keep $filtStx?]?) =>
    let (program, sel) ← liftTermElabM do
      let pe ← Term.elabTermEnsuringType progStx (mkConst ``Program)
      Term.synthesizeSyntheticMVarsNoPostponing
      let program ← unsafe Meta.evalExpr Strata.Laurel.Program (mkConst ``Program) pe
      -- No `keep` clause ⇒ keep everything.
      let sel : String → Bool ←
        match filtStx? with
        | none =>
          pure (fun (_ : String) => (true : Bool))
        | some filtStx => do
          let boolArrow ← Lean.mkArrow (mkConst ``String) (mkConst ``Bool)
          let fe ← Term.elabTermEnsuringType filtStx (expectedType? := some boolArrow)
          Term.synthesizeSyntheticMVarsNoPostponing
          unsafe Meta.evalExpr (String → Bool) boolArrow fe
      pure (program, sel)
    -- Get selected types we will generate.
    -- A procedure or field whose signature references any other named type is
    -- skipped, so generated combinators never mention a `Ty` that was not emitted.
    let knownTypes : Std.HashSet String := program.types.foldl (init := {}) fun s td =>
      let name := td.name
      if sel name.text then s.insert name.text else s
    -- Types must NOT overload: two type declarations sharing a sanitized Lean name is an
    -- error (a `Ty` constructor has no signature to disambiguate on).
    let typeNames : IO.Ref (Std.HashSet String) ← IO.mkRef {}
    -- Records a selected type's name, returning whether it should be generated. Errors if its
    -- sanitized name collides with an already-recorded type.
    let recordType name : CommandElabM Bool := do
          if sel name then
            let key := sanitizedName name
            let present ← typeNames.modifyGet (·.containsThenInsert key)
            if present then
              throwError s!"derive_laurel_ops: overloaded type '{name}' (collides on '{key}')"
            return true
          else
            return false

    for td in program.types do
      if ← recordType td.name.text then
        match td with
        | .Opaque ot => genTypeCtor ot.name ot.typeArgs
        | .Datatype dt => genDatatype typeNames knownTypes dt
        | .Alias ta => genTypeCtor ta.name ta.typeArgs
        -- N.B. We do not yet generate accessors/constructors for composites.
        | .Composite ty => genTypeCtor ty.name ty.typeArgs
        | .Constrained ty => genTypeCtor ty.name []
    -- Procedures MAY overload in Laurel (by signature) but Lean `def`s cannot. Count selected
    -- procedures by sanitized name, log each overloaded operator once, and emit only the
    -- non-overloaded ones.
    let procCounts : Std.HashMap String Nat :=
          program.staticProcedures.foldl (init := {}) fun counts p =>
            if sel p.name.text then
              let key := sanitizedName p.name.text
              counts.alter key fun mc => some (mc.getD 0 + 1)
            else
              counts
    let overloads := procCounts.toArray |>.filter (fun (_, c) => c > 1) |>.qsort (·.fst < ·.fst)
    for (key, _) in overloads do
      logInfo s!"derive_laurel_ops: skipping overloaded procedure '{key}'"
    for p in program.staticProcedures do
      if sel p.name.text && procCounts.getD (sanitizedName p.name.text) 0 ≤ 1 then
        genExternalProc typeNames knownTypes p
  | _ => throwUnsupportedSyntax

end Strata.Laurel.Checked
end -- meta section
