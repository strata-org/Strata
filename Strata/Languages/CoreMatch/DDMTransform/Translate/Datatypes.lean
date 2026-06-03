/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic
public import Strata.Languages.Core.TypeDecl
public import Strata.DL.Lambda.TypeFactory

/-!
Datatype cache, derived `LDatatype` synthesis, and symbol resolution
against `TransState.gctx`.
-/

namespace Strata.CoreMatch.Translate

open Lambda

public section

def addDatatype (n : String) (info : DatatypeInfo) : TransM Unit :=
  modify fun s => { s with datatypes := s.datatypes.insert n info }

def lookupDatatype (n : String) : TransM (Option DatatypeInfo) := do
  return (← StateT.get).datatypes.get? n

def lookupCtor (dtName ctor : String) : TransM (Option (List String)) := do
  return ((← lookupDatatype dtName) >>= (·.find? (·.1 == ctor))).map (·.2)

/-- Synthesise an `LDatatype Unit` from cached info. Field types are
stubbed with `.int`: lowering and `ArmCheck` only inspect constructor
names and field counts, and user-visible field types come from each
arm's pattern binders. -/
private def synthLDatatype (n : String) (info : DatatypeInfo)
    : Except String (LDatatype Unit) :=
  match info with
  | [] => .error s!"datatype '{n}' has no constructors"
  | c :: rest =>
    let toConstr : String × List String → LConstr Unit := fun (cname, fields) =>
      { name       := mkIdent cname
        args       := fields.map fun fn => (mkIdent fn, .int)
        testerName := s!"{n}..is{cname}" }
    .ok { name := n, typeArgs := [],
          constrs := toConstr c :: rest.map toConstr,
          constrs_ne := by simp }

def lookupLDatatype (n : String) : TransM (LDatatype Unit) := do
  match (← lookupDatatype n) with
  | none => throw <| .fromMessage s!"match: datatype '{n}' is not declared"
  | some info =>
    match synthLDatatype n info with
    | .ok dt => return dt
    | .error msg => throw <| .fromMessage s!"match: {msg}"

def getFVarIsOp (i : Nat) : TransM Bool := do
  let s ← StateT.get
  match s.fvarIsOp[i]? with
  | some b => return b
  | none =>
    -- Fall back to inspecting the GlobalContext when the symbol is
    -- outside the precomputed range (e.g. inherited via a dialect import).
    return s.gctx.vars[i]? |>.any (·.2 matches .expr _)

/-- Resolve a DDM bound variable. A pattern-binder slot stores
`bvar 0` as a tag and the de Bruijn index is derived from the slot's
stack position; any other slot stores a pre-built reference. -/
def getBVarExpr (m : SourceRange) (i : Nat) : TransM Core.Expression.Expr := do
  let xs := (← StateT.get).bvars
  match xs[xs.size - 1 - i]? with
  | some (.bvar _ _) => return .bvar () i
  | some e           => return e
  | none             => throwAt m s!"unknown bound variable {i}"

end

end Strata.CoreMatch.Translate
