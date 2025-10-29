/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.HasInputContext
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions

open Lean
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand)
open Lean.Elab.Term (TermElab)
open System (FilePath)

open Strata.Integration.Lean

namespace Strata

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
private def mkAbsIdent (name : Lean.Name) : Ident :=
  let nameStr := toString name
  .mk (.ident .none nameStr.toSubstring name [.decl name []])

private def mkScopedName {m} [Monad m] [MonadError m] [MonadEnv m] [MonadResolveName m] (name : Name) : m (Ident × Name) := do
  let scope ← getCurrNamespace
  let fullName := scope ++ name
  let env ← getEnv
  if env.contains fullName then
    throwError s!"Cannot define {name}: {fullName} already exists."
  return (Lean.mkScopedIdent scope name, fullName)

/--
Create a new definition equal to the given term.
-/
private def elabDef (ident : Ident) (type : Term) (qdef : Term) : CommandElabM Unit := do
  let cmd ← `(command| def $ident : $type := $qdef)
  tryCatch (elabCommand cmd) fun e =>
    throwError m!"Definition of {ident} failed: {e.toMessageData}"

private def quoteList : List Term → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[x, quoteList xs]

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
  -- Identifier for dialect
  let dialectName := Name.anonymous |>.str d.name
  let (dialectIdent, dialectAbsName) ← mkScopedName dialectName
  -- Identifier for dialect map
  let (mapIdent, _) ← mkScopedName (Name.anonymous |>.str s!"{d.name}_map")
  elabDef dialectIdent (mkAbsIdent ``Dialect) (quote d)
  -- Add dialect to environment
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d dialectAbsName (isNew := true))
  -- Create term to represent minimal DialectMap with dialect.
  let s := (dialectExt.getState (←Lean.getEnv))
  let .isTrue mem := inferInstanceAs (Decidable (d.name ∈ s.loaded.dialects))
    | throwError "Internal error with unknown dialect"
  let openDialects := s.loaded.dialects.importedDialects d.name mem |>.toList
  let quoteD (d : Dialect) : CommandElabM Term := do
      let some name := s.nameMap[d.name]?
        | throwError s!"Unknown dialect {d.name}"
      return mkAbsIdent name
  let ds ← openDialects.mapM quoteD
  let mapTerm : Term := Syntax.mkCApp ``DialectMap.ofList! #[quoteList ds]
  elabDef mapIdent (mkAbsIdent ``DialectMap) mapTerm

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← getInputContext
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let (_, d, s) ← Strata.Elab.elabDialect {} loaded inputCtx p e
  if !s.errors.isEmpty then
    for e in s.errors do
      logMessage e
    return
  -- Add dialect to command environment
  declareDialect d

declare_tagged_region term strataProgram "#strata" "#end"

private def listToExprAux {α} [ToExpr α]
    (nil : Lean.Expr)
    (cons : Lean.Expr)
    (append : Lean.Expr)
    (l : Array α) : Lean.Expr :=
  if l.size <= 8 then
    l.foldr (init := nil) fun a r => mkApp2 cons (toExpr a) r
  else
    let h := l.size / 2
    let x := listToExprAux nil cons append (l.extract (stop := h))
    let y := listToExprAux nil cons append (l.extract (start := h))
    mkApp2 append x y

private def listToExpr {α : Type u} [ToLevel.{u}] [ToExpr α] (l : List α) : Lean.Expr :=
  let type := toTypeExpr α
  let lvl := toLevel.{u}
  let nil  := mkApp (mkConst ``List.nil [lvl]) type
  let cons := mkApp (mkConst ``List.cons [lvl]) type
  let append := mkApp (mkConst ``List.append [lvl]) type
  listToExprAux nil cons append l.toArray

private def arrayToExpr {α : Type u} [ToLevel.{u}] [ToExpr α] (as : Array α) : Lean.Expr :=
  mkApp2 (mkConst ``List.toArray [toLevel.{u}]) (toTypeExpr α) (listToExpr as.toList)

def nilArrayOperation : Array Operation := #[]

def singleArrayOperation (op : Operation) : Array Operation := #[op]

@[noinline]
def appendArrayOperation (x y : Array Operation) : Array Operation := x ++ y

private def opArrayToExpr (as : Array Operation) : Lean.Expr :=
  let nil := mkConst ``nilArrayOperation
  let one := mkConst ``singleArrayOperation
  let app := mkConst ``appendArrayOperation
  if as.size = 0 then
    nil
  else
    let rec aux (start : Nat) (stop : Nat) : Lean.Expr :=
          if start + 1 >= stop then
            mkApp one (toExpr as[start]!)
          else
            let h := (start + stop) / 2
            mkApp2 app (aux start h) (aux h stop)
    aux 0 as.size

@[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (getInputContext : CoreM _)
  let s := (dialectExt.getState (←Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram s.loaded leanEnv inputCtx p e with
  | .ok pgm =>
    -- Get Lean name for dialect
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    return astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (opArrayToExpr pgm.commands)
  | .error errors =>
    for e in errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Program) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

@[command_elab loadDialectCommand]
def loadDialectImpl: CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (←absPath.pathExists) then
      throwError "Could not find file {dialectPath}"
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let (_, r) ← Elab.loadDialectFromPath {} loaded #[]
                        (path := dialectPath) (actualPath := absPath) (expected := .none)
    -- Add dialect to command environment
    match r with
    | .ok d =>
        declareDialect d
    | .error errorMessages =>
      assert! errorMessages.size > 0
      throwError (← Elab.mkErrorReport errorMessages)
  | _ =>
    throwUnsupportedSyntax

end Strata
