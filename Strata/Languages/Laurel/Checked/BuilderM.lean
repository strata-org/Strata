module
public import Strata.Languages.Laurel.Checked.Builder

/-!
# BuilderM monad

`BuilderM` is a default minimal implementation of the `Builder` interface that provides
a counter for fresh names and state for accumulating statements.
-/

public section
namespace Strata.Laurel.Checked

/-- Wrap a value in a source-free `AstNode` (defaults to `FileRange.unknown`). -/
private def rawNd {t : Type} (v : t) (source : FileRange := .unknown) : AstNode t :=
  { val := v, source := source }

/-! ## BuilderM and state definitions.  -/

/-- Mutable state of BuilderM -/
structure BuilderState where
  /-- Statements accumulated so far, in order. -/
  private stmts : Array (AstNode StmtExpr) := #[]
  /-- Counter for fresh local names. -/
  freshCtr : Nat := 0

protected def BuilderState.mkId (st : BuilderState) (hint : String): Identifier × BuilderState :=
  let ident := mkId s!"{hint}${st.freshCtr}"
  let st' := { st with freshCtr := st.freshCtr + 1 }
  (ident, st')

/--
A statement building monad with a fresh variable creator.
-/
structure BuilderM (α : Type) where
  monad : StateM BuilderState α

namespace BuilderM

instance : Monad BuilderM where
  pure r := ⟨pure r⟩
  bind m h := ⟨BuilderM.monad ∘ h =<< m.monad⟩

private instance : MonadState BuilderState BuilderM where
  get := ⟨get⟩
  set s := ⟨set s⟩
  modifyGet f := ⟨modifyGet f⟩

def runAndReturn {ret} (act : BuilderM (Expr ret)) : AstNode StmtExpr :=
  let (r, st) := act.monad.run {}
  let retStmt : AstNode StmtExpr := { val := .Return (some r.node), source := r.node.source }
  if st.stmts.isEmpty then
    retStmt
  else
    rawNd <| .Block (st.stmts.push retStmt).toList none

def runUnit (act : BuilderM Unit) : AstNode StmtExpr :=
  let ((), st) := act.monad.run {}
  rawNd <| .Block st.stmts.toList none

protected def emit (s : AstNode StmtExpr) : BuilderM Unit :=
  modify fun st => { st with stmts := st.stmts.push s }

protected def freshName (hint : String) : BuilderM Identifier :=
  modifyGet (BuilderState.mkId · hint)

/-- Run `body` against a fresh statement buffer and return the statements it emits as a
    `Block`, threading the fresh-name counter through (so it is not reset). -/
protected def captureBlock (body : BuilderM Unit) : BuilderM (AstNode StmtExpr) := do
  let outerStmts ← modifyGet fun s => (s.stmts, { s with stmts := #[] })
  body
  let innerStmts ← modifyGet fun s => (s.stmts.toList, { s with stmts := outerStmts })
  pure (rawNd (.Block innerStmts none))


instance : Builder BuilderM where
  emit := BuilderM.emit
  freshName := BuilderM.freshName
  captureBlock := BuilderM.captureBlock

end BuilderM

/-! ## Reification: builder body → `Laurel.Procedure` -/

private def mkInputs (params : Array (String × Ty)) : List Parameter :=
  params |>.map (fun (n, t) => { name := mkId n, type := rawNd t.highType }) |>.toList

/-- Package `Expr .bool` clauses as Laurel `Condition`s (default mode `Both`). -/
private def mkConditions (clauses : Array (Expr .bool)) : List Condition :=
  clauses.map (fun c => { condition := c.node }) |>.toList

/-- Construct a procedure that returns a value from a builder. -/
def reifyValueProc {ret : Ty}
    (name : String) (params : Array (String × Ty))
    (preconditions : Array (Expr .bool))
    (body : BuilderM (Expr ret)) : Procedure := {
    name := mkId name
    inputs := mkInputs params
    outputs := [{ name := mkId resultOutputName, type := rawNd ret.highType }]
    preconditions := mkConditions preconditions
    decreases := none
    body := .Transparent body.runAndReturn
  }

/-- Construct a procedure that does not return a value. -/
def reifyUnitProc
    (name : String) (params : Array (String × Ty))
    (preconditions : Array (Expr .bool))
    (body : BuilderM Unit) : Procedure := {
    name := mkId name
    inputs := mkInputs params
    outputs := []
    preconditions := mkConditions preconditions
    decreases := none
    body := .Transparent body.runUnit
  }
