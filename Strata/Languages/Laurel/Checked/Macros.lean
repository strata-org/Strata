module
public import Strata.Languages.Laurel.Checked.Raw

namespace Strata.Laurel.Checked

public section

/-! ## `do`-notation sugar -/

/-- `ll:if c then <stmts> [ll:else <stmts>]` — a Laurel conditional as a builder statement. -/
scoped syntax (name := llIfElem) "ll:if " term " then " doSeq (ppDedent(ppLine) "ll:else " doSeq)? : doElem

/-- Emit a Laurel `if cond then { … }` (no else). -/
def lif {m} [Builder m] (cond : Expr .bool) (thenBody : m Unit) : m Unit := do
  emitStmt <| .IfThenElse cond.node (← captureBlock thenBody) none

/-- Emit a Laurel `if cond then { … } else { … }`. -/
def lifElse {m} [Builder m] (cond : Expr .bool) (thenBody elseBody : m Unit) : m Unit := do
  let t ← captureBlock thenBody
  let e ← captureBlock elseBody
  emitStmt <| .IfThenElse cond.node t (some e)

macro_rules
  | `(llIfElem| ll:if $c then $t:doSeq) => `(doElem| lif $c (do $t))
  | `(llIfElem| ll:if $c then $t:doSeq ll:else $e:doSeq) => `(doElem| lifElse $c (do $t) (do $e))

/-- `ll:while c do <stmts>` — a Laurel pre-test loop as a builder statement. -/
scoped syntax (name := llWhileElem) "ll:while " termBeforeDo " do " doSeq : doElem

/-- Emit a Laurel pre-test `while cond { … }` loop. -/
def lwhile {m} [Builder m] (cond : Expr .bool) (body : m Unit) : m Unit := do
  emitStmt <| .While cond.node [] none (← captureBlock body) false

macro_rules
  | `(llWhileElem| ll:while $c do $b:doSeq) => `(doElem| lwhile $c (do $b))

/-- `ll:set recv.field val` — assign `val` to field `field` of composite `recv`. The target
    must be exactly `receiver.field`; deeper paths are rejected. -/
scoped syntax (name := llSetElem) "ll:set " ident term : doElem

macro_rules
  | `(llSetElem| ll:set $lhs:ident $val:term) => do
      match lhs.getId with
      | .str (.str .anonymous recv) field =>
        let r : Lean.Syntax.Term ← ``(Expr.rawSetField $(Lean.mkIdentFrom lhs (Lean.Name.mkSimple recv)) $(Lean.Syntax.mkStrLit field) $val)
        `(doElem| $r:term)
      | _ => Lean.Macro.throwErrorAt lhs "ll:set expects a `receiver.field` target"
