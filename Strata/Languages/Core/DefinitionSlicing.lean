/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.DL.Imperative.EvalContext
public import Strata.DL.Imperative.PathConditionsFold

/-! # The definitions an obligation reads

An obligation's path condition defines variables (`init x := e`, a *definition*) that its goal
and its other entries may or may not read. Its *read definitions* are the ones the goal or a
non-definition entry reaches, directly or through the right-hand sides of read definitions. An
*unread definition* constrains only its own variable, which no other kept term mentions.
`readFold` computes what the entries of a path condition read incrementally, so obligations
that share a path prefix share its processing; `unreadDefinitions` adds an obligation's goal.
The discharge leaves an obligation's unread definitions out of its SMT query
(`ProofObligation.withoutDefinitions`).

Key definitions: `ReadState`, `readFold`, `readStateOf`, `unreadDefinitions`,
`ProofObligation.withoutDefinitions`. -/

namespace Core
open Imperative

public section

/-- The names of the free variables of `e`. -/
def freeVarNames (e : Expression.Expr) : List String :=
  (Lambda.LExpr.freeVars e).map (·.1.name)

/-- The names a path-condition entry reads: the free variables of an assumption, of a
    definition's right-hand side, or of the expressions of a distinctness fact; none for a
    declaration without a value. -/
def entryReadNames (e : PathConditionEntry Expression) : List String :=
  (entryExprs e).flatMap freeVarNames

/-- Add the names of `pending`, and every name they reach through `bodies`, to `reached`: a
    name not yet reached is added and the names of its bodies are queued. `fuel` bounds the
    names taken from the queue; the result is `none` when it runs out. -/
def reachThrough (bodies : Std.HashMap String (List String)) :
    Nat → List String → Std.HashSet String → Option (Std.HashSet String)
  | _, [], reached => some reached
  | 0, _ :: _, _ => none
  | fuel + 1, v :: pending, reached =>
    if reached.contains v then reachThrough bodies fuel pending reached
    else reachThrough bodies fuel (bodies.getD v [] ++ pending) (reached.insert v)

/-- What the entries of a path-condition prefix read: for each defined name, the names its
    right-hand sides read (`bodies`, the lists of total length `size`), and the names the
    non-definition entries read, closed through `bodies` (`reached`). `complete` is `false`
    once a closure has run out of fuel; then no definition is taken to be unread. -/
structure ReadState where
  bodies : Std.HashMap String (List String) := {}
  size : Nat := 0
  reached : Std.HashSet String := {}
  complete : Bool := true

/-- Add `names`, closed through the state's bodies, to its reached names. The fuel covers every
    name the closure can queue: the names given and those of the bodies. -/
def ReadState.reach (st : ReadState) (names : List String) : ReadState :=
  let { bodies, size, reached, complete } := st
  match reachThrough bodies (names.length + size) names reached with
  | some reached => { bodies, size, reached, complete }
  | none => { bodies, size, complete := false }

/-- Process one entry: a definition records the names its right-hand side reads and, when its
    variable is already reached, reaches them; any other entry reaches the names it reads. -/
def ReadState.step (st : ReadState) (entry : PathConditionEntry Expression) : ReadState :=
  match entry with
  | .varDecl x _ (.det e) =>
    let names := freeVarNames e
    let { bodies, size, reached, complete } := st
    let st : ReadState := { bodies := bodies.insert x.name (names ++ bodies.getD x.name [])
                            size := size + names.length, reached, complete }
    if st.reached.contains x.name then st.reach names else st
  | entry => st.reach (entryReadNames entry)

/-- The read state of the path conditions `pcs`, oldest first: `ReadState.step` over their
    entries in order. -/
def readStateOf (pcs : PathConditions Expression) : ReadState :=
  pcs.flatten.foldl ReadState.step {}

/-- `ReadState.step` as an incremental fold over path conditions
    (`Imperative.PathConditions.Fold`): advancing it to an obligation's path condition
    processes only the entries the previous obligation did not share. -/
def readFold : Imperative.PathConditions.Fold Empty ReadState Unit Expression where
  stepEntry st _ entry := .ok (st.step entry, ())
  emptyOutput := ()

/-- One entry's part in `unreadDefinitions`: the variable of a definition that `kept` does not
    contain is unread. -/
def unreadStep (kept : Std.HashSet String) (unread : Std.HashSet String) :
    PathConditionEntry Expression → Std.HashSet String
  | .varDecl x _ (.det _) => if kept.contains x.name then unread else unread.insert x.name
  | _ => unread

/-- The names of the unread definitions of `obligation`, given the read state `st` of its path
    conditions: the defined names that neither the goal nor `st`'s reached names reach. Empty
    when a closure has run out of fuel.

    Only deterministic definitions (`init x := e`) are ever unread; assumptions are always kept.
    Leaving out the definition of a variable nothing else reads keeps the query's
    satisfiability, but leaving out an assumption about such a variable could make an
    unsatisfiable path satisfiable, so that a dead cover would be reported reachable. -/
def unreadDefinitions (st : ReadState) (obligation : ProofObligation Expression) :
    Std.HashSet String :=
  let goalNames := freeVarNames obligation.obligation
  match st.complete, reachThrough st.bodies (goalNames.length + st.size) goalNames st.reached with
  | true, some kept =>
    obligation.assumptions.foldl (fun acc pc => pc.foldl (unreadStep kept) acc) {}
  | _, _ => {}

/-- `obligation` without its definitions named in `unread`. -/
def ProofObligation.withoutDefinitions (obligation : ProofObligation Expression)
    (unread : Std.HashSet String) : ProofObligation Expression :=
  if unread.isEmpty then obligation
  else { obligation with assumptions := obligation.assumptions.map fun pc => pc.filter fun
    | .varDecl x _ (.det _) => !unread.contains x.name
    | _ => true }

end -- public section

end Core
