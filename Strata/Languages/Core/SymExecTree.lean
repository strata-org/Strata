/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PathExplorer

/-! # The path tree as an obligation program

`Result.treeStmts` writes a run's path tree as one statement list of `assume`s, `assert`s,
`cover`s and nested `if *`s, from which obligation extraction recovers each obligation.
-/

namespace Core.SymExec

open Imperative Lambda

@[expose] public section

/-- The statements for the entries of the path condition `pc` (newest first) beyond its oldest
    `k`, oldest first: for a join symbol's definition `s == v` (`joinDefSym?`, against the join
    symbols the entries before it define), `s` annotated with its type `ty`, the declaration
    `init s : ty := v`; an `assume` for every other entry. -/
def newAssumes (pc : List (String × Expression.Expr)) (k : Nat) : List Statement :=
  let defined := joinDefsOf (pc.drop (pc.length - k))
  ((pc.take (pc.length - k)).reverse.foldl (fun (d, out) (l, e) =>
    match joinDefSym? d l e, e with
    | some s, .eq _ (.fvar _ x (some ty)) v =>
      (d.insert s, out.push (Statement.init x (.forAll [] ty) (.det v) #[]))
    | some s, _ => (d.insert s, out.push (Statement.assume l e #[]))
    | none, _ => (d, out.push (Statement.assume l e #[])))
    (defined, (#[] : Array Statement))).2.toList

/-- The `assert`/`cover` checking an obligation's condition. -/
def checkStmt (o : Obl) : Statement :=
  match o.kind with
  | .assert => Statement.assert o.label o.cond o.md
  | .cover => Statement.cover o.label o.cond o.md

/-- The statements of node `i` and its subtree, given that the oldest `k` entries of its path
    condition are already assumed on the way to it: each obligation preceded by the `assume`s
    added since the previous one, then the children as `if *` branches, each starting with the
    `assume`s up to its own start (the fork's condition). An assumption is written once, on the
    tree edge where it is introduced; obligation extraction scopes each branch's assumptions
    to that branch, so it recovers each obligation with its own path condition. `fuel` bounds the
    depth of the recursion; at `0` the subtree becomes a failing check
    (`<symexec_tree_depth>`), so it is never reported verified. -/
def nodeStmts (r : Result) (children : Array (List Nat)) (fuel i k : Nat) : List Statement :=
  match fuel, r.nodes[i]? with
  | _, none => []
  | 0, some _ => [Statement.assert "<symexec_tree_depth>" Core.false #[]]
  | fuel + 1, some n =>
    let (stmts, k) := n.obls.foldl (fun (acc, k) o =>
      ((acc ++ newAssumes o.pc k).push (checkStmt o), o.pc.length)) ((#[] : Array Statement), k)
    let stmts := stmts.toList
    let branch (j : Nat) : List Statement :=
      match r.nodes[j]? with
      | none => []
      | some c => newAssumes c.startPc k ++ nodeStmts r children fuel j c.startPc.length
    let forkStmts := match (children[i]?.getD []).reverse with
      | [] => []
      | j :: js => js.foldl (fun acc j' => [.ite .nondet (branch j') acc #[]]) (branch j)
    -- The merged continuation, if the branches merged: after the `if *`, under the shared prefix
    -- plus the merged entries.
    let contStmts := match n.cont >>= (r.nodes[·]?) with
      | some c =>
        newAssumes c.startPc k ++ nodeStmts r children fuel (n.cont.getD 0) c.startPc.length
      | none => []
    stmts ++ forkStmts ++ contStmts

/-- The path tree as one statement list in obligation form (`assume`, `assert`, `cover`,
    nested `if *`). Unreached checks (`Result.unreached`) are not included. -/
def Result.treeStmts (r : Result) : List Statement :=
  let children := (List.range r.nodes.size).foldl (fun (cs : Array (List Nat)) i =>
    match r.nodes[i]? >>= (·.parent) with
    | some p => cs.modify p (· ++ [i])
    | none => cs) (Array.replicate r.nodes.size [])
  -- A node's children and continuation are created after it, so every chain of `nodeStmts`
  -- calls visits increasing node indices: `r.nodes.size` levels suffice.
  nodeStmts r children r.nodes.size 0 0

end -- public section

end Core.SymExec
