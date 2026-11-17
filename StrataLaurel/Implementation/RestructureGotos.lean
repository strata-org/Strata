/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.LabelledJumps
import StrataLaurel.Implementation.StackShape

/-!
# Restructure Gotos

Lowers the two block features Core has no counterpart for: a `goto L` back to
the start of an enclosing block, and the invariants and termination measure a
block carries. Core's structured statements only offer `exit` (a forward jump
past the end of an enclosing block) and `while`, so a block that some `goto`
targets becomes a loop:

```
  { S } L invariant I decreases D
```
becomes
```
  { while(true) invariant I decreases D { { S'; exit L } $goto_start_n } } L
```
(`decreases D` stands for the block's measure in the AST. Laurel has no surface
syntax for a measure, on a block or on a `while`, so it is set only by a front
end and the pretty-printer omits it.) Here `S'` is `S` with every `goto L`
replaced by `exit $goto_start_n`. That
jump leaves the inner block and so reaches the loop's back edge; running off the
end of `S'` instead meets `exit L`, which leaves the loop, since falling off a
block's end never re-enters it. An `exit L` inside `S` leaves the loop directly.
The trailing `exit L` is omitted when `S'` already ends in a jump or `return`,
where it would be dead code. The invariants sit on the loop
head, which is exactly where a block's invariants are checked: on entry and on
every jump back to its start. Because every jump target is an *enclosing*
block, the control flow is reducible by construction and this local rewrite is
all the restructuring needed.

A labelled block that no `goto` targets is not a loop; its invariants become
`assert`s on entry and its measure, which has no iteration to decrease across,
is dropped.

The fresh label `$goto_start_{n}` uses a per-program counter; the leading `$`
keeps it out of the user-name space. A nested block reusing the label `L`
shadows it, so the replacement does not descend into one.

## Jumps to blocks that do not enclose them

A `goto` or `exit` may also name a labelled block that does not enclose it (see
`LabelledJumps`). Before the rewrite above, each region holding such a jump — the
procedure body, a `while` body or a `try` arm — is restructured so that every jump
names an enclosing block, following Ramsey's "Beyond Relooper" (ICFP 2022):

1. The region becomes a control-flow graph. Its blocks and `if`s that hold a label
   or a jump are flattened into nodes: one for each block's start and end, one for
   each `if` arm and join, and straight-line code in between. Any other statement,
   `while` and `try` included, stays whole inside a node, and a jump in it to a
   label of the region is an edge out of that node.
2. The dominator tree is computed. An edge to a node that does not dominate its
   source, but that comes no later in reverse postorder, enters a loop other than
   through its head: the flow is irreducible and the pass reports it rather than
   splitting nodes.
3. The tree is emitted top down. A loop head becomes a labelled block jumped back
   to with `goto`, carrying the invariants and measure of the block that started
   there; a node with two or more forward predecessors, or reached by a jump from
   inside a statement kept whole, becomes the code after a labelled block that the
   jumps `exit`; any other node is emitted in place at its only predecessor. A
   node the loop head dominates but that lies outside its loop follows the loop
   rather than sitting inside it, so the loop's frame covers only the loop.

Locals declared in flattened code are declared at the top of the region instead,
assigned where they were declared: the nesting puts a declaration and its uses in
different blocks. The region's own label stays as it is, since every jump to it
encloses.

The pass runs late — after `EliminateReturnStatements` and before
`LoopInvariantWellFormedness`, which needs to see the loops it creates — so
every earlier pass works on the goto form, and everything downstream, Core
included, sees only structured control flow. The traversal is the generic
bottom-up `mapProgramStmtExprM`, so inner blocks are restructured first.
-/

namespace Strata.Laurel

namespace RestructureGotos

public structure RestructureState where
  freshCounter : Nat := 0
  diags : List Message := []

public abbrev RestructureM := StateM RestructureState

private def freshStartLabel : RestructureM String :=
  modifyGet fun s => (s!"$goto_start_{s.freshCounter}", { s with freshCounter := s.freshCounter + 1 })

/-- Replace every `goto label` that targets this block by `exit startLabel`,
    without descending into a nested block that shadows `label`. Returns whether
    any jump was replaced. -/
private def redirectGotos (label startLabel : String) (stmts : List StmtExprMd) :
    List StmtExprMd × Bool :=
  let pre (e : StmtExprMd) : StateM Bool (Option StmtExprMd) :=
    match e.val with
    | .Block _ (some l) _ _ => pure (if l == label then some e else none)
    | _ => pure none
  let post (e : StmtExprMd) : StateM Bool StmtExprMd :=
    match e.val with
    | .Goto l .blockStart =>
      if l == label then do
        set true
        pure ⟨.Goto startLabel .blockEnd, e.source⟩
      else pure e
    | _ => pure e
  (stmts.mapM (mapStmtExprPrePostM pre post) |>.run false)

private def freshLabel (base : String) : RestructureM String :=
  modifyGet fun s => (s!"$goto_{base}_{s.freshCounter}", { s with freshCounter := s.freshCounter + 1 })

private def reportAt (source : FileRange) (msg : String) (kind : MessageKind := .userError) :
    RestructureM Unit :=
  modify fun s => { s with diags := s.diags ++ [diagnosticFromSource source msg kind] }

private inductive Term where
  | jump (target : Nat)
  | branch (cond : StmtExprMd) (thenTarget elseTarget : Nat)
  | stop (stmt : StmtExprMd)
  | halt
  deriving Inhabited

private structure Node where
  stmts : Array StmtExprMd := #[]
  term : Term := .halt
  label : Option String := none
  invariants : List StmtExprMd := []
  decreases : Option StmtExprMd := none
  exits : List Nat := []
  source : FileRange := .unknown
  deriving Inhabited

private structure Cfg where
  nodes : Array Node := #[]
  labels : Std.HashMap String (Nat × Nat) := {}
  regionLabels : Std.HashSet String := {}
  decls : Array StmtExprMd := #[]

private abbrev CfgM := StateM Cfg

private def newNode (source : FileRange) : CfgM Nat :=
  modifyGet fun c => (c.nodes.size, { c with nodes := c.nodes.push { source } })

private def modifyNode (n : Nat) (f : Node → Node) : CfgM Unit :=
  modify fun c => { c with nodes := c.nodes.modify n f }

private def labelNodes (l : String) (source : FileRange) : CfgM (Nat × Nat) := do
  match (← get).labels[l]? with
  | some p => pure p
  | none =>
    let st ← newNode source
    let en ← newNode source
    modify fun c => { c with labels := c.labels.insert l (st, en) }
    pure (st, en)

private def ensureNode (cur : Option Nat) (source : FileRange) : CfgM Nat := do
  match cur with
  | some n => pure n
  | none => newNode source

private def finish (cur : Option Nat) (t : Term) : CfgM Unit := do
  if let some n := cur then modifyNode n fun node => { node with term := t }

private def jumpNode (l : String) (d : GotoDestination) (source : FileRange) : CfgM Nat := do
  let (st, en) ← labelNodes l source
  pure (match d with
    | .blockStart => st
    | .blockEnd => en)

/-- The jumps in `s` to a label of the region, other than to a block nested in `s`
    that encloses them. -/
private def regionJumps (labels : Std.HashSet String) (s : StmtExprMd) : List (String × GotoDestination) :=
  (nonEnclosingJumps s).filterMap fun j => match j.val with
    | .Goto l d => if labels.contains l then some (l, d) else none
    | _ => none

private def flattens (s : StmtExprMd) : Bool :=
  (s.val matches .Block .. || s.val matches .IfThenElse ..) &&
    (!(statementLabels s).isEmpty || anyStmtExpr (·.val matches .Goto ..) s)

private def hoist (s : StmtExprMd) : CfgM StmtExprMd := do
  match s.val with
  | .Assign [⟨.Declare p, ds⟩] v =>
    modify fun c => { c with decls := c.decls.push ⟨.Var (.Declare p), ds⟩ }
    pure ⟨.Assign [⟨.Local p.name, ds⟩] v, s.source⟩
  | .Var (.Declare p) =>
    modify fun c => { c with decls := c.decls.push s }
    pure ⟨.Assign [⟨.Local p.name, s.source⟩] ⟨.Hole false p.type, s.source⟩, s.source⟩
  | .Assign targets v =>
    if !targets.any (·.val matches .Declare _) then pure s else
    let targets' ← targets.mapM fun t => match t.val with
      | .Declare p => do
        modify fun c => { c with decls := c.decls.push ⟨.Var (.Declare p), t.source⟩ }
        pure ⟨.Local p.name, t.source⟩
      | _ => pure t
    pure ⟨.Assign targets' v, s.source⟩
  | _ => pure s

private partial def flat (s : StmtExprMd) (cur : Option Nat) : CfgM (Option Nat) := do
  let labels := (← get).regionLabels
  let keepWhole : CfgM (Option Nat) := do
    let n ← ensureNode cur s.source
    let s' ← hoist s
    let targets ← (regionJumps labels s').mapM fun (l, d) => jumpNode l d s.source
    modifyNode n fun node => { node with stmts := node.stmts.push s', exits := node.exits ++ targets }
    if endsAbruptly s' then pure none else pure (some n)
  let stopWith : CfgM (Option Nat) := do
    finish (some (← ensureNode cur s.source)) (.stop s)
    pure none
  match s.val with
  | .Block stmts label invs dec =>
    if !flattens s then keepWhole else
    match label with
    | some l =>
      let (st, en) ← labelNodes l s.source
      finish cur (.jump st)
      modifyNode st fun n => { n with label := some l, invariants := invs, decreases := dec, source := s.source }
      let c ← stmts.foldlM (fun c x => flat x c) (some st)
      finish c (.jump en)
      pure (some en)
    | none => stmts.foldlM (fun c x => flat x c) cur
  | .IfThenElse c th el =>
    if !flattens s then keepWhole else
    let n ← ensureNode cur s.source
    let t ← newNode th.source
    let e ← newNode s.source
    let j ← newNode s.source
    finish (some n) (.branch c t e)
    finish (← flat th (some t)) (.jump j)
    let ce ← match el with
      | some x => flat x (some e)
      | none => pure (some e)
    finish ce (.jump j)
    pure (some j)
  | .Goto l d =>
    if labels.contains l then
      finish (some (← ensureNode cur s.source)) (.jump (← jumpNode l d s.source))
      pure none
    else stopWith
  | .Return _ | .Throw _ => stopWith
  | _ => keepWhole

private def succs (n : Node) : List Nat :=
  (match n.term with
    | .jump t => [t]
    | .branch _ t e => [t, e]
    | _ => []) ++ n.exits

private partial def postorder (nodes : Array Node) (entry : Nat) : Array Nat :=
  let rec visit (n : Nat) : StateM (Std.HashSet Nat × Array Nat) Unit := do
    if (← get).1.contains n then return
    modify fun (v, o) => (v.insert n, o)
    for m in succs nodes[n]! do visit m
    modify fun (v, o) => (v, o.push n)
  ((visit entry).run ({}, #[])).2.2

private partial def intersect (idom rpoNum : Array Nat) (a b : Nat) : Nat :=
  if a == b then a
  else if rpoNum[a]! > rpoNum[b]! then intersect idom rpoNum idom[a]! b
  else intersect idom rpoNum a idom[b]!

private def dominators (size : Nat) (rpo : Array Nat) (rpoNum : Array Nat) (preds : Array (List Nat)) :
    Array Nat := Id.run do
  let undefined := size
  let entry := rpo[0]!
  let mut idom := (Array.replicate size undefined).set! entry entry
  for _ in [0:size + 1] do
    let mut changed := false
    for b in rpo.toList.drop 1 do
      let ready := preds[b]!.filter (idom[·]! != undefined)
      match ready with
      | [] => pure ()
      | p :: ps =>
        let d := ps.foldl (fun acc q => intersect idom rpoNum q acc) p
        if idom[b]! != d then
          idom := idom.set! b d
          changed := true
    if !changed then break
  return idom

private partial def dominates (idom : Array Nat) (entry a b : Nat) : Bool :=
  if a == b then true else if b == entry then false else dominates idom entry a idom[b]!

private structure Graph where
  nodes : Array Node
  rpoNum : Array Nat
  children : Array (List Nat)
  headers : Std.HashSet Nat
  merges : Std.HashSet Nat
  labels : Std.HashMap String (Nat × Nat)
  /-- Each loop header's natural loop: the nodes that reach one of its back edges
      without passing through it, and the header. -/
  loops : Std.HashMap Nat (Std.HashSet Nat)

private abbrev Frames := List (Nat × String × Bool)

private def frameJump (g : Graph) (ctx : Frames) (x t : Nat) (source : FileRange) : RestructureM StmtExprMd := do
  let back := g.rpoNum[t]! ≤ g.rpoNum[x]!
  match ctx.find? fun (n, _, loop) => n == t && loop == back with
  | some (_, l, _) => pure ⟨.Goto l (if back then .blockStart else .blockEnd), source⟩
  | none =>
    reportAt source "RestructureGotos: a jump has no enclosing block to leave or restart" .strataBug
    pure ⟨.Goto "$unstructured" .blockEnd, source⟩

private partial def substituteJumps (f : String → GotoDestination → FileRange → RestructureM (Option StmtExprMd))
    (enclosing : List String) (e : StmtExprMd) : RestructureM StmtExprMd :=
  mapStmtExprPrePostM (fun n => match n.val with
    | .Block stmts (some l) invs dec => do
      let stmts' ← stmts.mapM (substituteJumps f (l :: enclosing))
      let invs' ← invs.mapM (substituteJumps f enclosing)
      let dec' ← dec.mapM (substituteJumps f enclosing)
      pure (some ⟨.Block stmts' (some l) invs' dec', n.source⟩)
    | .Goto l d => do
      if enclosing.contains l then pure (some n)
      else pure (some ((← f l d n.source).getD n))
    | _ => pure none) pure e

private def dropTrailingExit (label : String) (stmts : List StmtExprMd) : List StmtExprMd :=
  match stmts.getLast? with
  | some ⟨.Goto l .blockEnd, _⟩ => if l == label then stmts.dropLast else stmts
  | _ => stmts

private def jumpsTo (label : String) (stmts : List StmtExprMd) : Bool :=
  stmts.any (anyStmtExpr fun n => match n.val with
    | .Goto l _ => l == label
    | _ => false)

/-- `stmts` in a block labelled `label`, or bare when no jump leaves it. -/
private def wrapExited (label : String) (stmts : List StmtExprMd) (source : FileRange) : List StmtExprMd :=
  let stmts := dropTrailingExit label stmts
  if jumpsTo label stmts then [⟨.Block stmts (some label) [] none, source⟩] else stmts

mutual

private partial def doTree (g : Graph) (x : Nat) (ctx : Frames) : RestructureM (List StmtExprMd) := do
  let node := g.nodes[x]!
  let kids := ((g.children[x]!.filter g.merges.contains).toArray.qsort
    (fun a b => g.rpoNum[a]! > g.rpoNum[b]!)).toList
  if g.headers.contains x then
    let label ← match node.label with
      | some l => pure l
      | none => freshLabel "loop"
    let inLoop := (g.loops.getD x {}).contains
    let rec afterLoop : List Nat → Frames → RestructureM (List StmtExprMd)
      | y :: rest, ctx => do
        let l ← freshLabel "join"
        let inner ← afterLoop rest ((y, l, false) :: ctx)
        pure (wrapExited l inner node.source ++ (← doTree g y ctx))
      | [], ctx => do
        let body ← nodeWithin g x (kids.filter inLoop) ((x, label, true) :: ctx)
        pure [⟨.Block body (some label) node.invariants node.decreases, node.source⟩]
    afterLoop (kids.filter (!inLoop ·)) ctx
  else
    let asserts := node.invariants.map fun inv => (⟨.Assert inv none, inv.source⟩ : StmtExprMd)
    pure (asserts ++ (← nodeWithin g x kids ctx))

private partial def nodeWithin (g : Graph) (x : Nat) (merges : List Nat) (ctx : Frames) :
    RestructureM (List StmtExprMd) := do
  let node := g.nodes[x]!
  match merges with
  | y :: rest =>
    let label ← freshLabel "join"
    let inner ← nodeWithin g x rest ((y, label, false) :: ctx)
    pure (wrapExited label inner node.source ++ (← doTree g y ctx))
  | [] =>
    let jumpOut (l : String) (d : GotoDestination) (source : FileRange) : RestructureM (Option StmtExprMd) := do
      match g.labels[l]? with
      | some (st, en) => some <$> frameJump g ctx x (match d with | .blockStart => st | .blockEnd => en) source
      | none => pure none
    let stmts ← node.stmts.toList.mapM (substituteJumps jumpOut [])
    let term ← match node.term with
      | .jump t => branchTo g x t ctx node.source
      | .branch c t e => do
        let th ← branchTo g x t ctx c.source
        let el ← branchTo g x e ctx c.source
        pure [⟨.IfThenElse c ⟨.Block th none [] none, c.source⟩ (some ⟨.Block el none [] none, c.source⟩),
          node.source⟩]
      | .stop s => pure [s]
      | .halt => pure []
    pure (stmts ++ term)

private partial def branchTo (g : Graph) (x t : Nat) (ctx : Frames) (source : FileRange) :
    RestructureM (List StmtExprMd) := do
  if g.rpoNum[t]! ≤ g.rpoNum[x]! || g.merges.contains t then pure [← frameJump g ctx x t source]
  else doTree g t ctx

end

private def renameLocal (old new : String) (e : StmtExprMd) : StmtExprMd :=
  let target (v : VariableMd) : VariableMd := match v.val with
    | .Local x => if x.text == old then ⟨.Local { x with text := new }, v.source⟩ else v
    | .Declare p => if p.name.text == old then ⟨.Declare { p with name := { p.name with text := new } }, v.source⟩ else v
    | _ => v
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local x) => if x.text == old then ⟨.Var (.Local { x with text := new }), n.source⟩ else n
    | .Var (.Declare p) =>
      if p.name.text == old then ⟨.Var (.Declare { p with name := { p.name with text := new } }), n.source⟩ else n
    | .Assign targets v => ⟨.Assign (targets.map target) v, n.source⟩
    | _ => n) e

mutual

/-- Give the declarations that flattening will hoist distinct names: two blocks of
    the region may declare the same name, each in its own scope, and the hoisted
    declarations share one. A later declaration is renamed together with the
    statements after it in its scope. Declarations inside a statement kept whole
    are renamed the same way when a hoisted one has their name, since they would
    then lie in its scope. -/
private partial def uniquifyDecls (seen : Std.HashSet String) (stmts : List StmtExprMd) :
    RestructureM (List StmtExprMd × Std.HashSet String) := do
  match stmts with
  | [] => pure ([], seen)
  | s :: rest =>
    match statementDecls s with
    | names@(_ :: _) =>
      let mut stmt := s
      let mut after := rest
      let mut taken := seen
      for n in names do
        if taken.contains n then
          let n' ← freshLabel n
          stmt := renameLocal n n' stmt
          after := after.map (renameLocal n n')
          taken := taken.insert n'
        else
          taken := taken.insert n
      let (s', taken') ← uniquifyKept taken stmt
      let (rest', seen') ← uniquifyDecls taken' after
      pure (s' :: rest', seen')
    | [] =>
      let (s', seen) ← if !flattens s then uniquifyKept seen s else match s.val with
        | .Block ss label invs dec => do
          let (ss', seen) ← uniquifyDecls seen ss
          pure (⟨.Block ss' label invs dec, s.source⟩, seen)
        | .IfThenElse c th el => do
          let (th', seen) ← uniquifyDecls seen [th]
          let (el', seen) ← match el with
            | some x => do
              let (x', seen) ← uniquifyDecls seen [x]
              pure (x'.head?, seen)
            | none => pure (none, seen)
          pure (⟨.IfThenElse c (th'.head?.getD th) el', s.source⟩, seen)
        | _ => pure (s, seen)
      let (rest', seen) ← uniquifyDecls seen rest
      pure (s' :: rest', seen)

/-- `uniquifyDecls` through the blocks of a statement that is kept whole, including
    blocks used as values. -/
private partial def uniquifyKept (seen : Std.HashSet String) (s : StmtExprMd) :
    RestructureM (StmtExprMd × Std.HashSet String) := do
  match s.val with
  | .Block ss label invs dec => do
    let (ss', seen) ← uniquifyDecls seen ss
    pure (⟨.Block ss' label invs dec, s.source⟩, seen)
  | .IfThenElse c th el => do
    let (th', seen) ← uniquifyKept seen th
    let (el', seen) ← match el with
      | some x => do
        let (x', seen) ← uniquifyKept seen x
        pure (some x', seen)
      | none => pure (none, seen)
    pure (⟨.IfThenElse c th' el', s.source⟩, seen)
  | .While c invs dec b post => do
    let (b', seen) ← uniquifyKept seen b
    pure (⟨.While c invs dec b' post, s.source⟩, seen)
  | .Try b catches fin => do
    let (b', seen0) ← uniquifyKept seen b
    let mut acc := seen0
    let mut catches' := []
    for c in catches do
      let (cb, next) ← uniquifyKept acc c.body
      acc := next
      catches' := catches' ++ [{ c with body := cb }]
    let (fin', final) ← match fin with
      | some f => do
        let (f', next) ← uniquifyKept acc f
        pure (some f', next)
      | none => pure (none, acc)
    pure (⟨.Try b' catches' fin', s.source⟩, final)
  | _ =>
    (mapStmtExprPrePostM (m := StateT (Std.HashSet String) RestructureM) (fun n => match n.val with
      | .Block ss label invs dec => do
        let (ss', seen') ← uniquifyDecls (← get) ss
        set seen'
        pure (some ⟨.Block ss' label invs dec, n.source⟩)
      | _ => pure none) pure s).run seen

end

/-- Nest the blocks of the region `stmts` so that every jump in it leaves or
    restarts an enclosing block. `none` when the flow is irreducible, which is
    reported. -/
private def structureStmts (stmts : List StmtExprMd) (labels : Std.HashSet String) (source : FileRange) :
    RestructureM (Option (List StmtExprMd)) := do
  let endLabel ← freshLabel "end"
  let build : CfgM (Nat × Nat) := do
    let entry ← newNode source
    let last ← stmts.foldlM (fun c x => flat x c) (some entry)
    let exit ← newNode source
    finish (some exit) (.stop ⟨.Goto endLabel .blockEnd, source⟩)
    finish last (.jump exit)
    pure (entry, exit)
  let ((entry, _), cfg) := build.run { regionLabels := labels }
  let nodes := cfg.nodes
  let size := nodes.size
  let rpo := (postorder nodes entry).reverse
  let rpoNum := rpo.zipIdx.foldl (fun acc (n, i) => acc.set! n i) (Array.replicate size size)
  let reachable (n : Nat) : Bool := rpoNum[n]! < size
  let edges : List (Nat × Nat) := rpo.toList.flatMap fun u => (succs nodes[u]!).map (u, ·)
  let preds := edges.foldl (fun acc (u, v) => acc.modify v (u :: ·)) (Array.replicate size [])
  let idom := dominators size rpo rpoNum preds
  let retreating := edges.filter fun (u, v) => rpoNum[v]! ≤ rpoNum[u]!
  if let some (_, v) := retreating.find? fun (u, v) => !dominates idom entry v u then
    let name := (cfg.labels.toList.find? fun (_, (st, en)) => st == v || en == v).map (·.1)
    let place := match name with
      | some l => s!" at '{l}'"
      | none => ""
    reportAt nodes[v]!.source s!"the jumps in this block form a loop that is entered other than through its first statement{place}; irreducible control flow cannot be restructured"
    return none
  let headers : Std.HashSet Nat := retreating.foldl (fun s (_, v) => s.insert v) {}
  let loops : Std.HashMap Nat (Std.HashSet Nat) := retreating.foldl (init := {}) fun acc (u, h) =>
    let rec grow (fuel : Nat) (work : List Nat) (seen : Std.HashSet Nat) : Std.HashSet Nat :=
      match fuel, work with
      | 0, _ | _, [] => seen
      | fuel + 1, w :: rest =>
        if seen.contains w then grow fuel rest seen
        else grow fuel (preds[w]! ++ rest) (seen.insert w)
    acc.insert h (grow (size * size + 1) [u] ((acc.getD h {}).insert h))
  let forward := edges.filter fun (u, v) => rpoNum[v]! > rpoNum[u]!
  let inDegree := forward.foldl (fun acc (_, v) => acc.modify v (· + 1)) (Array.replicate size 0)
  let forced := rpo.toList.flatMap fun u => nodes[u]!.exits.filter fun v => rpoNum[v]! > rpoNum[u]!
  let merges : Std.HashSet Nat := (rpo.toList.filter fun n => inDegree[n]! ≥ 2).foldl (·.insert ·)
    (forced.foldl (·.insert ·) {})
  let exitedLoop (n : Nat) : Option Nat :=
    headers.toList.foldl (init := none) fun best h =>
      let body := loops.getD h {}
      if body.contains idom[n]! && !body.contains n then
        match best with
        | some b => if rpoNum[b]! ≤ rpoNum[h]! then some b else some h
        | none => some h
      else best
  let children := (rpo.toList.drop 1).foldl (fun acc n => acc.modify ((exitedLoop n).getD idom[n]!) (· ++ [n]))
    (Array.replicate size [])
  let exits := headers.toList.flatMap fun h =>
    children[h]!.filter fun c => !((loops.getD h {}).contains c)
  let merges := exits.foldl (·.insert ·) merges
  let _ := reachable
  let g : Graph := { nodes, rpoNum, children, headers, merges, labels := cfg.labels, loops }
  let code ← doTree g entry []
  return some (cfg.decls.toList ++ wrapExited endLabel code source)

/-- Restructure the region `root`, the body of a procedure, of a `while` or of a
    `try` arm, when a jump in it names a block of it that does not enclose the
    jump. The root's own label and invariants stay on it. -/
private def structureRegion (root : StmtExprMd) : RestructureM StmtExprMd := do
  let (stmts, label, invs, dec) := match root.val with
    | .Block stmts label invs dec => (stmts, label, invs, dec)
    | _ => ([root], none, [], none)
  let labelList := stmts.flatMap statementLabels
  let labels : Std.HashSet String := labelList.foldl (·.insert ·) {}
  let targets := nonEnclosingTargets ⟨.Block stmts none [] none, root.source⟩
  if !(labelList.any targets.contains) then return root
  if labels.size != labelList.length then
    reportAt root.source "RestructureGotos: a label names more than one block of a region with non-enclosing jumps" .strataBug
    return root
  let (stmts, _) ← uniquifyDecls {} stmts
  match ← structureStmts stmts labels root.source with
  | some stmts' => pure ⟨.Block stmts' label invs dec, root.source⟩
  | none => pure root

/-- The labels some jump in `e` names. -/
private def jumpLabels (e : StmtExprMd) : Std.HashSet String :=
  (collectStmtExprList (fun n => match n.val with
    | .Goto l _ => [l]
    | _ => []) e).foldl (·.insert ·) {}

/-- `stmts` without the labelled blocks that follow a statement ending abruptly and
    of whose labels, their own and those nested in them, no jump names one: nothing
    can reach them. -/
private partial def dropDeadBlocks (exited targets : Std.HashSet String) : List StmtExprMd → List StmtExprMd
  | [] => []
  | s :: rest =>
    let rest := if endsAbruptlyIn exited s then
        rest.dropWhile fun t => match t.val with
          | .Block _ (some _) _ _ => !((statementLabels t).any targets.contains)
          | _ => false
      else rest
    s :: dropDeadBlocks exited targets rest

private def labelledBlockCount (e : StmtExprMd) : Nat :=
  (collectStmtExprList (fun n => match n.val with
    | .Block _ (some _) _ _ => [()]
    | _ => []) e).length

/-- The locals `e` reads or assigns. -/
private def mentionedLocals (e : StmtExprMd) : Std.HashSet String :=
  (collectStmtExprList (fun n => match n.val with
    | .Var (.Local x) => [x.text]
    | .Assign targets _ => targets.filterMap fun t => match t.val with
      | .Local x => some x.text
      | _ => none
    | _ => []) e).foldl (·.insert ·) {}

/-- Drop the code no jump reaches any more and then the declarations of `Unknown`-typed
    locals that nothing mentions. `EliminateExceptions` drops a catch clause that can
    never fire, which leaves the blocks only that clause jumped to unreachable, and the
    locals typed after its binding without a type Core can translate. -/
private partial def dropDeadCode (body : StmtExprMd) : StmtExprMd :=
  let targets := jumpLabels body
  let exited := exitedLabels body
  let body' := mapStmtExpr (fun n => match n.val with
    | .Block ss l invs dec => ⟨.Block (dropDeadBlocks exited targets ss) l invs dec, n.source⟩
    | _ => n) body
  if labelledBlockCount body' < labelledBlockCount body then dropDeadCode body' else
  let used := mentionedLocals body'
  mapStmtExpr (fun n => match n.val with
    | .Block ss l invs dec => ⟨.Block (ss.filter fun s => match s.val with
        | .Var (.Declare ⟨x, some ⟨.Unknown, _⟩⟩) => used.contains x.text
        | _ => true) l invs dec, n.source⟩
    | _ => n) body'

/-- Restructure every region of a procedure body that holds a jump to a block not
    enclosing it, innermost first, once the code no jump reaches is gone. -/
public def structureBody (body : StmtExprMd) : RestructureM StmtExprMd := do
  let body := dropDeadCode body
  if !hasNonEnclosingJump body then return body
  let body' ← mapStmtExprM (fun n => match n.val with
    | .While c invs dec b postTest => do pure ⟨.While c invs dec (← structureRegion b) postTest, n.source⟩
    | .Try b catches fin => do
      let catches' ← catches.mapM fun c => do pure { c with body := ← structureRegion c.body }
      pure ⟨.Try (← structureRegion b) catches' (← fin.mapM structureRegion), n.source⟩
    | _ => pure n) body
  structureRegion body'

/-- Lowers one labelled block carrying a backward `goto` or invariants; all other
    nodes pass through. -/
public def rewriteNode (node : StmtExprMd) : RestructureM StmtExprMd := do
  match node.val with
  | .Block stmts (some label) invs dec =>
    let source := node.source
    let startLabel ← freshStartLabel
    let (stmts', jumpsBack) := redirectGotos label startLabel stmts
    if jumpsBack then
      let endsInJump := (stmts'.getLast?.map endsAbruptly).getD false
      let leave : List StmtExprMd := if endsInJump then [] else [⟨.Goto label .blockEnd, source⟩]
      let body : StmtExprMd := ⟨.Block (stmts' ++ leave) (some startLabel) [] none, source⟩
      let loop : StmtExprMd := ⟨.While ⟨.LiteralBool true, source⟩ invs dec body false, source⟩
      pure ⟨.Block [loop] (some label) [] none, source⟩
    else if invs.isEmpty && dec.isNone then
      pure node
    else
      let asserts := invs.map fun inv => (⟨.Assert inv none, inv.source⟩ : StmtExprMd)
      pure ⟨.Block (asserts ++ [⟨.Block stmts (some label) [] none, source⟩]) none [] none, source⟩
  | _ => pure node

end RestructureGotos

public section

/-- Nest the blocks of every region with a jump to a block that does not enclose
    it, then lower every backward `goto` and every block invariant; afterwards every
    `Goto` is a forward `exit` and no block carries invariants or a measure. -/
def restructureGotos (program : Program) : Program × List Message :=
  let run : RestructureGotos.RestructureM Program := do
    let p ← mapProgramProceduresM (mapProcedureBodiesM RestructureGotos.structureBody) program
    mapProgramStmtExprM RestructureGotos.rewriteNode p
  let (p, st) := run.run {}
  (p, st.diags)

/-- Pipeline pass: turn blocks that are the targets of backward jumps into loops. -/
public def restructureGotosPass : LaurelPass where
  name := "RestructureGotos"
  creates := [
      NodeKind.StmtExpr.While,
      NodeKind.StmtExpr.Block,
      NodeKind.StmtExpr.Goto,
      NodeKind.StmtExpr.LiteralBool,
      NodeKind.StmtExpr.Assert
    ]
  removes := [
      NodeKind.StmtExpr.Goto.destination.blockStart,
      NodeKind.StmtExpr.Block.invariants.cons,
      NodeKind.StmtExpr.Block.decreases.some
    ]
  documentation := "Drops the labelled blocks no jump reaches and the declarations of `Unknown`-typed locals left unused. Nests the labelled blocks of a region in which a jump names a block that does not enclose it, so that every jump leaves or restarts an enclosing block, and refuses irreducible control flow. Then lowers a labelled block that some `goto` jumps back into to `{ while(true) invariant I decreases D { { S'; exit L } $goto_start_n } } L`, where `S'` redirects each `goto L` to `exit $goto_start_n`. A labelled block with invariants but no backward jump asserts them on entry instead. Afterwards Core sees only structured control flow: forward exits and `while` loops."
  run := fun _ p _m => let (p', diags) := restructureGotos p; (p', diags, {})

end -- public section
end Strata.Laurel
