/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.StackShape
public import StrataLaurel.Implementation.HeapAnalysis
import StrataLaurel.Implementation.MapStmtExpr

namespace Strata.Laurel

public section

private def writesNonLocal (globals : List String) (v : VariableMd) : Bool :=
  match v.val with
  | .Field .. => true
  | .Local name => globals.contains name.text
  | .Declare _ | .Stack _ => false

private def impureNode (globals : List String) (e : StmtExprMd) : Bool :=
  match e.val with
  | .Assert .. | .Assume _ | .New .. | .Call (some _) .. | .Hole .. | .While ..
  | .Throw _ | .Try .. | .Yield | .Resume .. | .HasNext _ | .Snapshot _ => true
  | .Assign targets _ => targets.any (writesNonLocal globals)
  | .IncrDecr _ _ target | .CompoundAssign _ target _ => writesNonLocal globals target
  | _ => false

private def calleesOf (e : StmtExprMd) : List String :=
  collectStmtExprList (fun n => match n.val with
    | .Call none callee _ _ => [callee.text]
    | _ => []) e

private def pureCallees (procs : List Procedure) (globals composites : List String) :
    Std.HashSet String := Id.run do
  let isCompositeType (t : HighTypeMd) : Bool :=
    match t.val with
    | .UserDefined name => composites.contains name.text
    | _ => false
  let isComposite (param : Parameter) : Bool :=
    match param.type.val with
    | .Applied base _ => isCompositeType base
    | _ => isCompositeType param.type
  let locallyPure (p : Procedure) : Bool :=
    p.preconditions.isEmpty && p.throwsType.isNone && !p.isInterpretEntry
      && !(p.inputs ++ p.outputs).any isComposite
      && p.invokeOn.isNone && p.axioms.isEmpty
      && (match p.contracts with | .Regular => true | _ => false)
      && match p.body with
        | .External => true
        | .Transparent b => !anyStmtExpr (impureNode globals) b
        | _ => false
  let bodyCallees (p : Procedure) : List String :=
    match p.body with
    | .Transparent b => calleesOf b
    | _ => []
  let procNames : Std.HashSet String := procs.foldl (·.insert ·.name.text) {}
  let mut impure : Std.HashSet String :=
    procs.foldl (fun s p => if locallyPure p then s else s.insert p.name.text) {}
  for _ in procs do
    let next := procs.foldl (fun s p =>
      if (bodyCallees p).any (fun c => procNames.contains c && s.contains c)
      then s.insert p.name.text else s) impure
    if next.size == impure.size then break
    impure := next
  return procNames.filter (!impure.contains ·)

private def LaurelProgram.pureCallee (p : LaurelProgram) : String → Bool :=
  let procs := p.staticProcedures ++ p.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  let composites := p.types.filterMap fun
    | .Composite ct => some ct.name.text
    | _ => none
  let pure := pureCallees procs (p.staticFields.map (·.name.text)) composites
  let procNames : Std.HashSet String := procs.foldl (·.insert ·.name.text) {}
  fun c => c != "$quantifierBody" && (pure.contains c || !procNames.contains c)

private structure StackState where
  stack : List (Identifier × Option HighTypeMd) := []
  counter : Nat := 0
  diags : List Message := []
  shared : List String := []
  readTypes : List (String × HighTypeMd) := []
  witnesses : List (String × StmtExprMd) := []
  oldNames : List String := []
  wrapOld : StmtExprMd → Bool := fun _ => true
  heapWriters : Option (Std.HashSet Nat) := none
  pure : String → Bool := fun _ => true
  globals : Std.HashSet String := {}
  openLabels : List String := []
  exits : List (String × Nat × List (Identifier × Option HighTypeMd)) := []

private abbrev StackM := StateM StackState

private def report (source : FileRange) (msg : String) : StackM Unit :=
  modify fun s => { s with diags := s.diags ++ [diagnosticFromSource source msg] }

private def fresh : StackM Identifier := do
  let s ← get
  set { s with counter := s.counter + 1 }
  pure (mkId s!"$stack_{s.counter}")

private def substReads (e : StmtExprMd) (names : List Identifier) :
    StmtExprMd × List (String × HighTypeMd) :=
  let step (n : StmtExprMd) : StateM (List Identifier × List (String × HighTypeMd)) StmtExprMd := do
    match n.val, (← get) with
    | .Var (.Stack t), (name :: rest, typed) =>
      set (rest, (t.map fun ty => (name.text, ty)).toList ++ typed)
      pure ⟨.Var (.Local name), n.source⟩
    | _, _ => pure n
  let (e', _, typed) := (mapStmtExprM step e).run (names, [])
  (e', typed)

private def localNames (e : StmtExprMd) : List String :=
  ((foldStmtExprM (m := StateM (List String)) (fun n => do
    if let .Var (.Local name) := n.val then modify (name.text :: ·)) e).run []).2

private def stripOld (e : StmtExprMd) (names : List String) : StmtExprMd × List String :=
  let step (n : StmtExprMd) : StateM (List String) StmtExprMd := do
    match n.val with
    | .Old inner none =>
      let read := (localNames inner).filter names.contains
      modify (read ++ ·)
      match inner.val with
      | .Var (.Local name) => if names.contains name.text then pure inner else pure n
      | _ => pure n
    | _ => pure n
  (mapStmtExprM step e).run []

private def popReads (e : StmtExprMd) : StackM StmtExprMd := do
  let n := countStackReads e
  if n == 0 then return e
  let s ← get
  if s.stack.length < n then
    report e.source "this reads more stack values than were pushed"
    return e
  let names := (s.stack.take n).reverse.map (·.1)
  let (e', typed) := substReads e names
  let (e', olds) := stripOld e' (names.map (·.text))
  set { s with stack := s.stack.drop n, oldNames := olds ++ s.oldNames,
               readTypes := typed.filter (fun (p : String × HighTypeMd) => s.shared.contains p.1) ++ s.readTypes }
  pure e'

private def endsWith (base whole : List (Identifier × Option HighTypeMd)) : Bool :=
  base.length ≤ whole.length &&
    ((whole.drop (whole.length - base.length)).map (·.1.text)) == base.map (·.1.text)

private def wrapBlock (stmts : List StmtExprMd) (source : FileRange) : StmtExprMd :=
  match stmts with
  | [single] => single
  | _ => ⟨.Block stmts none [] none, source⟩

private def defaultValue (witnesses : List (String × StmtExprMd)) (t : HighTypeMd) (source : FileRange) :
    Option StmtExprMd :=
  match t.val with
  | .UserDefined r => (witnesses.find? (·.1 == r.text)).map (·.2)
  | .TBool => some ⟨.LiteralBool false, source⟩
  | .TInt => some ⟨.LiteralInt 0, source⟩
  | .TString => some ⟨.LiteralString "", source⟩
  | _ => none

private def exitsTo (label : String) (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with
    | .Goto l .blockEnd => l == label
    | _ => false) e

private def contMark (source : FileRange) : StmtExprMd := ⟨.Goto "$cont" .blockEnd, source⟩

private def isContMark (e : StmtExprMd) : Bool := e.val matches .Goto "$cont" .blockEnd

private def armStmts (b : StmtExprMd) : List StmtExprMd :=
  match b.val with
  | .Block ss none [] none => ss
  | _ => [b]

private def armBlock (ss : List StmtExprMd) (source : FileRange) : StmtExprMd :=
  ⟨.Block ss none [] none, source⟩

private partial def contCount (e : StmtExprMd) : Nat :=
  if isContMark e then 1 else match e.val with
    | .Block ss none [] none => ss.foldl (· + contCount ·) 0
    | .IfThenElse _ th el => contCount th + (el.map contCount).getD 0
    | _ => 0

private partial def spliceCont (r : List StmtExprMd) (e : StmtExprMd) : List StmtExprMd :=
  if isContMark e then r else match e.val with
    | .Block ss none [] none => [armBlock (ss.flatMap (spliceCont r)) e.source]
    | .IfThenElse c th el =>
      [⟨.IfThenElse c (armBlock ((armStmts th).flatMap (spliceCont r)) th.source)
        (el.map fun x => armBlock ((armStmts x).flatMap (spliceCont r)) x.source), e.source⟩]
    | _ => [e]

private def literalStackAssign (s : StmtExprMd) : Bool :=
  let literal (v : StmtExprMd) : Bool := v.val matches .LiteralBool _ | .LiteralInt _
  match s.val with
  | .Assign [⟨.Stack _, _⟩] v => literal v
  | .Assign [⟨.Local name, _⟩] v => name.text.startsWith "$stack_" && literal v
  | _ => false

private partial def negOf (c : StmtExprMd) (source : FileRange) : StmtExprMd :=
  match c.val with
  | .Call none op [inner] _ => if op.text == Operation.Not.procName then inner else notMd source c
  | .Call none op [a, b] _ =>
    if op.text == Operation.AndThen.procName then ⟨.Call none (mkId Operation.OrElse.procName) [negOf a source, negOf b source] [], source⟩
    else if op.text == Operation.OrElse.procName then ⟨.Call none (mkId Operation.AndThen.procName) [negOf a source, negOf b source] [], source⟩
    else notMd source c
  | _ => notMd source c

private def boolIte (c x y : StmtExprMd) (source : FileRange) : StmtExprMd :=
  let andThen (a b : StmtExprMd) : StmtExprMd := ⟨.Call none (mkId Operation.AndThen.procName) [a, b] [], source⟩
  let orElse (a b : StmtExprMd) : StmtExprMd := ⟨.Call none (mkId Operation.OrElse.procName) [a, b] [], source⟩
  match x.val, y.val with
  | .LiteralBool true, .LiteralBool false => c
  | .LiteralBool false, .LiteralBool true => negOf c source
  | _, .LiteralBool false => andThen c x
  | .LiteralBool true, _ => orElse c y
  | .LiteralBool false, _ => andThen (negOf c source) y
  | _, .LiteralBool true => orElse (negOf c source) x
  | _, _ => ⟨.IfThenElse c x (some y), source⟩

private inductive ArmShape where
  | leaf (stmts : List StmtExprMd)
  | cont
  | ite (c : StmtExprMd) (th el : ArmShape)

private def leafShape? (ss : List StmtExprMd) : Option ArmShape :=
  match ss.getLast? with
  | some last =>
    if (last.val matches .Goto _ .blockEnd) && ss.dropLast.all literalStackAssign then some (.leaf ss) else none
  | none => none

private partial def armShape? (ss : List StmtExprMd) : Option ArmShape :=
  match ss with
  | [] => some (.leaf [])
  | [s] =>
    if isContMark s then some .cont else
    match s.val with
    | .IfThenElse c th (some el) => do
      let t ← armShape? (armStmts th)
      let e ← armShape? (armStmts el)
      pure (.ite c t e)
    | _ => leafShape? ss
  | _ => leafShape? ss

private def ArmShape.leaves : ArmShape → List (List StmtExprMd)
  | .leaf ss => [ss]
  | .cont => []
  | .ite _ th el => th.leaves ++ el.leaves

private def ArmShape.conds : ArmShape → List StmtExprMd
  | .ite c th el => c :: (th.conds ++ el.conds)
  | _ => []

private def ArmShape.pred (source : FileRange) : ArmShape → StmtExprMd
  | .leaf _ => ⟨.LiteralBool true, source⟩
  | .cont => ⟨.LiteralBool false, source⟩
  | .ite c th el => boolIte c (th.pred source) (el.pred source) source

private def callLike (pure : String → Bool) (e : StmtExprMd) : Bool :=
  !pure "$quantifierBody" && anyStmtExpr (fun n => match n.val with
    | .Call none callee _ _ => !(callee.text.startsWith "$" && pure callee.text)
    | .Assign [⟨.Declare _, _⟩] _ => false
    | .Block _ none [] none => false
    | .Call (some _) .. | .New .. | .Assign .. | .IncrDecr .. | .CompoundAssign .. | .Quantifier ..
    | .AsType .. | .Hole .. | .Assert .. | .Assume .. | .Block .. | .Return .. | .Throw .. => true
    | _ => false) e

private def leafKey (ss : List StmtExprMd) : String :=
  String.intercalate ";" (ss.map fun s => match s.val with
    | .Assign [_] v => reprStr v.val
    | _ => reprStr s.val)

private def combineArms (isPure : String → Bool) (source : FileRange) (c : StmtExprMd)
    (th el r : List StmtExprMd) : Option (List StmtExprMd) :=
  match armShape? th, armShape? el with
  | some t, some e =>
    let sh := ArmShape.ite c t e
    match sh.leaves with
    | first :: others =>
      if others.all (fun l => leafKey l == leafKey first) && sh.conds.all (fun x => !callLike isPure x) then
        some [⟨.IfThenElse (sh.pred source) (armBlock first source) (some (armBlock r source)), source⟩]
      else none
    | [] => none
  | _, _ => none

private partial def unexit (isPure : String → Bool) (label : String) (source : FileRange) :
    List StmtExprMd → List StmtExprMd → Option (List StmtExprMd)
  | [], cont => some cont
  | s :: rest, cont =>
    if !exitsTo label s then (unexit isPure label source rest cont).map (s :: ·)
    else match s.val with
      | .Goto _ .blockEnd => some []
      | .Block ss none [] none => unexit isPure label source (ss ++ rest) cont
      | .IfThenElse c th el => do
        let r ← unexit isPure label source rest cont
        let th' ← unexit isPure label source (armStmts th) [contMark s.source]
        let el' ← unexit isPure label source ((el.map armStmts).getD []) [contMark s.source]
        let ite : StmtExprMd := ⟨.IfThenElse c (armBlock th' th.source) (some (armBlock el' s.source)), s.source⟩
        if r.isEmpty || contCount ite ≤ 1 || r.all (fun x => isContMark x || literalStackAssign x) then some (spliceCont r ite)
        else combineArms isPure s.source c th' el' r
      | _ => none

private def structureExits (isPure : String → Bool) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Block stmts (some label) [] none =>
      if stmts.any (exitsTo label) && !(stmts.any (anyStmtExpr fun x => match x.val with
          | .Goto l .blockStart => l == label
          | _ => false)) then
        match unexit isPure label n.source stmts [] with
        | some ss => armBlock ss n.source
        | none => n
      else n
    | _ => n) e

private def exitMarker (id : Nat) (goto : StmtExprMd) : StmtExprMd :=
  ⟨.Block [goto] none [⟨.LiteralInt id, goto.source⟩] none, goto.source⟩

private def placeExitCopies (copies : List (Nat × List StmtExprMd)) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Block [goto] none [⟨.LiteralInt id, _⟩] none =>
      match copies.find? (·.1 == id) with
      | some (_, []) => goto
      | some (_, cs) => ⟨.Block (cs ++ [goto]) none [] none, n.source⟩
      | none => n
    | _ => n) e

private def isLoop (label : String) (stmts : List StmtExprMd) : Bool :=
  stmts.any (anyStmtExpr fun n => match n.val with
    | .Goto l .blockStart => l == label
    | _ => false)

mutual

private partial def elimStmts (stmts : List StmtExprMd) : StackM (List StmtExprMd) :=
  stmts.flatMapM elimStmt

private partial def elimBranch (branch : StmtExprMd) : StackM StmtExprMd := do
  match branch.val with
  | .Block stmts none [] none => pure ⟨.Block (← elimStmts stmts) none [] none, branch.source⟩
  | _ => pure (wrapBlock (← elimStmt branch) branch.source)

private partial def appendCopies (branch : StmtExprMd) (copies : List StmtExprMd) : StmtExprMd :=
  if copies.isEmpty then branch else
  match branch.val with
  | .Block stmts none [] none => ⟨.Block (stmts ++ copies) none [] none, branch.source⟩
  | _ => ⟨.Block (branch :: copies) none [] none, branch.source⟩

private partial def mergeFinals (source : FileRange) (base : List (Identifier × Option HighTypeMd))
    (finals : List (List (Identifier × Option HighTypeMd))) :
    StackM (List StmtExprMd × List (List StmtExprMd)) := do
  let unchanged := finals.map fun _ => ([] : List StmtExprMd)
  if finals.isEmpty then
    set { (← get) with stack := [] }
    return ([], unchanged)
  let consumed := finals.map fun final =>
    ((List.range (base.length + 1)).find? fun c => endsWith (base.drop c) final).getD base.length
  let c := (consumed.head?).getD 0
  if !consumed.all (· == c) then
    report source "the branches consume different numbers of the stack values pushed before them"
    set { (← get) with stack := base }
    return ([], unchanged)
  let kept := base.drop c
  let nets := finals.map fun final => final.take (final.length - kept.length)
  let k := (nets.head?.map List.length).getD 0
  if !nets.all (·.length == k) then
    report source "the branches leave different numbers of values on the stack"
    set { (← get) with stack := base }
    return ([], unchanged)
  if k == 0 then
    set { (← get) with stack := kept }
    return ([], unchanged)
  let mut shared : List (Identifier × Option HighTypeMd) := []
  let mut decls : List StmtExprMd := []
  for i in List.range k do
    let ty := nets.findSome? fun net => (net[i]?).bind (·.2)
    let name ← fresh
    modify fun st => { st with shared := name.text :: st.shared }
    match ty with
    | some t =>
      let declared : StmtExprMd := match defaultValue (← get).witnesses t source with
        | some init => ⟨.Assign [⟨.Declare ⟨name, some t⟩, source⟩] init, source⟩
        | none => ⟨.Var (.Declare ⟨name, some t⟩), source⟩
      decls := decls ++ [declared]
    | none => report source "a value pushed in both branches needs a type on its push"
    shared := shared ++ [(name, ty)]
  let copies := nets.map fun net => (shared.zip net).map fun ((j, _), (n, _)) =>
    (⟨.Assign [⟨.Local j, source⟩] ⟨.Var (.Local n), source⟩, source⟩ : StmtExprMd)
  set { (← get) with stack := shared ++ kept }
  return (decls, copies)

private partial def mergeArms (source : FileRange) (base : List (Identifier × Option HighTypeMd))
    (arms : List (StmtExprMd × List (Identifier × Option HighTypeMd))) :
    StackM (List StmtExprMd × List StmtExprMd) := do
  let live := arms.filter fun (arm, _) => !endsAbruptly arm
  let (decls, copies) ← mergeFinals source base (live.map (·.2))
  let (arms', _) := arms.foldl (init := ([], copies)) fun (acc, cs) (arm, _) =>
    if endsAbruptly arm then (acc ++ [arm], cs)
    else (acc ++ [appendCopies arm (cs.head?.getD [])], cs.drop 1)
  return (decls, arms')

private partial def elimIsolated (body : StmtExprMd) (what : String) : StackM StmtExprMd := do
  let outer := (← get).stack
  set { (← get) with stack := [] }
  let body' ← elimBranch body
  unless (← get).stack.isEmpty do
    report body.source s!"stack values are left over at the end of {what}"
  set { (← get) with stack := outer }
  pure body'

private partial def elimRoot (e : StmtExprMd) : StackM StmtExprMd :=
  elimIsolated e "an expression"

private partial def elimQuantifierBodies (e : StmtExprMd) : StackM StmtExprMd :=
  mapStmtExprM (fun n => match n.val with
    | .Quantifier mode param trig body =>
      if anyStmtExpr nodeTouchesStack body then do
        let body' ← elimIsolated body "a quantifier body"
        pure ⟨.Quantifier mode param trig body', n.source⟩
      else pure n
    | _ => pure n) e

private partial def permuteStack (s v : StmtExprMd) (order : List Nat) : StackM (List StmtExprMd) := do
  let st ← get
  let k := countStackReads v
  if st.stack.length < k then
    report v.source "this reads more stack values than were pushed"
    return [s]
  let popped := (st.stack.take k).reverse
  let pushed := order.filterMap (popped[·]?)
  set { st with stack := pushed.reverse ++ st.stack.drop k }
  return []

private partial def elimStmt (s0 : StmtExprMd) : StackM (List StmtExprMd) := do
  let s ← elimQuantifierBodies s0
  match s.val with
  | .Assign [⟨.Stack t, ts⟩] v =>
    if let some order := stackPermutation [⟨.Stack t, ts⟩] v then
      return ← permuteStack s v order
    if hasStackPush v then report v.source "a stack push must be a statement"
    let v' ← popReads v
    let name ← fresh
    modify fun st => { st with stack := (name, t) :: st.stack }
    pure [⟨.Assign [⟨.Declare ⟨name, t⟩, ts⟩] v', s.source⟩]
  | .Assign targets v =>
    if let some order := stackPermutation targets v then
      permuteStack s v order
    else
      if hasStackPush s then report s.source "a stack push must be a statement"
      pure [← popReads s]
  | .IfThenElse c th el =>
    if hasStackPush c then report c.source "a stack push must be a statement"
    let c' ← popReads c
    let base := (← get).stack
    let th' ← elimBranch th
    let thFinal := (← get).stack
    set { (← get) with stack := base }
    let (el', elFinal) ← match el with
      | some e => do
        let e' ← elimBranch e
        pure (some e', (← get).stack)
      | none => pure (none, base)
    let arms := [(th', thFinal)] ++ (el'.map (·, elFinal)).toList
    let (decls, arms') ← mergeArms s.source base
      (if el'.isNone then arms ++ [(⟨.Block [] none [] none, s.source⟩, elFinal)] else arms)
    let thOut := arms'.head?.getD th'
    let elOut := if el'.isNone && decls.isEmpty then none else arms'[1]?
    pure (decls ++ [⟨.IfThenElse c' thOut elOut, s.source⟩])
  | .Block stmts none [] none =>
    let base := (← get).stack
    let stmts' ← elimStmts stmts
    let final := (← get).stack
    let (decls, arms') ← mergeArms s.source base [(⟨.Block stmts' none [] none, s.source⟩, final)]
    pure (decls ++ arms')
  | .Block stmts (some label) [] none =>
    if isLoop label stmts then
      let body' ← elimIsolated ⟨.Block stmts none [] none, s.source⟩ "a labelled block"
      let stmts' := match body'.val with
        | .Block inner none [] none => inner
        | _ => [body']
      return [⟨.Block stmts' (some label) [] none, s.source⟩]
    let base := (← get).stack
    modify fun st => { st with openLabels := label :: st.openLabels }
    let stmts' ← elimStmts stmts
    let final := (← get).stack
    let st ← get
    let mine := st.exits.filter (·.1 == label)
    set { st with openLabels := st.openLabels.drop 1, exits := st.exits.filter (·.1 != label) }
    let natural := !endsAbruptly ⟨.Block stmts' none [] none, s.source⟩
    let finals := (if natural then [final] else []) ++ mine.map (·.2.2)
    let (decls, copies) ← mergeFinals s.source base finals
    let (natCopies, exitCopies) := if natural then (copies.head?.getD [], copies.drop 1) else ([], copies)
    let placed := ((mine.map (·.2.1)).zip (exitCopies ++ mine.map fun _ => []))
    let body := (stmts' ++ natCopies).map (placeExitCopies placed)
    pure (decls ++ [⟨.Block body (some label) [] none, s.source⟩])
  | .Block stmts label invs dec =>
    let invs' ← invs.mapM elimRoot
    let dec' ← dec.mapM elimRoot
    let body' ← elimIsolated ⟨.Block stmts none [] none, s.source⟩ "a labelled block"
    let stmts' := match body'.val with
      | .Block inner none [] none => inner
      | _ => [body']
    pure [⟨.Block stmts' label invs' dec', s.source⟩]
  | .While c invs dec body postTest =>
    if countStackReads c > 0 || hasStackPush c then
      report c.source "a loop condition cannot use the stack"
    let invs' ← invs.mapM elimRoot
    let dec' ← dec.mapM elimRoot
    let body' ← elimIsolated body "a loop body"
    pure [⟨.While c invs' dec' body' postTest, s.source⟩]
  | .Try body catches fin =>
    let body' ← elimIsolated body "a try block"
    let catches' ← catches.mapM fun c => do
      pure { c with body := ← elimIsolated c.body "a catch handler" }
    let fin' ← fin.mapM (elimIsolated · "a finally block")
    pure [⟨.Try body' catches' fin', s.source⟩]
  | .Goto target .blockEnd =>
    let st ← get
    if st.openLabels.contains target then
      set { st with counter := st.counter + 1, exits := st.exits ++ [(target, st.counter, st.stack)] }
      pure [exitMarker st.counter s]
    else
      unless st.stack.isEmpty do
        report s.source "stack values are left over at a jump"
      pure [s]
  | .Goto .. =>
    unless (← get).stack.isEmpty do
      report s.source "stack values are left over at a jump"
    pure [s]
  | _ =>
    if hasStackPush s then report s.source "a stack push must be a statement"
    pure [← popReads s]

end

private def copiesBetween (shared : List String) (e : StmtExprMd) : List (String × String) :=
  ((foldStmtExprM (m := StateM (List (String × String))) (fun n => do
    match n.val with
    | .Assign [⟨.Local b, _⟩] ⟨.Var (.Local a), _⟩ =>
      if shared.contains a.text && shared.contains b.text then modify ((a.text, b.text) :: ·)
    | _ => pure ()) e).run []).2

private def retypeShared (e : StmtExprMd) : StackM StmtExprMd := do
  let st ← get
  let copies := copiesBetween st.shared e
  let types := copies.foldl (init := st.readTypes) fun acc (a, b) =>
    if acc.any (·.1 == a) then acc else match acc.find? (·.1 == b) with
      | some (_, ty) => (a, ty) :: acc
      | none => acc
  let typeOf (name : Identifier) := (types.find? (·.1 == name.text)).map (·.2)
  pure <| mapStmtExpr (fun n => match n.val with
    | .Assign [⟨.Declare ⟨name, _⟩, ts⟩] v =>
      match typeOf name with
      | some ty => ⟨.Assign [⟨.Declare ⟨name, some ty⟩, ts⟩] v, n.source⟩
      | none => n
    | .Var (.Declare ⟨name, _⟩) =>
      match typeOf name with
      | some ty => ⟨.Var (.Declare ⟨name, some ty⟩), n.source⟩
      | none => n
    | _ => n) e

private def assignedFrom (e : StmtExprMd) : List (String × List String) :=
  ((foldStmtExprM (m := StateM (List (String × List String))) (fun n => do
    match n.val with
    | .Assign [⟨.Declare ⟨name, _⟩, _⟩] v | .Assign [⟨.Local name, _⟩] v =>
      if name.text.startsWith "$stack_" then modify ((name.text, localNames v) :: ·)
    | _ => pure ()) e).run []).2

private def oldClosure (deps : List (String × List String)) (start : List String) : List String :=
  (List.range (deps.length + 1)).foldl (init := start) fun acc _ =>
    let more := (deps.filter (acc.contains ·.1)).flatMap (·.2)
    (acc ++ more.filter (!acc.contains ·)).eraseDups

private def oldifyPushes (e : StmtExprMd) : StackM StmtExprMd := do
  let st ← get
  set { st with oldNames := [] }
  if st.oldNames.isEmpty then return e
  let pre := oldClosure (assignedFrom e) st.oldNames
  pure <| mapStmtExpr (fun n => match n.val with
    | .Assign [⟨.Declare ⟨name, t⟩, ts⟩] v =>
      if name.text.startsWith "$stack_" && pre.contains name.text && st.wrapOld v then
        ⟨.Assign [⟨.Declare ⟨name, t⟩, ts⟩] ⟨.Old v none, v.source⟩, n.source⟩
      else n
    | _ => n) e

private def isStackTemp (name : Identifier) : Bool := name.text.startsWith "$stack_"

private def stackTempReads (e : StmtExprMd) : List String :=
  (localNames e).filter (·.startsWith "$stack_")

private def assignedNames (e : StmtExprMd) : List String :=
  ((foldStmtExprM (m := StateM (List String)) (fun n => do
    match n.val with
    | .Assign targets _ => modify (targets.filterMap (fun t => match t.val with
        | .Local name | .Declare ⟨name, _⟩ => some name.text
        | _ => none) ++ ·)
    | .IncrDecr _ _ ⟨.Local name, _⟩ | .CompoundAssign _ ⟨.Local name, _⟩ _ => modify (name.text :: ·)
    | _ => pure ()) e).run []).2

private def readsHeapOutsideOld (e : StmtExprMd) : Bool :=
  let withoutOld := mapStmtExpr (fun n => match n.val with
    | .Old .. => ⟨.LiteralBool true, n.source⟩
    | _ => n) e
  anyStmtExpr (·.val matches .Var (.Field ..)) withoutOld

private def writesHeap (writers : Option (Std.HashSet Nat)) (e : StmtExprMd) : Bool :=
  let writer (callee : Identifier) : Bool := match writers, callee.uniqueId with
    | some ws, some id => ws.contains id
    | _, _ => true
  anyStmtExpr (fun n => match n.val with
    | .Assign targets _ => targets.any (·.val matches .Field ..)
    | .IncrDecr _ _ ⟨.Field .., _⟩ | .CompoundAssign _ ⟨.Field .., _⟩ _ => true
    | .Call none callee _ _ => !callee.text.startsWith "$" && writer callee
    | .Call (some _) callee _ _ => writer callee
    | _ => false) e

private def callsHeapWriter (writers : Option (Std.HashSet Nat)) (e : StmtExprMd) : Bool :=
  let writer (callee : Identifier) : Bool := match writers, callee.uniqueId with
    | some ws, some id => ws.contains id
    | _, _ => true
  anyStmtExpr (fun n => match n.val with
    | .Call none callee _ _ => !callee.text.startsWith "$" && writer callee
    | .Call (some _) callee _ _ => writer callee
    | _ => false) e

private def substLocal (name : String) (v : StmtExprMd) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local x) => if x.text == name then v else n
    | _ => n) e

private def compoundUse (name : String) (u : StmtExprMd) : Bool :=
  match u.val with
  | .IfThenElse c th el => (localNames th).contains name || (el.map (localNames · |>.contains name)).getD false
      || !(localNames c).contains name
  | .Block .. | .While .. | .Try .. => true
  | _ => false

private def readsGlobal (globals : Std.HashSet String) (v : StmtExprMd) : Bool :=
  (localNames v).any globals.contains

private def stableAcross (writers : Option (Std.HashSet Nat)) (globals : Std.HashSet String) (v : StmtExprMd)
    (between : List StmtExprMd) : Bool :=
  let reads := localNames v
  let heap := readsHeapOutsideOld v
  let global := readsGlobal globals v
  between.all fun b => !(assignedNames b).any reads.contains && !(heap && writesHeap writers b)
    && !(global && writesHeap none b)

private def usedAsReceiver (name : String) (u : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with
    | .Call (some ⟨.Var (.Local x), _⟩) _ _ _ => x.text == name
    | _ => false) u

private def receiverValue (v : StmtExprMd) : Bool :=
  v.val matches .Var (.Local _) | .This

private def rootRead? (name : String) (u : StmtExprMd) : Option (StmtExprMd → StmtExprMd) :=
  match u.val with
  | .Assign [t] ⟨.Var (.Local x), _⟩ =>
    if x.text == name then some fun v => ⟨.Assign [t] v, u.source⟩ else none
  | _ => none

private partial def inlineList (pure : String → Bool) (writers : Option (Std.HashSet Nat))
    (globals : Std.HashSet String) (uses : Std.HashMap String Nat) :
    List StmtExprMd → List StmtExprMd
  | [] => []
  | s :: rest =>
    match s.val with
    | .Assign [⟨.Declare ⟨name, _⟩, _⟩] v =>
      if !isStackTemp name || uses.getD name.text 0 != 1 then s :: inlineList pure writers globals uses rest else
      match rest.findIdx? (fun u => (localNames u).contains name.text) with
      | none => s :: inlineList pure writers globals uses rest
      | some j =>
        let between := rest.take j
        let u := rest[j]!
        let after := rest.drop (j + 1)
        if usedAsReceiver name.text u && !receiverValue v then s :: inlineList pure writers globals uses rest
        else if !callLike pure v then
          let simple := !compoundUse name.text u
          if stableAcross writers globals v (if simple then between else between ++ [u])
              && !(readsHeapOutsideOld v && callsHeapWriter writers u)
              && !(readsGlobal globals v && callsHeapWriter none u) then
            inlineList pure writers globals uses (between ++ substLocal name.text v u :: after)
          else s :: inlineList pure writers globals uses rest
        else
          match between, rootRead? name.text u with
          | [], some rebuild => inlineList pure writers globals uses (rebuild v :: after)
          | _, _ => s :: inlineList pure writers globals uses rest
    | _ => s :: inlineList pure writers globals uses rest

private def armValue? (arm : StmtExprMd) : Option (String × List StmtExprMd × StmtExprMd) :=
  let stmts := match arm.val with
    | .Block ss none [] none => ss
    | _ => [arm]
  match stmts.reverse with
  | last :: revPrefix =>
    let isDecl (s : StmtExprMd) : Bool := match s.val with
      | .Assign [⟨.Declare _, _⟩] _ => true
      | _ => false
    match last.val with
    | .Assign [⟨.Local t, _⟩] v =>
      if revPrefix.all isDecl then some (t.text, revPrefix.reverse, v) else none
    | _ => none
  | [] => none

private def armExpr (arm : StmtExprMd) (decls : List StmtExprMd) (v : StmtExprMd) : StmtExprMd :=
  if decls.isEmpty then v else ⟨.Block (decls ++ [v]) none [] none, arm.source⟩

private def declaresLocal (s : StmtExprMd) : Bool :=
  s.val matches .Assign [⟨.Declare _, _⟩] _ || s.val matches .Var (.Declare _)

private def assignsThrough (inner : List StmtExprMd) : Option (Identifier × FileRange × StmtExprMd) :=
  match inner.reverse with
  | ⟨.Assign [⟨.Local x, xs⟩] v, _⟩ :: revPre =>
    if revPre.all (·.val matches .Assign [⟨.Declare _, _⟩] _)
        && !revPre.any (fun d => match d.val with
          | .Assign [⟨.Declare p, _⟩] _ => p.name.text == x.text
          | _ => false) then some (x, xs, v) else none
  | _ => none

private def flattenBlocks (ss : List StmtExprMd) : List StmtExprMd :=
  ss.flatMap fun s => match s.val with
    | .Block inner none [] none =>
      if !inner.any declaresLocal then inner
      else match assignsThrough inner with
        | some (x, xs, v) =>
          [⟨.Assign [⟨.Local x, xs⟩] ⟨.Block (inner.dropLast ++ [v]) none [] none, s.source⟩, s.source⟩]
        | none => [s]
    | _ => [s]

private def declOf (d : StmtExprMd) : Option (Parameter? × FileRange) :=
  match d.val with
  | .Assign [⟨.Declare p, ds⟩] _ => some (p, ds)
  | .Var (.Declare p) => some (p, d.source)
  | _ => none

private def foldDeclAssign : List StmtExprMd → List StmtExprMd
  | d :: a :: rest =>
    match declOf d, a.val with
    | some (p, ds), .Assign [⟨.Local t, _⟩] v =>
      if p.name.text == t.text && isStackTemp p.name && !(localNames v).contains t.text then
        ⟨.Assign [⟨.Declare p, ds⟩] v, d.source⟩ :: foldDeclAssign rest
      else d :: foldDeclAssign (a :: rest)
    | _, _ => d :: foldDeclAssign (a :: rest)
  | ss => ss

private partial def withJump (jump : StmtExprMd) (arm : StmtExprMd) : StmtExprMd :=
  if endsAbruptly arm then arm else
  match arm.val with
  | .Block ss none [] none =>
    match ss.reverse with
    | ⟨.IfThenElse c th (some el), src⟩ :: rest =>
      ⟨.Block (rest.reverse ++ [⟨.IfThenElse c (withJump jump th) (some (withJump jump el)), src⟩]) none [] none,
        arm.source⟩
    | _ => ⟨.Block (ss ++ [jump]) none [] none, arm.source⟩
  | _ => ⟨.Block [arm, jump] none [] none, arm.source⟩

private def distributeJump (ss : List StmtExprMd) : List StmtExprMd :=
  match ss.reverse with
  | jump :: ⟨.IfThenElse c th (some el), src⟩ :: rest =>
    if jump.val matches .Goto .. then
      rest.reverse ++ [⟨.IfThenElse c (withJump jump th) (some (withJump jump el)), src⟩]
    else ss
  | _ => ss

private def foldMerges : List StmtExprMd → List StmtExprMd
  | d :: ite :: rest =>
    let decl := match d.val with
      | .Assign [⟨.Declare p, ds⟩] ⟨.LiteralBool _, _⟩ => some (p, ds)
      | .Assign [⟨.Declare p, ds⟩] ⟨.LiteralInt _, _⟩ => some (p, ds)
      | .Assign [⟨.Declare p, ds⟩] ⟨.LiteralString _, _⟩ => some (p, ds)
      | .Var (.Declare p) => some (p, d.source)
      | _ => none
    match decl, ite.val with
    | some (p, ds), .IfThenElse c th (some el) =>
      match armValue? th, armValue? el with
      | some (t1, dx, x), some (t2, dy, y) =>
        let reads := (c :: x :: y :: dx ++ dy).any (localNames · |>.contains p.name.text)
        if isStackTemp p.name && !reads && t1 == p.name.text && t2 == p.name.text then
          ⟨.Assign [⟨.Declare p, ds⟩] (if dx.isEmpty && dy.isEmpty then boolIte c x y ite.source
            else ⟨.IfThenElse c (armExpr th dx x) (some (armExpr el dy y)), ite.source⟩), d.source⟩ :: foldMerges rest
        else d :: foldMerges (ite :: rest)
      | _, _ => d :: foldMerges (ite :: rest)
    | _, _ => d :: foldMerges (ite :: rest)
  | ss => ss

private def unwrapValue (pure : String → Bool) (e : StmtExprMd) : StmtExprMd :=
  match e.val with
  | .Block [x] none [] none => if callLike pure x then e else x
  | _ => e

private partial def simplify (pure : String → Bool) (writers : Option (Std.HashSet Nat))
    (globals : Std.HashSet String) (uses : Std.HashMap String Nat)
    (e : StmtExprMd) : StmtExprMd :=
  let list (ss : List StmtExprMd) := inlineList pure writers globals uses (distributeJump (foldDeclAssign (foldMerges (flattenBlocks (ss.map (simplify pure writers globals uses))))))
  let spec (c : StmtExprMd) := unwrapValue pure (simplify pure writers globals uses c)
  match e.val with
  | .Block ss label invs dec => ⟨.Block (list ss) label (invs.map spec) (dec.map spec), e.source⟩
  | .IfThenElse c th el => ⟨.IfThenElse c (simplify pure writers globals uses th) (el.map (simplify pure writers globals uses)), e.source⟩
  | .While c invs dec body post => ⟨.While c invs dec (simplify pure writers globals uses body) post, e.source⟩
  | .Assign targets v => match v.val with
    | .Block .. => ⟨.Assign targets (spec v), e.source⟩
    | _ => e
  | .Try body catches fin =>
    ⟨.Try (simplify pure writers globals uses body) (catches.map fun c => { c with body := simplify pure writers globals uses c.body })
      (fin.map (simplify pure writers globals uses)), e.source⟩
  | _ => e

private def reassignedNames (e : StmtExprMd) : List String :=
  ((foldStmtExprM (m := StateM (List String)) (fun n => do
    match n.val with
    | .Assign targets _ => modify (targets.filterMap (fun t => match t.val with
        | .Local name => some name.text
        | _ => none) ++ ·)
    | _ => pure ()) e).run []).2

private def tempUses (e : StmtExprMd) : Std.HashMap String Nat :=
  let reassigned := reassignedNames e
  (stackTempReads e).foldl (init := {})
    fun m n => if reassigned.contains n then m.insert n 2 else m.insert n (m.getD n 0 + 1)

private def inlinePushes (e : StmtExprMd) : StackM StmtExprMd := do
  let writers := (← get).heapWriters
  let isPure := (← get).pure
  let globals := (← get).globals
  let simplifyQuantifiers (e : StmtExprMd) : StmtExprMd :=
    mapStmtExpr (fun n => match n.val with
      | .Quantifier mode param trig body =>
        let inBody (c : String) : Bool := c == "$quantifierBody" || isPure c
        ⟨.Quantifier mode param trig (unwrapValue inBody (simplify inBody writers globals (tempUses body) body)), n.source⟩
      | _ => n) e
  let single (a : StmtExprMd) : StmtExprMd := match a.val with
    | .Block [x] none [] none => x
    | _ => a
  let boolSimplify (e : StmtExprMd) : StmtExprMd :=
    mapStmtExpr (fun n => match n.val with
      | .IfThenElse c x (some y) =>
        if (single x).val matches .LiteralBool _ || (single y).val matches .LiteralBool _ then
          boolIte c (single x) (single y) n.source
        else n
      | .Block _ none [] none => unwrapValue isPure (simplify isPure writers globals (tempUses n) n)
      | _ => n) e
  let step (e : StmtExprMd) := boolSimplify (simplifyQuantifiers (unwrapValue isPure (simplify isPure writers globals (tempUses e) e)))
  pure ((List.range 4).foldl (fun e _ => step e) e)

def eliminateStack (program : LaurelProgram) (wrapOld : StmtExprMd → Bool := fun _ => true)
    (heapWriters : Option (Std.HashSet Nat) := none) : LaurelProgram × List Message :=
  let run (proc : Procedure) : StateM StackState Procedure :=
    if procedureTouchesStack proc then do
      let entry := (proc.inputs ++ proc.outputs).map (·.name.text)
      modify fun s => { s with
        wrapOld := fun v => wrapOld v || (localNames v).any fun n => entry.contains n || s.globals.contains n }
      let isPure := (← get).pure
      mapProcedureM (fun e => elimRoot (structureExits isPure e) >>= retypeShared >>= oldifyPushes >>= inlinePushes
        >>= fun e' => inlinePushes (structureExits isPure e')) proc
    else pure proc
  let witnesses := program.types.filterMap fun
    | .Constrained ct => some (ct.name.text, ct.witness)
    | _ => none
  let globals : Std.HashSet String := program.staticFields.foldl (·.insert ·.name.text) {}
  let (program', st) := (mapLaurelProgramProceduresM run program).run
    { witnesses, wrapOld, heapWriters, pure := program.pureCallee, globals }
  (program', st.diags)

def eliminateStackPass : LaurelPass where
  name := "EliminateStack"
  needsResolves := true
  documentation := "Turns Laurel's operand stack into locals: each `Stack := e` declares a fresh `$stack_N`, each read of `Stack` reads the local its statement takes in push order, a value pushed in both arms of an `if` is copied into one local declared before it, and a push whose value an `old(...)` reads is evaluated in the pre-state. Runs first, so no later pass sees a `Stack`; it needs the types resolution gives each push."
  creates := [
      NodeKind.StmtExpr.Assign,
      NodeKind.StmtExpr.Var,
      NodeKind.StmtExpr.Block,
      NodeKind.StmtExpr.LiteralBool
    ]
  removes := [NodeKind.StmtExpr.Var.var.Stack]
  run := fun _ p m => match p with
    | .Unordered program =>
      let (program', diags) := eliminateStack program (exprReadsHeap m.heapReaders) (some m.heapWriters)
      (.Unordered program', diags, {})
    | other => wrongProgram "EliminateStack" other

end -- public section

end Strata.Laurel
