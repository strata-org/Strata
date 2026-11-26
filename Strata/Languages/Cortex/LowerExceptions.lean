/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.LowerExceptions

open Imperative Lambda

public section

def thrownOut : String := "$thrown"
def excOut : String := "$exc"
def exvVar : String := "$exv"
def callThrown : String := "$callThrown"
def callExc : String := "$callExc"
def testVar : String := "$exnTest"
def anyExnName : TypeName := "$AnyComposite"
def exnTy : LTy := mono (tcon anyExnName)
def boolTy : LTy := mono .bool

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

structure St where
  blocks : Array (Label × LBlock) := #[]
  fresh : Nat := 0
  saves : Array (String × LTy) := #[]

abbrev M := StateM St

def freshLabel (base : String) : M Label := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{base}$exn{s.fresh}"

def saveVar (ty : LTy) : M String := do
  let s ← get
  let x := s!"$callResult{s.saves.size}"
  set { s with saves := s.saves.push (x, ty) }
  return x

def addBlock (l : Label) (b : LBlock) : M Unit :=
  modify fun s => { s with blocks := s.blocks.push (l, b) }

def setCmd (x : String) (e : Expr) (md : MD := .empty) : IRCmd := .cmd (.set (ident x) (.det e) md)

def uncaughtMd (summary : String) (md : MD) : MD :=
  match md.findElem Imperative.MetaData.propertySummary with
  | some _ => md
  | none => md.pushElem Imperative.MetaData.propertySummary (.msg summary)

def dispatch (procThrows : Bool) (exitLabel : Label) (md : MD) (summary : String) :
    List Handler → M Label
  | [] => do
    let l ← freshLabel "$uncaught"
    if procThrows then
      addBlock l { cmds := [setCmd excOut (mkFvar exvVar) md, setCmd thrownOut tt md],
                   transfer := .goto exitLabel }
    else
      addBlock l { cmds := [.cmd (.assert "uncaught_exception" ff (uncaughtMd summary md)),
                            .cmd (.assume "uncaught_exception" ff md)],
                   transfer := .finish md }
    return l
  | h :: rest => do
    let bind ← freshLabel "$catch"
    addBlock bind { cmds := [setCmd h.binder.name (mkFvar exvVar) md], transfer := .goto h.target }
    match h.catchType with
    | none => return bind
    | some t =>
      let next ← dispatch procThrows exitLabel md summary rest
      let l ← freshLabel "$catchTest"
      addBlock l { cmds := [.instanceOf (ident testVar) (mkFvar exvVar) (mono (tcon t)) md],
                   transfer := .condGoto (mkFvar testVar) bind next md }
      return l

def raiseMd : IRCmd → MD
  | .throw _ md | .call _ _ _ md | .virtualCall _ _ _ _ md => md
  | _ => .empty

partial def splitBlock (tys : Std.HashMap String LTy) (throwing : Std.HashMap String (String × List Nat)) (procThrows : Bool) (exitLabel : Label)
    (hs : List Handler) (label : Label) (pre : Array IRCmd) :
    List IRCmd → DetTransferCmd Label Core.Expression → M Unit
  | [], tr => addBlock label { cmds := pre.toList, transfer := tr }
  | c :: cs, tr =>
    match c with
    | .throw e md => do
      let d ← dispatch procThrows exitLabel md "uncaught exception is not thrown" hs
      addBlock label { cmds := (pre.push (setCmd exvVar e md)).toList, transfer := .goto d }
      let dead ← freshLabel "$afterThrow"
      splitBlock tys throwing procThrows exitLabel hs dead #[] cs tr
    | .call lhs p args md =>
      if let some (ty, inouts) := throwing.get? p then do
        let d ← dispatch procThrows exitLabel md s!"call does not throw an uncaught '{ty}'" hs
        let raise ← freshLabel "$raise"
        let results ← lhs.zipIdx.mapM fun (x, i) => do
          if inouts.contains i then return (x, none) else
          match tys.get? x.name with
          | some ty => return (x, some (← saveVar ty))
          | none => return (x, none)
        let targets := results.map fun (x, tmp) => match tmp with
          | some t => ident t
          | none => x
        let assigns := results.filterMap fun (x, tmp) => tmp.map fun t => setCmd x.name (mkFvar t) md
        addBlock raise { cmds := [setCmd exvVar (mkFvar callExc) md], transfer := .goto d }
        let cont ← freshLabel "$noThrow"
        let call : IRCmd := .call (targets ++ [ident callThrown, ident callExc]) p args md
        addBlock label { cmds := (pre.push call).toList,
                         transfer := .condGoto (mkFvar callThrown) raise cont md }
        splitBlock tys throwing procThrows exitLabel hs cont assigns.toArray cs tr
      else splitBlock tys throwing procThrows exitLabel hs label (pre.push c) cs tr
    | _ => splitBlock tys throwing procThrows exitLabel hs label (pre.push c) cs tr

def lowerBody (tys : Std.HashMap String LTy) (throwing : Std.HashMap String (String × List Nat)) (procThrows : Bool) (b : Body) : Body :=
  let exitLabel := "$exnExit"
  let entry := "$exnEntry"
  let act : M Unit := do
    for (l, blk) in b.cfg.blocks do
      let hs := b.handlers.filter (·.covered.contains l)
      splitBlock tys throwing procThrows exitLabel hs l #[] blk.cmds blk.transfer
  let ((), st) := act.run {}
  let raised := st.fresh > 0
  let inits : List IRCmd := if !raised && !procThrows then [] else
    [.cmd (.init (ident exvVar) exnTy .nondet .empty),
     .cmd (.init (ident callThrown) boolTy .nondet .empty),
     .cmd (.init (ident callExc) exnTy .nondet .empty),
     .cmd (.init (ident testVar) boolTy .nondet .empty)] ++
    st.saves.toList.map (fun (x, ty) => .cmd (.init (ident x) ty .nondet .empty)) ++
    (if procThrows then [setCmd thrownOut ff] else [])
  let extra : List (Label × LBlock) :=
    [(entry, { cmds := inits, transfer := .goto b.cfg.entry })] ++
    (if procThrows then [(exitLabel, { cmds := [], transfer := .finish .empty })] else [])
  { cfg := { entry := entry, blocks := extra ++ st.blocks.toList }, handlers := [] }

/-- The procedure with its exceptions lowered. A procedure with a `throws` clause gains the
outputs `$thrown` and `$exc`, and returns normally where it raised, with `$thrown` true; its
postconditions, which the source checks only on a normal return, become `$thrown || e`. -/
def lowerProcedure (globals : List (Core.Expression.Ident × LTy)) (throwing : Std.HashMap String (String × List Nat))
    (p : Procedure) : Procedure :=
  let procThrows := p.throws.isSome
  let outputs := if procThrows then p.outputs ++ [(ident thrownOut, boolTy), (ident excOut, exnTy)]
    else p.outputs
  let tys : Std.HashMap String LTy := (globals ++ p.inputs ++ p.outputs).foldl (fun m (x, t) => m.insert x.name t) {}
  let tys := match p.body with
    | some b => b.cfg.blocks.foldl (fun m (_, blk) => blk.cmds.foldl (fun m c => match c with
        | .cmd (.init x t _ _) => m.insert x.name t
        | _ => m) m) tys
    | none => tys
  let ensures := if procThrows then
      p.ensures.map fun post => { post with cond := mkCall "Bool.Or" [mkFvar thrownOut, post.cond] }
    else p.ensures
  { p with outputs, ensures, throws := none, body := p.body.map (lowerBody tys throwing procThrows) }

def run (prog : UnorderedProgram) : Except String UnorderedProgram := do
  prog.refuseVirtualCalls "LowerExceptions"
  let throwing : Std.HashMap String (String × List Nat) := prog.procedures.foldl
    (fun s p => match p.throws with
      | some t =>
        let inouts := p.outputs.zipIdx.filterMap fun ((x, _), i) =>
          if p.inputs.any (·.1.name == x.name) then some i else none
        s.insert p.name (t, inouts)
      | none => s) {}
  .ok (prog.mapProcedures (lowerProcedure prog.globals throwing))

def pass : Pass := Pass.onUnordered "LowerExceptions" run

end

end Cortex.LowerExceptions
