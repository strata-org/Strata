/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Cortex
public meta import Strata.Languages.Cortex.Wire
public meta import Strata.Languages.Cortex.Interpreter

/-!
# Helpers for the tests of the Cortex cleanup passes

Builders for small programs in the Cortex wire format, a printer for Cortex
procedure bodies, a well-formedness check, and a runner that reports what the
Cortex interpreter observes.

The printer ends each command with `@n`, where `n` is the start offset of the
command's source range, so that an expected output pins which source
locations the commands carry.
-/

meta section

public section

namespace Cortex.CleanupHelpers

open Imperative Lambda Strata Cortex.Liveness

def at_ (n : Nat) : FileRange := { file := .file "T.java", range := { start := ⟨n⟩, stop := ⟨n + 1⟩ } }

def int : Wire.Ty := .int
def v (x : String) : Wire.Expr := .var x
def blk (label : String) (cmds : List Wire.Cmd) (transfer : Wire.Transfer) : Wire.Block :=
  { label, cmds, transfer }

/-- `var x: int := 0`, at offset `n`. -/
def decl (x : String) (n : Nat) : Wire.Cmd := .init x int (some (.int 0)) (at_ n)

/-- A procedure with the body `blocks`, entered at the first block. -/
def proc (name : String) (inputs outputs : List (String × Wire.Ty)) (blocks : List Wire.Block)
    (handlers : List Wire.Handler := []) (entry : Bool := false) : Wire.Procedure :=
  { name, inputs := inputs.map fun (x, ty) => { name := x, ty },
    outputs := outputs.map fun (x, ty) => { name := x, ty },
    throws := none, requires := [], entry, source := at_ 0,
    body := some { entry := (blocks.head?.map (·.label)).getD "", blocks, handlers } }

/-- A handler for every exception of the `covered` blocks. -/
def handler (covered : List String) (binder target : String) : Wire.Handler :=
  { covered, catchType := none, binder, target, source := at_ 0 }

/-- The composites `Exn`, with no fields, and `Box`, with the field `val: int`. -/
def composites : List Wire.Composite :=
  [{ name := "Exn", extending := [], fields := [] },
   { name := "Box", extending := [], fields := [{ name := "val", ty := int }] }]

/-- The array type `Ints`, with `int` elements. -/
def arrays : List Wire.ArrayDecl := [{ name := "Ints", elem := int, extending := [] }]

/-- The Cortex program of `procedures` over `composites` and `arrays`. -/
def program (procedures : List Wire.Procedure) (constrained : List Wire.Constrained := []) :
    Except String UnorderedProgram :=
  Wire.Program.toCortex { composites, constrained, procedures, arrays }

def offset (md : MD) : String :=
  match Imperative.getFileRange md with
  | some fr => s!"  @{fr.range.start.byteIdx}"
  | none => ""

def showExprs (es : List Expr) : String := ", ".intercalate (es.map fun e => toString (Std.format e))

def showResults (lhs : List Core.Expression.Ident) : String :=
  if lhs.isEmpty then "" else s!"{", ".intercalate (lhs.map (·.name))} := "

def showCmd : IRCmd → String
  | .cmd (.init x ty (.det e) md) => s!"var {x.name}: {Std.format ty} := {Std.format e}{offset md}"
  | .cmd (.init x ty .nondet md) => s!"var {x.name}: {Std.format ty}{offset md}"
  | .cmd (.set x (.det e) md) => s!"{x.name} := {Std.format e}{offset md}"
  | .cmd (.set x .nondet md) => s!"havoc {x.name}{offset md}"
  | .cmd (.assert l e md) => s!"assert {l}: {Std.format e}{offset md}"
  | .cmd (.assume l e md) => s!"assume {l}: {Std.format e}{offset md}"
  | .cmd (.cover l e md) => s!"cover {l}: {Std.format e}{offset md}"
  | .cast x ty e mode md => s!"{x.name} := cast {ty} {Std.format e} {repr mode}{offset md}"
  | .new x ty md => s!"{x.name} := new {ty}{offset md}"
  | .readField x o f md => s!"{x.name} := {Std.format o}.{f.owner}.{f.field}{offset md}"
  | .writeField o f e md => s!"{Std.format o}.{f.owner}.{f.field} := {Std.format e}{offset md}"
  | .instanceOf x o ty md => s!"{x.name} := {Std.format o} instanceof {ty}{offset md}"
  | .newArray x ty len md => s!"{x.name} := newArray {ty}[{Std.format len}]{offset md}"
  | .readElem x a i ty md => s!"{x.name} := {Std.format a}[{Std.format i}] : {Std.format ty}{offset md}"
  | .writeElem a i v ty md => s!"{Std.format a}[{Std.format i}] := {Std.format v} : {Std.format ty}{offset md}"
  | .arrayLength x a md => s!"{x.name} := length {Std.format a}{offset md}"
  | .call lhs p args md => s!"call {showResults lhs}{p}({showExprs args}){offset md}"
  | .virtualCall lhs o m args md => s!"virtualCall {showResults lhs}{o}.{m}({showExprs args}){offset md}"
  | .throw e md => s!"throw {Std.format e}{offset md}"

def showTransfer : DetTransferCmd Label Core.Expression → String
  | .finish md => s!"finish{offset md}"
  | .condGoto c lt lf md =>
    if lt == lf then s!"goto {lt}{offset md}" else s!"if {Std.format c} goto {lt} else {lf}{offset md}"

def showProcedure (p : Procedure) : String :=
  let params := fun (ps : List (Core.Expression.Ident × Core.Expression.Ty)) =>
    ", ".intercalate (ps.map fun (x, t) => s!"{x.name}: {Std.format t}")
  let header := s!"procedure {p.name}({params p.inputs}) returns ({params p.outputs})"
  match p.body with
  | none => header
  | some b =>
    let blocks := b.cfg.blocks.flatMap fun (l, blk) =>
      s!"{l}:" :: blk.cmds.map (s!"  {showCmd ·}") ++ [s!"  {showTransfer blk.transfer}"]
    let handlers := b.handlers.map fun h =>
      s!"handler {h.covered} catch {h.catchType.getD "*"} as {h.binder.name} goto {h.target}"
    "\n".intercalate (header :: blocks ++ handlers)

def showProgram (prog : UnorderedProgram) : String :=
  "\n".intercalate (prog.procedures.map showProcedure)

/-- What is wrong with the shape of `prog`: a transfer or a handler that names
a missing block, a duplicate label, or a variable that is read, assigned or
bound without being a global, a parameter or a declared local. -/
def wellFormedErrors (prog : UnorderedProgram) : List String :=
  prog.procedures.flatMap fun p =>
    match p.body with
    | none => []
    | some b =>
      let labels := b.cfg.labels
      let declared : VarSet := Std.HashSet.ofList <|
        (prog.globals ++ p.inputs ++ p.outputs).map (·.1.name) ++
        b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.filterMap fun
          | .cmd (.init x ..) => some x.name
          | _ => none
      let undeclared := fun (xs : List String) =>
        (xs.filter (!declared.contains ·)).map fun x => s!"{p.name}: variable '{x}' is not declared"
      (if labels.contains b.cfg.entry then [] else [s!"{p.name}: entry '{b.cfg.entry}' is not a block"]) ++
      (if labels.eraseDups.length == labels.length then [] else [s!"{p.name}: duplicate label"]) ++
      (b.cfg.blocks.flatMap fun (_, blk) =>
        (blk.transfer.targets.filter (!labels.contains ·)).map (s!"{p.name}: transfer to missing block '{·}'") ++
        undeclared (transferUses blk.transfer) ++
        blk.cmds.flatMap fun c => undeclared (cmdUses c ++ assignedNames c)) ++
      b.handlers.flatMap fun h =>
        ((h.target :: h.covered).filter (!labels.contains ·)).map (s!"{p.name}: handler names missing block '{·}'") ++
        undeclared [h.binder.name]

/-- What the Cortex interpreter observes when it runs the entry procedures of
`prog`: per entry, the failed assertions with their offsets, and then the
values of the outputs or the offset of the uncaught exception. -/
def observe (prog : UnorderedProgram) (fuel : Nat := 10000) : String :=
  "\n".intercalate <| (prog.procedures.filter Interp.isEntry).map fun p =>
    match Interp.runEntry prog fuel p with
    | .error _ => s!"{p.name}: stopped"
    | .ok (final, trace) =>
      let failed := (Interp.failures trace).map fun (md, summary) => s!"{summary} fails{offset md};"
      let ending := match final with
        | .terminal ρ => "returns " ++ ", ".intercalate (p.outputs.map fun (x, _) =>
            s!"{x.name} = {(ρ.store x).map (toString ∘ Std.format) |>.getD "?"}")
        | .raised _ _ md => s!"raises{offset md}"
        | _ => "did not finish"
      " ".intercalate (s!"{p.name}:" :: failed ++ [ending])

/-- Print `prog` after `pass`, or the error, and then the well-formedness
errors of the result. -/
def showAfter (pass : Pass) (prog : Except String UnorderedProgram) : IO Unit :=
  match prog >>= fun prog => runPasses [pass] (.unordered prog) with
  | .error e => IO.println s!"error: {e}"
  | .ok (.unordered prog) => do
    IO.println (showProgram prog)
    for e in wellFormedErrors prog do IO.println s!"ill-formed: {e}"
  | .ok (.ordered _) => IO.println "error: ordered program"

end Cortex.CleanupHelpers

end

end
