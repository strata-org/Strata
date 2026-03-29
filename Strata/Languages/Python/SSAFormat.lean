/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.SSA
import Lean.Data.Position

/-!
# PythonSSA Pretty-Printer

Formats SSA IR as the textual notation defined in `docs/PythonSSA.md`.
Implements sugar for `callQualified`, `call attr()`, and inline literals.
-/

namespace Strata.Python.SSAFormat

open Strata.Python.SSA

def fmtVal (names : Array SSAName) (v : SSAVal) : String :=
  if h : v.id < names.size then
    let n := names[v.id]
    s!"%{v.id}:{n.base}.{n.suffix}"
  else
    s!"%{v.id}"

def fmtValBare (v : SSAVal) : String :=
  s!"%{v.id}"

def fmtBlockId (b : BlockId) : String :=
  s!"bb{b.id}"

/-! ## Type Formatting -/

partial def fmtPyType (t : PyType) : String :=
  match t with
  | .any     => "any"
  | .str     => "str"
  | .int     => "int"
  | .bool    => "bool"
  | .float   => "float"
  | .none    => "none"
  | .bytes   => "bytes"
  | .object  => "object"
  | .list e  => s!"list({fmtPyType e})"
  | .dict k v => s!"dict({fmtPyType k}, {fmtPyType v})"
  | .set e   => s!"set({fmtPyType e})"
  | .tuple es =>
    let inner := ", ".intercalate (es.toList.map fmtPyType)
    s!"tuple({inner})"
  | .optional t => s!"optional({fmtPyType t})"
  | .union alts =>
    let inner := ", ".intercalate (alts.toList.map fmtPyType)
    s!"union({inner})"
  | .typedDict _ _ => "typedDict(...)"
  | .literal _ => "literal(...)"
  | .named n => n

/-! ## Operator Formatting -/

def fmtBinOp (op : BinOpKind) : String :=
  match op with
  | .add => "add" | .sub => "sub" | .mult => "mult" | .div => "div"
  | .floorDiv => "floorDiv" | .mod => "mod" | .pow => "pow"

def fmtUnaryOp (op : UnaryOpKind) : String :=
  match op with
  | .not_ => "not" | .uSub => "uSub"

def fmtCmpOp (op : CmpOpKind) : String :=
  match op with
  | .eq => "eq" | .notEq => "notEq" | .lt => "lt" | .ltE => "ltE"
  | .gt => "gt" | .gtE => "gtE" | .is_ => "is" | .isNot => "isNot"
  | .in_ => "in" | .notIn => "notIn"

/-! ## Literal Helpers -/

def isLiteral (i : Instruction) : Bool :=
  match i with
  | .intLit _ | .floatLit _ | .strLit _ | .boolLit _ | .noneLit | .bytesLit _ => true
  | _ => false

def fmtLiteralInline (i : Instruction) : String :=
  match i with
  | .intLit v      => s!"intLit {v}"
  | .floatLit v    => s!"floatLit \"{v}\""
  | .strLit v      => s!"strLit \"{v}\""
  | .boolLit true  => "boolLit true"
  | .boolLit false => "boolLit false"
  | .noneLit       => "noneLit"
  | .bytesLit v    => s!"bytesLit \"{v}\""
  | _              => panic! "fmtLiteralInline called on non-literal"

/-! ## Use Count Analysis -/

def buildUseCounts (func : Func) : Std.HashMap Nat Nat := Id.run do
  let mut counts : Std.HashMap Nat Nat := {}
  let countVal (v : SSAVal) (c : Std.HashMap Nat Nat) : Std.HashMap Nat Nat :=
    let vid := v.id
    c.insert vid (c.getD vid 0 + 1)
  let countArg (a : CallArg) (c : Std.HashMap Nat Nat) : Std.HashMap Nat Nat :=
    match a with
    | .positional v | .starArgs v | .starKwargs v => countVal v c
    | .keyword _ v => countVal v c
  for block in func.blocks do
    for ni in block.instrs do
      match ni.instr with
      | .call f args =>
        counts := countVal f counts
        for a in args do counts := countArg a counts
      | .attr obj _ => counts := countVal obj counts
      | .setAttr obj _ v => counts := countVal obj (countVal v counts)
      | .binOp _ l r | .compareOp _ l r =>
        counts := countVal l (countVal r counts)
      | .unaryOp _ v | .fmtValue v | .isDefined v =>
        counts := countVal v counts
      | .mkDict ks vs =>
        for k in ks do counts := countVal k counts
        for v in vs do counts := countVal v counts
      | .mkList es | .mkTuple es | .strConcat es =>
        for e in es do counts := countVal e counts
      | .getItem o k => counts := countVal o (countVal k counts)
      | .setItem o k v => counts := countVal o (countVal k (countVal v counts))
      | .getSlice o l h s =>
        counts := countVal o counts
        if let some lv := l then counts := countVal lv counts
        if let some hv := h then counts := countVal hv counts
        if let some sv := s then counts := countVal sv counts
      | .assert_ c m =>
        counts := countVal c counts
        if let some mv := m then counts := countVal mv counts
      | _ => pure ()
      if let some eargs := ni.exceptArgs then
        for ea in eargs do
          if let .val v := ea then counts := countVal v counts
    match block.term with
    | .branch _ args =>
      for a in args do counts := countVal a counts
    | .condBranch c _ ta _ ea =>
      counts := countVal c counts
      for a in ta do counts := countVal a counts
      for a in ea do counts := countVal a counts
    | .ret (some v) => counts := countVal v counts
    | .raise exc => counts := countVal exc counts
    | _ => pure ()
  return counts

/-! ## Block Context (precomputed for O(1) lookups) -/

/-- Precomputed per-block context for efficient formatting. -/
structure BlockCtx where
  names      : Array SSAName
  useCounts  : Std.HashMap Nat Nat
  /-- Maps SSA val ID → defining NamedInstr (O(1) vs O(n) scan). -/
  defMap     : Std.HashMap Nat NamedInstr
  /-- Set of SSA val IDs that appear as the `func` argument of a `.call`. -/
  callTargets : Std.HashSet Nat
  /-- Set of SSA val IDs that appear in the block's terminator.
      Literals used in terminators cannot be inlined (terminators use bare refs). -/
  termUses : Std.HashSet Nat

private def collectTermUses (term : Terminator) : Std.HashSet Nat :=
  let addVal (s : Std.HashSet Nat) (v : SSAVal) := s.insert v.id
  match term with
  | .branch _ args => args.foldl addVal {}
  | .condBranch c _ ta _ ea =>
    let s := addVal {} c
    let s := ta.foldl addVal s
    ea.foldl addVal s
  | .ret (some v) => addVal {} v
  | .raise v => addVal {} v
  | _ => {}

def buildBlockCtx (names : Array SSAName) (useCounts : Std.HashMap Nat Nat)
    (instrs : Array NamedInstr) (term : Terminator) : BlockCtx :=
  let defMap : Std.HashMap Nat NamedInstr := instrs.foldl (init := {}) fun m ni =>
    match ni.result with
    | some v => m.insert v.id ni
    | none => m
  let callTargets : Std.HashSet Nat := instrs.foldl (init := {}) fun s ni =>
    match ni.instr with
    | .call func _ => s.insert func.id
    | _ => s
  let termUses := collectTermUses term
  { names, useCounts, defMap, callTargets, termUses }

/-- Use count for an SSA value. Returns 0 for unknown IDs, which is sound:
    a value not in the map was never referenced, so inlining/skipping decisions
    that check `useCount ctx v == 1` correctly treat it as non-inlineable. -/
def useCount (ctx : BlockCtx) (v : SSAVal) : Nat :=
  ctx.useCounts.getD v.id 0

/-! ## Value Resolution -/

def findDef (ctx : BlockCtx) (v : SSAVal) : Option NamedInstr :=
  ctx.defMap[v.id]?

def resolveVal (ctx : BlockCtx) (v : SSAVal) : String :=
  match findDef ctx v with
  | some ni =>
    if isLiteral ni.instr && useCount ctx v == 1 then
      fmtLiteralInline ni.instr
    else fmtValBare v
  | none => fmtValBare v

/-! ## CallArg Formatting -/

def fmtCallArg (ctx : BlockCtx) (arg : CallArg) : String :=
  let rv := resolveVal ctx
  match arg with
  | .positional v => s!"positional({rv v})"
  | .keyword n v  => s!"keyword(\"{n}\", {rv v})"
  | .starArgs v   => s!"starArgs({rv v})"
  | .starKwargs v => s!"starKwargs({rv v})"

def fmtExceptArgs (args : Array ExceptArgVal) : String :=
  let parts := args.map fun ea => match ea with
    | .val v => fmtValBare v
    | .exc   => "exc"
  s!"  [exceptArgs: {", ".intercalate parts.toList}]"

/-! ## Instruction Formatting -/

def shouldSkipInstr (ctx : BlockCtx) (ni : NamedInstr) : Bool :=
  match ni.result with
  | none => false
  | some v =>
    let vid := v.id
    -- Never skip values used in terminators (terminators use bare refs, not inlined)
    if vid ∈ ctx.termUses then false
    else
    let uses := useCount ctx v
    if uses != 1 then false
    else if isLiteral ni.instr then true
    else match ni.instr with
    | .attr _ _ | .qualifiedRef _ => vid ∈ ctx.callTargets
    | _ => false

def fmtNamedInstr (ctx : BlockCtx) (ni : NamedInstr) : Array String :=
  if shouldSkipInstr ctx ni then #[]
  else
    let rv := resolveVal ctx
    let fmtArgs' (args : Array CallArg) :=
      ", ".intercalate (args.map (fmtCallArg ctx) |>.toList)
    let fmtLhs : String :=
      match ni.result with
      | some val =>
        let typeStr := match ni.type with | some t => s!" : {fmtPyType t}" | none => ""
        s!"{fmtVal ctx.names val}{typeStr} = "
      | none => ""
    let exceptStr := match ni.exceptArgs with
      | some eargs => fmtExceptArgs eargs
      | none => ""
    match ni.instr with
    | .call func args =>
      match findDef ctx func with
      | some funcNi =>
        match funcNi.instr with
        | .qualifiedRef qn =>
          if useCount ctx func == 1 then
            let argsStr := fmtArgs' args
            let line := s!"    {fmtLhs}callQualified {qn} [{argsStr}]{exceptStr}"
            let whereLines := args.toList.filterMap fun arg =>
              let argVal := match arg with
                | .positional v | .keyword _ v | .starArgs v | .starKwargs v => v
              match findDef ctx argVal with
              | some argNi => match argNi.instr with
                | .qualifiedRef argQn =>
                  if useCount ctx argVal == 1 then
                    some s!"      -- where {fmtValBare argVal} = qualifiedRef {argQn}"
                  else none
                | _ => none
              | _ => none
            #[line] ++ whereLines.toArray
          else #[s!"    {fmtLhs}call {rv func}({fmtArgs' args}){exceptStr}"]
        | .attr obj attrName =>
          if useCount ctx func == 1 then
            #[s!"    {fmtLhs}call attr({rv obj}, \"{attrName}\")({fmtArgs' args}){exceptStr}"]
          else #[s!"    {fmtLhs}call {rv func}({fmtArgs' args}){exceptStr}"]
        | _ => #[s!"    {fmtLhs}call {rv func}({fmtArgs' args}){exceptStr}"]
      | none => #[s!"    {fmtLhs}call {rv func}({fmtArgs' args}){exceptStr}"]
    | _ =>
      let instrStr := match ni.instr with
        | .undef name     => s!"undef(\"{name}\")"
        | .isDefined v    => s!"isDefined {rv v}"
        | .intLit v       => s!"intLit {v}"
        | .floatLit v     => s!"floatLit \"{v}\""
        | .strLit v       => s!"strLit \"{v}\""
        | .boolLit true   => "boolLit true"
        | .boolLit false  => "boolLit false"
        | .noneLit        => "noneLit"
        | .bytesLit v     => s!"bytesLit \"{v}\""
        | .qualifiedRef qn => s!"qualifiedRef {qn}"
        | .attr obj name  => s!"attr {rv obj} \"{name}\""
        | .setAttr obj name val => s!"setAttr {rv obj} \"{name}\" {rv val}"
        | .binOp op l r   => s!"binOp {fmtBinOp op} {rv l} {rv r}"
        | .unaryOp op v   => s!"unaryOp {fmtUnaryOp op} {rv v}"
        | .compareOp op l r => s!"compareOp {fmtCmpOp op} {rv l} {rv r}"
        | .mkDict ks vs   =>
          s!"mkDict [{", ".intercalate (ks.toList.map rv)}] [{", ".intercalate (vs.toList.map rv)}]"
        | .mkList es      => s!"mkList [{", ".intercalate (es.toList.map rv)}]"
        | .mkTuple es     => s!"mkTuple [{", ".intercalate (es.toList.map rv)}]"
        | .getItem o k    => s!"getItem {rv o} {rv k}"
        | .setItem o k v  => s!"setItem {rv o} {rv k} {rv v}"
        | .getSlice o l h s =>
          let fmtOpt opt := match opt with | some x => s!"(some {rv x})" | none => "none"
          s!"getSlice {rv o} {fmtOpt l} {fmtOpt h} {fmtOpt s}"
        | .fmtValue v     => s!"fmtValue {rv v}"
        | .strConcat ps   => s!"strConcat [{", ".intercalate (ps.toList.map rv)}]"
        | .assert_ c m    =>
          let mStr := match m with | some v => s!"(some {rv v})" | none => "none"
          s!"assert_ {rv c} {mStr}"
        | .unsupported n  => s!"unsupported \"{n}\""
        | .call _ _       => unreachable!
      #[s!"    {fmtLhs}{instrStr}{exceptStr}"]

/-! ## Terminator Formatting -/

def fmtTerminator (t : Terminator) : String :=
  match t with
  | .branch target args =>
    s!"    branch {fmtBlockId target}({", ".intercalate (args.toList.map fmtValBare)})"
  | .condBranch cond thenB thenArgs elseB elseArgs =>
    let thenStr := ", ".intercalate (thenArgs.toList.map fmtValBare)
    let elseStr := ", ".intercalate (elseArgs.toList.map fmtValBare)
    s!"    condBranch {fmtValBare cond} {fmtBlockId thenB}({thenStr}) {fmtBlockId elseB}({elseStr})"
  | .ret (some v) => s!"    ret {fmtValBare v}"
  | .ret none     => "    ret"
  | .raise exc    => s!"    raise {fmtValBare exc}"
  | .unreachable  => "    unreachable"

/-! ## Block and Function Formatting -/

def fmtBlockParam (names : Array SSAName) (bp : BlockParam) : String :=
  let typeStr := match bp.type with | some t => s!" : {fmtPyType t}" | none => ""
  s!"{fmtVal names bp.val}{typeStr}"

def fmtBlock (names : Array SSAName) (useCounts : Std.HashMap Nat Nat)
    (block : Block) : Array String :=
  let ctx := buildBlockCtx names useCounts block.instrs block.term
  let paramsStr := ", ".intercalate (block.params.toList.map (fmtBlockParam names))
  let exceptStr := match block.except with
    | some et => s!" [except: {fmtBlockId et.target}]"
    | none => ""
  let header := s!"  {fmtBlockId block.id}({paramsStr}){exceptStr}:"
  let instrLines := block.instrs.flatMap (fmtNamedInstr ctx)
  let termLine := fmtTerminator block.term
  #[header] ++ instrLines ++ #[termLine]

def fmtFuncParam (fp : FuncParam) : String :=
  match fp.type with
  | some t => s!"{fp.name}: {fmtPyType t}"
  | none   => fp.name

/-- Format a complete function. -/
public def fmtFunc (func : Func) : String :=
  let useCounts := buildUseCounts func
  let paramsStr := ", ".intercalate (func.params.toList.map fmtFuncParam)
  let retStr := match func.retType with | some t => s!" -> {fmtPyType t}" | none => ""
  let header := s!"func {func.name}({paramsStr}){retStr}:"
  let blockLines := func.blocks.flatMap (fmtBlock func.names useCounts)
  "\n".intercalate (#[header] ++ blockLines).toList

/-- Format a source range using an optional FileMap for line:col positions. -/
def fmtSourceRange (sr : SourceRange) (fileMap : Option Lean.FileMap) : String :=
  if sr.isNone then ""
  else match fileMap with
  | some fm =>
    let startPos := fm.toPosition sr.start
    let endPos := fm.toPosition sr.stop
    s!"{startPos.line}:{startPos.column}-{endPos.line}:{endPos.column}"
  | none => s!"{sr.start}-{sr.stop}"

/-- Format a single diagnostic (warning or error) as a comment line. -/
def fmtDiagnostic (prefix_ : String) (msg : String) (sr : SourceRange)
    (fileMap : Option Lean.FileMap) : String :=
  if sr.isNone then s!"-- {prefix_}: {msg}"
  else s!"-- {prefix_}: {msg} at {fmtSourceRange sr fileMap}"

/-- Format an array of diagnostics as comment lines. -/
public def fmtDiagnostics (prefix_ : String) (diags : Array (String × SourceRange))
    (fileMap : Option Lean.FileMap) : Array String :=
  diags.map fun (msg, sr) => fmtDiagnostic prefix_ msg sr fileMap

/-- Format a complete SSA module. -/
public def fmtModule (mod : Module) : String :=
  let header := s!"module \"{mod.name}\":"
  let funcStrs := mod.funcs.map fmtFunc
  s!"{header}\n\n{"\n\n".intercalate funcStrs.toList}\n"

/-- Format warnings as comment lines suitable for prepending to SSA output. -/
public def fmtWarnings (warnings : Array (String × SourceRange))
    (fileMap : Option Lean.FileMap := none) : String :=
  if warnings.isEmpty then ""
  else
    let lines := fmtDiagnostics "WARNING" warnings fileMap
    "\n".intercalate lines.toList ++ "\n"
