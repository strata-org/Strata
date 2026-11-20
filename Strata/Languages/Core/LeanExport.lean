/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.SMT.Lean.ExportConfig
public import Strata.DL.SMT.Lean.Query

/-!
# Optional Lean export for Core verification

Set `Core.VerifyOptions.leanExport` to an `ExportConfig`. Each validity check that comes up
for export (`Scope`) and is in the config's scope is then also written as a Lean theorem
file: the proposition is Strata's translation to Lean of the check's validity query, and its
proof is left as `sorry`. That the translation is faithful is tested and reviewed, not proved
(docs/LeanExport.md). By default the scope is the checks the solver leaves undecided
(`unknown`, or a timeout). The solver's answers, and everything Core reports,
are unchanged.
-/

public section

open Lean Strata.SMT.LeanExport

namespace Core.LeanExport

/-! ## Printing

The proposition is written out in full: every constant by its full name with `@`, every
argument, universe level, instance and literal explicit, every binder with its type. Nothing
is left for Lean to infer, so the text elaborates to the expression it was printed from, up
to the names of binders (a binder is renamed when an enclosing binder or a constant has its
name, and Lean names the hypothesis of an implication itself), and printing needs no Lean
environment. A subterm that occurs more than once in a term and whose text is at least
`shareThreshold` bytes long is written once and bound by a `let` without a type, as the
solver's own format binds a shared term; unfolding those bindings gives the expression the
text was printed from. Only identical subterms are bound together: two that differ in a
binder's name are written separately. After `unfold vcProp`, Lean displays the goal in the
usual notation.

Nothing here type-checks the proposition, which would need an environment as well. The
translator builds a well-typed expression from a well-sorted query; an ill-sorted one gives a
file that Lean rejects when it is opened. -/

/-- The first component of every constant the expression uses. A binder with such a name
would capture a reference to the constant. -/
private def constantHeads (e : Expr) : Std.HashSet String :=
  e.foldConsts {} fun n heads => heads.insert n.getRoot.toString

private def levelText (l : Level) : Except String String :=
  match l.toNat with
  | some n => pure (toString n)
  | none => throw s!"Universe level '{l}' is not a numeral"

/-- The binders in scope, innermost last, and the names they use. The structure is shared
between a scope and the scopes under it, so entering a binder does not copy it. -/
private structure Binders where
  binders : Lean.PersistentArray String := {}
  names : Lean.PersistentHashSet String := {}
  /-- The last suffix tried for a name that was already taken. -/
  suffixes : Lean.PersistentHashMap String Nat := {}

/-- The scope under one more binder. A premise binds nothing a body can name; it is entered
with `none` and still counts as a binder. -/
private def Binders.enter (scope : Binders) (name : Option String) : Binders :=
  match name with
  | some name =>
    { scope with binders := scope.binders.push name, names := scope.names.insert name }
  | none => { scope with binders := scope.binders.push "_" }

/-- The binder a bound variable refers to. -/
private def Binders.binder? (scope : Binders) (index : Nat) : Option String :=
  if index < scope.binders.size then some (scope.binders.get! (scope.binders.size - 1 - index))
  else none

/-- A binder as it is written, and the scope under it. The name is always quoted, so that a
name that is a keyword or has unusual characters is still an identifier, and renamed when an
enclosing binder or a constant already uses it. -/
private def Binders.bind (heads : Std.HashSet String) (scope : Binders) (n : Name) :
    String × Binders := Id.run do
  let raw := n.toString (escape := false)
  let unusable := n.isAnonymous || n.hasMacroScopes || raw.isEmpty ||
    raw.any fun c => c == '»' || c == '\n' || c == '\r'
  let base := if unusable then "x" else raw
  let mut candidate := base
  -- Start after the suffixes already given to this name: many binders of one name do not
  -- each try them all again.
  let mut i := (scope.suffixes.find? base).getD 0
  let mut renamed := false
  while scope.names.contains s!"«{candidate}»" || heads.contains candidate do
    i := i + 1
    candidate := s!"{base}_{i}"
    renamed := true
  let name := s!"«{candidate}»"
  let scope := if renamed then { scope with suffixes := scope.suffixes.insert base i } else scope
  return (name, scope.enter name)

private unsafe def addressImpl (e : Expr) : UInt64 :=
  let mixed := (ptrAddrUnsafe e).toUInt64 * 0x9E3779B97F4A7C15
  (mixed >>> 32) ||| (mixed <<< 32)

/-- A number that tells one expression object from every other while both are alive: its
address in memory, multiplied by an odd constant and with its two halves exchanged, so that
the low bits, which a hash table looks at, differ between neighbouring objects. The tables of
the printer are keyed by it and not by the
expression: comparing two expressions goes through them, and on a chain tens of thousands of
levels deep Lean's hash of an expression repeats, so that every lookup would compare two
chains.

Two keys are equal exactly when the objects are the same, so a table can only miss that two
expressions are equal, never take two different ones for one. Such a miss costs size and
time, not correctness: a subterm is then written out again where it could have been bound
once. `render` makes equal subterms one object first, so there are no misses, and it keeps the
proposition alive while the tables are in use, so no address is given to a second object. -/
@[implemented_by addressImpl] private opaque address (e : Expr) : UInt64

/-- Which of the binders of a chain a term under them refers to. `e` stands under `before` of
them and `offset` binders of its own; the state holds the applications already looked at at
this place of the chain. Each subterm is looked at once, and a subterm that refers to nothing
outside itself is skipped. -/
private partial def markUsed (before : Nat) (e : Expr) (offset : Nat) :
    StateM (Std.HashSet (UInt64 × Nat) × Array Bool) Unit := do
  if e.looseBVarRange ≤ offset then return
  match e with
  | .bvar i =>
    let index := i - offset
    if index < before then modify fun (seen, used) => (seen, used.set! (before - 1 - index) true)
  | .app f a =>
    if (← get).1.contains (address e, offset) then return
    modify fun (seen, used) => (seen.insert (address e, offset), used)
    markUsed before f offset
    markUsed before a offset
  | .lam _ t b _ | .forallE _ t b _ =>
    markUsed before t offset
    markUsed before b (offset + 1)
  | .letE _ t v b _ =>
    markUsed before t offset
    markUsed before v offset
    markUsed before b (offset + 1)
  | .mdata _ e | .proj _ _ e => markUsed before e offset
  | _ => pure ()

/-- Text assembled from parts. A part is not copied into the text it stands in, so writing a
term takes time and memory in the size of the result, however deeply it nests, and a part can
stand in several places. -/
private inductive Text where
  | leaf (text : String)
  | node (parts : Array Text) (bytes : Nat)
deriving Inhabited

private def Text.bytes : Text → Nat
  | .leaf text => text.utf8ByteSize
  | .node _ bytes => bytes

private def Text.join (parts : Array Text) : Text :=
  .node parts (parts.foldl (fun bytes part => bytes + part.bytes) 0)

/-- The parts with `separator` between them. -/
private def Text.intercalate (separator : String) (parts : Array Text) : Text := Id.run do
  let mut joined : Array Text := Array.mkEmpty (2 * parts.size)
  for part in parts do
    unless joined.isEmpty do joined := joined.push (.leaf separator)
    joined := joined.push part
  return .join joined

/-- The text, appended to `out`. -/
private partial def Text.write (out : String) : Text → String
  | .leaf text => out ++ text
  | .node parts _ => parts.foldl Text.write out

/-- `total + bytes`, the length of a text that grows by `bytes`, unless that is more than a
file may hold. It is asked for every part of a long text as the part is written, so that
writing stops at the first part that does not fit. (The passes that come before writing,
preparation and translation, have run by then; `maxPreparedNodes` bounds those.) -/
private def addBytes (limit total bytes : Nat) : Except String Nat :=
  if total + bytes > limit then
    throw s!"The proposition is too large to write: its text is longer than {limit} bytes"
  else pure (total + bytes)

/-- A subterm's text and depth, unless the text is longer than a file may hold. -/
private def fitting (limit : Nat) (text : Text) (depth : Nat) : Except String (Text × Nat) := do
  let _ ← addBytes limit 0 text.bytes
  return (text, depth)

/-- A subterm that occurs more than once in a term and whose text is at least this long is
written once, in a `let`. A shorter one is written out where it stands. -/
private def shareThreshold : Nat := 256

/-- What is known while one term is written, not looking under its binders. -/
private structure Sharing where
  /-- How often each application and each binder expression occurs in the term, by address. -/
  uses : Std.HashMap UInt64 Nat := {}
  /-- The subterms that occur more than once and are written already, with what stands for each
  where it occurs (its text, or the name it is bound to) and how deeply that nests. -/
  written : Std.HashMap UInt64 (Text × Nat) := {}
  /-- The bindings of the subterms that are named, each after those it uses. -/
  bindings : Array Text := #[]
  /-- The length of the bound texts together. -/
  bindingBytes : Nat := 0
  /-- The deepest nesting among the bound texts. -/
  depth : Nat := 0

/-- Count how often each application and each binder expression (a function, a quantification,
a `have`) occurs in `e`. A binder expression counts as a whole and is not entered: under a
binder the same expression can stand for another value. An application met again is counted
and not entered again, so the count takes time in the size of the term as it is shared, not as
it is written out. -/
private partial def countUses (uses : Std.HashMap UInt64 Nat) (e : Expr) :
    Std.HashMap UInt64 Nat :=
  match e with
  | .mdata _ e => countUses uses e
  | .app .. =>
    match uses[address e]? with
    | some n => uses.insert (address e) (n + 1)
    | none => e.getAppArgs.foldl countUses (uses.insert (address e) 1)
  | .lam .. | .forallE .. | .letE .. => uses.insert (address e) (uses.getD (address e) 0 + 1)
  | _ => uses

mutual

/-- An expression as an argument: an atom as it is, anything else in parentheses. Also returns
how deeply the text nests, for the recursion limit the file sets. A subterm that occurs more
than once in the term is written once: where it occurs again, the text of the first time
stands, or the name it was bound to. -/
private partial def argText (heads : Std.HashSet String) (limit : Nat) (scope : Binders)
    (e : Expr) : StateT Sharing (Except String) (Text × Nat) :=
  match e with
  | .bvar i => match scope.binder? i with
    | some name => pure (.leaf name, 1)
    | none => throw "Loose bound variable"
  | .const n ls => do
    let ls ← (ls.mapM levelText : Except String (List String))
    pure (.leaf ("@" ++ n.toString (escape := true) ++
      (if ls.isEmpty then "" else ".{" ++ ", ".intercalate ls ++ "}")), 1)
  | .sort l => do
    if l.isZero then pure (.leaf "Prop", 1) else pure (.leaf s!"(Sort {← levelText l})", 1)
  | .lit (.natVal n) => pure (.leaf s!"(nat_lit {n})", 1)
  | .lit (.strVal s) => pure (.leaf s.quote, 1)
  | .mdata _ e => argText heads limit scope e
  | .app .. | .lam .. | .forallE .. | .letE .. => do
    -- Only a subterm that occurs again is remembered: the text of one that occurs once is part
    -- of the text around it, and keeping every such text would keep the term many times over.
    let shared := (← get).uses.getD (address e) 0 > 1
    if shared then
      if let some known := (← get).written[address e]? then return known
    let (text, depth) ← compoundText heads limit scope e
    unless shared do return (text, depth)
    let state ← get
    let stands ← if text.bytes ≥ shareThreshold then
        let (name, _) := scope.bind heads (Name.mkSimple s!"_s{state.bindings.size + 1}")
        set { state with
          bindings := state.bindings.push (.join #[.leaf s!"let {name} := ", text, .leaf ";"])
          bindingBytes := ← addBytes limit state.bindingBytes text.bytes
          depth := max state.depth depth }
        pure (.leaf name, 1)
      else pure (text, depth)
    modify fun state => { state with written := state.written.insert (address e) stands }
    return stands
  | _ => throw "Unsupported expression"

/-- An application or a binder expression, written out. -/
private partial def compoundText (heads : Std.HashSet String) (limit : Nat) (scope : Binders)
    (e : Expr) : StateT Sharing (Except String) (Text × Nat) :=
  match e with
  | .lam n t b _ => do
    let (x, inner) := scope.bind heads n
    let (t, dt) ← argText heads limit scope t
    let (b, db) ← bodyText heads limit inner b
    fitting limit (.join #[.leaf s!"(fun ({x} : ", t, .leaf ") =>\n", b, .leaf ")"]) (max dt db + 1)
  | .forallE .. | .letE .. => do
    let (text, depth) ← bodyText heads limit scope e
    pure (.join #[.leaf "(", text, .leaf ")"], depth + 1)
  | _ => do
    let (f, depth) ← argText heads limit scope e.getAppFn
    let args := e.getAppArgs
    let mut parts : Array Text := (Array.mkEmpty (2 * args.size + 3)).push (.leaf "(") |>.push f
    let mut depth := depth
    let mut bytes := f.bytes
    for arg in args do
      let (text, d) ← argText heads limit scope arg
      parts := parts.push (.leaf " ") |>.push text
      depth := max depth d
      bytes ← addBytes limit bytes text.bytes
    fitting limit (.join (parts.push (.leaf ")"))) (depth + 1)

/-- A term, with the subterms that occur in it more than once bound by `let` in front of it. A
term that uses a subterm several times (the operand of `abs`, the condition of an `if` in its
instance, an operand of a chain) would otherwise write it out each time, and nesting such
terms would multiply the text. Sharing stops at binders. -/
private partial def termText (heads : Std.HashSet String) (limit : Nat) (scope : Binders)
    (e : Expr) : Except String (Text × Nat) := do
  let ((text, depth), state) ← (argText heads limit scope e).run { uses := countUses {} e }
  if state.bindings.isEmpty then return (text, depth)
  fitting limit
    (.join #[.leaf "(", .intercalate "\n" (state.bindings.push text), .leaf ")"])
    (max depth state.depth + state.bindings.size + 1)

/-- An expression in body position. A chain of quantifiers, premises and `have` bindings is
written one per line, without nesting, so that a long chain stays flat in the text. -/
private partial def bodyText (heads : Std.HashSet String) (limit : Nat) (scope : Binders)
    (e : Expr) : Except String (Text × Nat) := do
  -- The chain, and what follows it.
  let mut links : Array Expr := #[]
  let mut last := e
  repeat
    match last with
    | .mdata _ b => last := b
    | .forallE _ _ b _ | .letE _ _ _ b _ => links := links.push last; last := b
    | _ => break
  -- A quantification whose variable nothing refers to is a premise. A short chain asks each
  -- binder, which looks through all that follows it. A long chain is gone through once:
  -- asking would look through it once per binder. On a short chain the single pass costs
  -- more than asking, and a term with many nested binders has many short chains.
  let mark (used : Array Bool) (before : Nat) (terms : List Expr) : Array Bool :=
    -- What was seen at one place of the chain says nothing at the next: the same expression
    -- means other binders there.
    ((terms.forM fun t => markUsed before t 0).run ({}, used)).2.2
  let mut used := Array.replicate links.size false
  if links.size ≤ 4 then
    for i in [0:links.size] do
      if let Expr.forallE _ _ b _ := links[i]! then used := used.set! i (b.hasLooseBVar 0)
  else
    for i in [0:links.size] do
      match links[i]! with
      | Expr.forallE _ t _ _ => used := mark used i [t]
      | Expr.letE _ t v _ _ => used := mark used i [t, v]
      | _ => pure ()
    used := mark used links.size [last]
  let mut lines : Array Text := Array.mkEmpty (links.size + 1)
  let mut scope := scope
  let mut depth := 0
  let mut bytes := 0
  for i in [0:links.size] do
    let mut line : Text := default
    match links[i]! with
    | .forallE n t _ _ =>
      let (t, d) ← termText heads limit scope t
      depth := max depth d
      if used[i]! then
        let (x, inner) := scope.bind heads n
        line := .join #[.leaf s!"∀ ({x} : ", t, .leaf "),"]
        scope := inner
      else
        line := .join #[t, .leaf " →"]
        scope := scope.enter none
    | .letE n t v _ nondep =>
      let (x, inner) := scope.bind heads n
      let (t, dt) ← termText heads limit scope t
      let (v, dv) ← termText heads limit scope v
      depth := max depth (max dt dv)
      line := .join #[
        .leaf s!"{if nondep then "have" else "let"} {x} : ", t, .leaf " := ", v, .leaf ";"]
      scope := inner
    | _ => continue
    lines := lines.push line
    bytes ← addBytes limit bytes line.bytes
  let (final, d) ← termText heads limit scope last
  -- Lean elaborates a chain by recursion, one level per line.
  fitting limit (.intercalate "\n" (lines.push final)) (max depth d + lines.size)

end

/-- The text of a closed proposition, and how deeply it nests; an error when the text would be
longer than `limit` bytes. Equal subterms are made one object first, which is what lets the
printer's tables go by `address`. -/
private def render (limit : Nat) (e : Expr) : Except String (String × Nat) := do
  let e := ShareCommon.shareCommon' e
  let (text, depth) ← bodyText (constantHeads e) limit {} e
  return (text.write "", depth)

/-- The answer that a validity result of the per-obligation path stands for. An error result
is a timeout when its message says so, although Core reports it as a solver error: a check the
solver gave up on for time is undecided, and belongs to the default scope. -/
def Answer.ofResult : Imperative.SMT.Result Core.Expression.Ident → Answer
  | .unsat => .proved
  | .sat _ => .refuted
  | .unknown _ => .unknown
  | .err message => match Imperative.SMT.failureOfMessage message with
    | .timeout _ => .timeout
    | _ => .error

/-- The answer for the decision of a solver session that walks several checks. -/
def Answer.ofSessionDecision : Strata.SMT.Decision → Answer
  | .unsat => .provedInSession
  | .sat => .refuted
  | .unknown => .unknown
  | .timeout => .timeout

/-- The solver's answer, as the file's header reports it. -/
private def Answer.text : Answer → String
  | .proved => "unsat (the solver found the query valid)"
  | .provedInSession => "unsat (in a solver session that may hold more than this query states)"
  | .refuted => "sat (the solver found a counterexample)"
  | .unknown => "unknown"
  | .timeout => "timeout"
  | .error => "error"
  | .notAsked => "not asked"

/-- A label as part of a file name: every character other than an ASCII letter or digit, `_`,
`-` and `.` becomes `_`; a name that would start with `.` or `-`, or be empty, gets `vc` in front,
so that it is neither hidden nor read as an option; and the first 96 characters are kept. -/
private def fileStem (label : String) : String :=
  let kept := label.map fun c => if c.isAlphanum || c == '_' || c == '-' || c == '.' then c else '_'
  let kept :=
    if kept.startsWith "." || kept.startsWith "-" || kept.isEmpty then "vc" ++ kept else kept
  (kept.take 96).toString

/-- Lean's default recursion limit. -/
private def defaultRecursionLimit : Nat := 512

/-- A proposition longer than this, in bytes, is given all the time Lean needs to read it. -/
private def largeProposition : Nat := 65536

/-- The exported file: the proposition as a definition, and a theorem whose proof is left
open. A proposition that nests deeper than Lean's default recursion limit allows gets a
higher limit, for the whole file. The header's answer is that of the run that writes the
file. -/
private def fileText (label answer proposition : String) (depth : Nat) : String :=
  let label := label.map fun c => if c == '\n' || c == '\r' then ' ' else c
  let limit := 8 * depth + 256
  let recursion := if limit ≤ defaultRecursionLimit then ""
    else s!"set_option maxRecDepth {limit}\n"
  -- Lean gives up on a declaration that takes it too long; a large proposition takes long,
  -- as a definition and as the statement of the theorem.
  let patience := if proposition.utf8ByteSize ≤ largeProposition then ""
    else "set_option maxHeartbeats 0 in\n"
  s!"-- Strata verification condition: {label}\n\
     -- Solver's answer: {answer}\n\
     -- `vcProp` is Strata's translation to Lean of the query it builds for the solver for this\n\
     -- condition: for every interpretation of its declared symbols and every value of a\n\
     -- division or modulo by zero (`divByZero`, `modByZero`, bound when it has a div or mod),\n\
     -- the assumptions imply the goal. A proof of `vc` shows the condition as far as that\n\
     -- translation is faithful, which is tested and reviewed, not proved (docs/LeanExport.md).\n\
     -- The proposition is written out in full, with every type, instance and literal explicit,\n\
     -- so that Lean reads back the expression Strata built, up to the names of binders. After\n\
     -- `unfold vcProp` the goal is displayed in the usual notation. Definitions are `have`\n\
     -- bindings, and a long subterm that occurs several times in a term is bound once by a\n\
     -- `let`; `dsimp only` unfolds both into the goal, which some tactics (`omega`) need.\n\
     {recursion}\
     {patience}\
     set_option linter.unusedVariables false in\n\
     def vcProp : Prop :=\n\
     {proposition}\n\n\
     {patience}\
     theorem vc : vcProp := by\n  unfold vcProp\n  sorry\n"

/-- Publish the fully written file `staged` under the name `file`, unless a file of that name
exists. The name is given by a hard link, which fails when the name exists, whoever created
it and however shortly before, and otherwise makes the file appear under that name at once,
complete. Returns whether the file was published. Either way the removal of `staged` is
attempted and an existing file is untouched; when the link fails for another reason (the
directory is on a file system without hard links, for one), nothing is left under `file`. -/
def publish (staged file : System.FilePath) : IO Bool := do
  let outcome ← (IO.FS.hardLink staged file).toBaseIO
  try IO.FS.removeFile staged catch _ => pure ()
  match outcome with
  | .ok () => return true
  | .error (.alreadyExists ..) => return false
  | .error error => throw <| .userError s!"The file cannot be published by a hard link: {error}"

/-- Create the file `path` with the text `text`, unless a file of that name exists; returns
whether it was created. The file is closed when this returns. After an error no file of this
function's making is left: when the file cannot be created there is none, and when the text
cannot be written the file is removed. -/
private def writeNew (path : System.FilePath) (text : String) : IO Bool := do
  let handle ← try IO.FS.Handle.mk path .writeNew catch
    | .alreadyExists .. => return false
    | error => throw error
  try
    handle.putStr text
    handle.flush
  catch error =>
    try IO.FS.removeFile path catch _ => pure ()
    throw error
  return true

/-- Numbers the files this process is writing, so that no two of them share a name. -/
private initialize stagedFiles : IO.Ref Nat ← IO.mkRef 0

/-- Write the validity query of one check as a Lean theorem file, when the scope covers the
solver's `answer` to it. Nothing is returned, and nothing the caller reports depends on it. A
query that is not translated, and a write that fails or does not read back, are reported to
the observer and leave no file. (The read-back goes through the system's cache and nothing
is synced: a file system that takes a text into its cache and cannot store it later may go
unnoticed.) The file name is the label and a hash of the proposition, so it does not depend on the
order in which checks finish. A file that exists is never overwritten (stage `kept`): its
name says that it states the same theorem, and its proof may have been filled in. -/
def ExportConfig.exportValidity (config : ExportConfig) (answer : Answer)
    (context : Core.SMT.Context) (assumptions : List Strata.SMT.Term)
    (goal : Strata.SMT.Term) (definitions : List Core.VarDefinition)
    (declarations : List Core.VarDeclaration) (label : String) : IO Unit := do
  unless config.scope.covers answer do return
  -- An observer that fails stops nothing.
  let report (event : Event) : IO Unit := try config.observe event catch _ => pure ()
  let rendered ← (do
    match prepareClosed context assumptions goal definitions declarations with
    | .ok query => IO.ofExcept (render config.maxFileBytes query.validity)
    | .error message => throw <| .userError (← message.toString) : IO (String × Nat)).toBaseIO
  let .ok (proposition, depth) := rendered
    | if let .error error := rendered then
        report { label, stage := .preparationFailure, diagnostic := toString error }
  let outcome ← (do
    IO.FS.createDirAll config.directory
    let name := s!"{fileStem label}_{(hash proposition).toBitVec.toHex}.lean"
    let file := config.directory / name
    -- Looked for first, so that a check exported before costs no write.
    if ← file.pathExists then return (false, file)
    -- Written under a name of its own and then published, so a reader never sees a file
    -- half written and two workers exporting the same proposition do not interleave.
    let serial ← stagedFiles.modifyGet fun n => (n, n + 1)
    let staged := config.directory /
      s!".{name}.{← IO.Process.getPID}_{serial}_{← IO.monoNanosNow}.tmp"
    let text := fileText label answer.text proposition depth
    let discardStaged : IO Unit := try IO.FS.removeFile staged catch _ => pure ()
    -- A file of that name that exists is another writer's, and stays.
    unless ← writeNew staged text do
      throw <| .userError s!"The staging name {staged} is taken"
    -- Read back before it is published: a disk without room can show only when the file is
    -- closed, which Lean does not report, and would leave a short file under the name.
    let readBack ← try IO.FS.readFile staged catch error => discardStaged; throw error
    unless readBack == text do
      discardStaged
      throw <| .userError "The file system did not keep the text of the file"
    return (← publish staged file, file) : IO (Bool × System.FilePath)).toBaseIO
  match outcome with
  | .ok (published, file) =>
    report { label, stage := if published then .exported else .kept, file := some file }
  | .error error => report { label, stage := .writeFailure, diagnostic := toString error }

/-- `exportValidity` for a check of a program, unless a variable the check declares or defines
has the name of a function (`functionAmong` finds one among the names it is given). The
context of such a check can have one symbol for the two (it does for a function without
parameters and of the variable's sort), and its terms then do not tell them apart, so the
file would state another condition than the check's. Such a check, when the scope covers
it, is reported as not prepared. Strata's type checker rejects a procedure whose parameter or
local variable has a function's name; a variable that a phase introduces (a common
subexpression) can still meet a function of its name. -/
def ExportConfig.exportCheck (config : ExportConfig)
    (functionAmong : List String → Option String)
    (answer : Answer) (context : Core.SMT.Context) (assumptions : List Strata.SMT.Term)
    (goal : Strata.SMT.Term) (definitions : List Core.VarDefinition)
    (declarations : List Core.VarDeclaration) (label : String) : IO Unit := do
  unless config.scope.covers answer do return
  match functionAmong (declarations.map (·.name) ++ definitions.map (·.name)) with
  | some name =>
    let diagnostic := s!"'{name}' is the name of a function and of a variable of the check"
    try config.observe { label, stage := .preparationFailure, diagnostic } catch _ => pure ()
  | none => config.exportValidity answer context assumptions goal definitions declarations label

end Core.LeanExport
