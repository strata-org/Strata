/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.StringLit
import Strata.DL.SMT.Symbol
import StrataDDM.Elab
public import Strata.Pipeline.Context
public import Strata.DL.Imperative.EvalContext
public import Strata.DL.SMT.Encoder
public import Strata.DL.SMT.IncrementalSolver
public import Strata.DL.SMT.VerdictReader
public import Strata.Util.ListMapProps
public import Strata.Languages.Core.Options

namespace Imperative
open Std (ToFormat Format format)

namespace SMT

public section
---------------------------------------------------------------------

/--
A model derived from an SMT solver is a map from an identifier
to an `SMT.Term`.
-/
abbrev Model (Ident : Type) := Map Ident Strata.SMT.Term

/-- Backward-compatible alias. -/
@[deprecated Model (since := "2026-04-03")] abbrev CounterEx := @Model

/-- Render an `SMT.Term` to a string via the SMTDDM translation. -/
private def termToString (t : Strata.SMT.Term) : String :=
  match Strata.SMTDDM.termToString t with
  | .ok s => s
  | .error _ => repr t |>.pretty

def Model.format {Ident} [ToFormat Ident] (m : Model Ident) : Format :=
  match m with
  | [] => ""
  | [(id, v)] => f!"({id}, {termToString v})"
  | (id, v) :: rest =>
    (f!"({id}, {termToString v}) ") ++ Model.format rest

instance {Ident} [ToFormat Ident] : ToFormat (Model Ident) where
  format := Model.format

/--
Result from an SMT solver.
-/
inductive Result (Ident : Type) where
  -- Also see Strata.SMT.Decision.
  | sat (model : Model Ident)
  | unsat
  | unknown (candidateModel : Option (Model Ident) := none)
  | err (msg : String)
  deriving DecidableEq, Repr

def Result.isSat {T} (r : Result T) : Bool :=
  match r with | .sat _ => true | _ => false

def Result.formatWithVerbose {Ident} [ToFormat Ident]
  (r : Result Ident) (verbose : Bool) : Format :=
  match r with
  | .sat m  =>
    if (not verbose) || m.isEmpty then
      f!"sat"
    else f!"sat\nModel: {m}"
  | .unsat => f!"unsat"
  | .unknown m =>
    match m with
    | some model =>
      if (not verbose) || model.isEmpty then
        f!"unknown"
      else f!"unknown\nCandidate model: {model}"
    | none => f!"unknown"
  | .err msg => f!"err {msg}"

instance {Ident} [ToFormat Ident]: ToFormat (Result Ident) where
  format r := r.formatWithVerbose true

def Result.formatModelIfSat {Ident} [ToFormat Ident]
  (r : Result Ident) (verbose : Bool) : Format :=
  match r with
  | .sat m =>
    if (not verbose) || m.isEmpty then
      f!""
    else
      f!"\nModel:\n{m}"
  | _ => f!""


/--
Find the Id for the SMT encoding of the variable `x` in the SMT encoder state `E`.
-/
def getSMTId {Ident Ty} [ToFormat Ident]
    (typedVarToSMTFn : Ident → Ty → Except Format (String × Strata.SMT.TermType))
    (x : Ident) (ty : Option Ty) (E : Strata.SMT.EncoderState) :
    Except Format String := do
  match (x, ty) with
  | (var, none) => .error f!"Expected variable {var} to be annotated with a type!"
  | (var, some ty) => do
    let (var', ty') ← typedVarToSMTFn var ty
    let key : Strata.SMT.UF := { id := var', args := [], out := ty' }
    match E.functions[key]? with
    | some id => .ok id
    | none => .error f!"Variable {var} (SMT name: {var'}) not found in encoder state"

def runSolver (solver : String) (args : Array String) : IO IO.Process.Output := do
  let output ← IO.Process.output {
    cmd := solver
    args := args
  }
  -- dbg_trace f!"runSolver: exitcode: {repr output.exitCode}\n\
  --                         stderr: {repr output.stderr}\n\
  --                         stdout: {repr output.stdout}"
  return output

/-- The validity verdict after a retry: the retry's when it is `unsat`, the first otherwise. A
    retried `sat` keeps the first `unknown` (and its candidate model), so a retry can turn an
    `unknown` into a proof and never into a refutation. This holds for any retry of the same
    validity query, whatever solver options the retry adds. -/
def retryVerdict {Ident : Type} (first retried : Result Ident) : Result Ident :=
  match retried with
  | .unsat => .unsat
  | _ => first

/-- Whether cvc5's output for `(get-info :reason-unknown)` says `incomplete`: some line of the
    output is exactly that response, so the same text inside a model or a message does not
    count. -/
def reasonUnknownIsIncomplete (stdout : String) : Bool :=
  (stdout.splitOn "\n").any fun l => l.trimAscii.toString == "(:reason-unknown incomplete)"

/-- Runs a best-effort step `act` (the retry); if it throws, `first` stands. -/
def orFirst {α : Type} (first : α) (act : IO α) : IO α :=
  try act catch _ => pure first

/-- A path beside `filename`, hidden and unique to this call, for a query a solver is about to
    read. It keeps the `.smt2` extension, by which solvers recognize the input language. Its name
    has a fixed length, independent of `filename`, so it is valid wherever `filename` is. Any
    later read of the query, such as a second solver run on it, must use this path and not the
    public name, which another run may have written meanwhile. -/
private def privateQueryPath (filename : String) : IO System.FilePath := do
  let nonce := (← IO.getRandomBytes 8).foldl (fun n b => n * 256 + b.toNat) 0
  let hex := String.ofList (Nat.toDigits 16 nonce)
  let path : System.FilePath := filename
  return path.withFileName s!".strata-{"".pushn '0' (16 - hex.length)}{hex}.smt2"

/-- Runs `solver` on `text`, written to a file private to this call beside `name` (see
    `privateQueryPath`), which is removed afterwards. A file this call did not create, because
    its name was taken, is someone else's and is left alone. -/
def runSolverOnText (solver name text : String) (args : Array String) :
    IO IO.Process.Output := do
  let path ← privateQueryPath name
  let created ← IO.mkRef false
  try
    IO.FS.withFile path .writeNew fun h => do
      created.set true
      h.putStr text
    runSolver solver (#[path.toString] ++ args)
  finally
    if ← created.get then try IO.FS.removeFile path catch _ => pure ()

/-- The query file without its satisfiability check, or `none` if the check block is not found.
    The cut removes the lines from the last `; Satisfiability` comment line up to the one
    `; Validity` comment line after it (both written by `writeCheckSatBlock`). The check block
    follows every declaration, so a declaration comment that repeats a marker (a constant named
    `Validity`) does not move the cut. The removed check is a `check-sat-assuming`, which asserts
    nothing, so the remaining validity check asks the same question. -/
def validityCheckOnly (text : String) : Option String :=
  let sat := "\n; Satisfiability\n"
  let val := "\n; Validity\n"
  match text.splitOn sat |>.reverse with
  | after :: rest@(_ :: _) =>
    match after.splitOn val with
    | [_, tail] => some (sat.intercalate rest.reverse ++ val ++ tail)
    | _ => none
  | _ => none

/-- Whether the solver's last answer on the query `text` written for `filename` (its validity
    check) was `unknown` for `incomplete`: the query is rerun with `(get-info :reason-unknown)`
    appended. Only cvc5 is asked; any other solver gives `false`. -/
def reasonIsIncomplete (solver filename text : String) (args : Array String) : IO Bool := do
  if solver != "cvc5" then return false
  -- The last check in the file is the validity check (`writeCheckSatBlock` writes the
  -- satisfiability check first when both run), so `:reason-unknown` refers to it.
  let out ← runSolverOnText solver (filename ++ ".reason.smt2")
    (text ++ "\n(get-info :reason-unknown)\n") args
  return reasonUnknownIsIncomplete out.stdout

/-- Classifies a per-obligation encoding or solver failure. -/
inductive SolverError where
  | encoding (error : Strata.SMT.StringLit.EncodingError)
  | timeout (detail : String)
  | crash (detail : String)

instance : ToString SolverError where
  toString
    | .encoding e => toString e
    | .timeout d => s!"Solver timeout: {d}"
    | .crash d   => s!"Solver crash: {d}"

/-- True when the word "timeout" appears as a whitespace-delimited token
    in the solver's stdout or stderr. z3 emits "timeout" as a standalone
    line on stdout; cvc5 prints "interrupted by timeout." on stderr.
    Only called when verdict parsing has already failed. -/
private def isTimeoutOutput (output : IO.Process.Output) : Bool :=
  let hasWord (s : String) := s.splitOn "\n" |>.any fun line =>
    line.splitOn " " |>.any fun tok =>
      tok.trimAscii.toString == "timeout" || tok.trimAscii.toString == "timeout."
  hasWord output.stdout || hasWord output.stderr

/-- A live solver's failure, by the words of its message: a timeout when they say so, else a
    crash, which is how the path that writes the query to a file reads a solver's output. -/
def failureOfMessage (detail : String) : SolverError :=
  if isTimeoutOutput { exitCode := 0, stdout := detail, stderr := "" } then .timeout detail
  else .crash detail

---------------------------------------------------------------------
-- SMTDDM-based parsing
---------------------------------------------------------------------

/-- The value and width of an SMT-LIB `#b`/`#x` literal's digits (`binary`: one bit
    per digit; otherwise hexadecimal: four), or `none` if a digit is out of range. -/
private def bvLiteralValue (binary : Bool) (digits : List Char) : Option (Nat × Nat) :=
  let digitVal (c : Char) : Option Nat :=
    if binary then
      if c == '0' then some 0 else if c == '1' then some 1 else none
    else hexDigitValue? c
  let base := if binary then 2 else 16
  let bitsPerDigit := if binary then 1 else 4
  let value := digits.foldlM (init := 0) fun acc c => (digitVal c).map (acc * base + ·)
  value.map fun v => (v, digits.length * bitsPerDigit)

/-- Where a left-to-right scan of a solver response is: outside string literals and quoted
    symbols, inside a string literal (`"…"`), or inside a quoted symbol (`|…|`). -/
inductive ResponseScan where
  | code
  | str
  | quoted

/-- A piece of a solver response: text outside string literals and quoted symbols (`code`), a
    string literal with its quotes (`str`, in which `""` is an escaped quote), or a quoted
    symbol with its bars (`quoted`). A response that ends inside a literal ends with a `str` or
    `quoted` piece that lacks its closing quote or bar. -/
inductive ResponseSegment where
  | code (text : String)
  | str (text : String)
  | quoted (text : String)

/-- The text of a piece of a solver response. -/
def ResponseSegment.text : ResponseSegment → String
  | .code t | .str t | .quoted t => t

/-- Whether a piece of a solver response is outside string literals and quoted symbols. -/
def ResponseSegment.isCode : ResponseSegment → Bool
  | .code _ => true
  | _ => false

/-- The pieces of a solver response, in order: their texts concatenate to the response, and
    every string literal and quoted symbol is a piece of its own. -/
def responseSegments (s : String) : List ResponseSegment :=
  (go .code "" #[] s.toList).toList
where
  /-- `out` followed by the pieces of the rest of the response, the scan being at the given
      `ResponseScan` with the text `acc` of the current piece read so far. -/
  go : ResponseScan → String → Array ResponseSegment → List Char → Array ResponseSegment
    | .code, acc, out, [] => out.push (.code acc)
    | .str, acc, out, [] => out.push (.str acc)
    | .quoted, acc, out, [] => out.push (.quoted acc)
    | .str, acc, out, '"' :: '"' :: rest => go .str ((acc.push '"').push '"') out rest
    | .str, acc, out, '"' :: rest => go .code "" (out.push (.str (acc.push '"'))) rest
    | .str, acc, out, c :: rest => go .str (acc.push c) out rest
    | .quoted, acc, out, '|' :: rest => go .code "" (out.push (.quoted (acc.push '|'))) rest
    | .quoted, acc, out, c :: rest => go .quoted (acc.push c) out rest
    | .code, acc, out, '"' :: rest => go .str "\"" (out.push (.code acc)) rest
    | .code, acc, out, '|' :: rest => go .quoted "|" (out.push (.code acc)) rest
    | .code, acc, out, c :: rest => go .code (acc.push c) out rest
  termination_by _ _ _ l => l.length

/-- Apply `f` to every piece of a solver response outside string literals and quoted symbols
    (`responseSegments`), copying string literals and quoted symbols unchanged. -/
def rewriteResponseCode (f : String → String) (s : String) : String :=
  (responseSegments s).foldl (init := "") fun acc seg =>
    acc ++ if seg.isCode then f seg.text else seg.text

/-- The characters of a solver response, each with whether it lies outside string literals and
    quoted symbols (`responseSegments`). -/
def responseChars (s : String) : List (Char × Bool) :=
  (responseSegments s).flatMap fun seg => seg.text.toList.map (·, seg.isCode)

/-- Rewrite every SMT-LIB bitvector literal `#b…`/`#x…` of a solver response into the
    indexed form `(_ bvV W)` the SMTResponse dialect parses (`#b`/`#x` are not tokens
    of it). String literals (`"…"`, with `""` as the escaped quote) and quoted symbols
    (`|…|`) are copied unchanged. This works around the SMT dialect's missing literal syntax
    (`Strata/DL/SMT/DDMTransform/Parse.lean`, the token list: `<hexadecimal> and <binary> are
    not available yet`). -/
def rewriteBVLiterals (s : String) : String :=
  rewriteResponseCode (go "" ·.toList) s
where
  /-- `acc` followed by the rewrite of the rest of a piece outside string literals and quoted
      symbols. -/
  go : String → List Char → String
    | acc, [] => acc
    | acc, '#' :: k :: rest =>
      if k == 'b' || k == 'x' then
        let digits := rest.takeWhile Char.isAlphanum
        match bvLiteralValue (k == 'b') digits with
        | some (v, w) =>
          if digits.isEmpty then go (acc.push '#') (k :: rest)
          else go (acc ++ s!"(_ bv{v} {w})") (rest.drop digits.length)
        | none => go (acc.push '#') (k :: rest)
      else go (acc.push '#') (k :: rest)
    | acc, c :: rest => go (acc.push c) rest
  termination_by _ l => l.length
  decreasing_by all_goals simp only [List.length_cons, List.length_drop] <;> omega

/-- A character that ends a bare symbol of a solver response. -/
def isResponseDelim (c : Char) : Bool := c == '(' || c == ')' || c == ' ' || c == '\n' ||
  c == '\t' || c == '\r' || c == '"' || c == '|'

/-- Quote every bare symbol of a solver response that starts with `@` (`@S_0` =>
    `|@S_0|`). SMT-LIB reserves a leading `@` for solver-invented symbols, which cvc5
    uses to name the elements of an uninterpreted sort, and the SMTResponse dialect
    reads `@` only as a reserved word, so a bare one fails to parse and drops the whole
    model; a quoted one parses as a symbol. A `@` that does not start a symbol (as in
    `x@1`), string literals and already-quoted symbols are copied unchanged. This works
    around the SMT dialect's symbol syntax (`Strata/DL/SMT/DDMTransform/Parse.lean`: the
    `("at", "@")` entry of `specialCharsInSimpleSymbol`, and the `<symbol>` TODO `Support
    quoted symbols`). -/
def quoteSolverSymbols (s : String) : String :=
  rewriteResponseCode (go true "" ·.toList) s
where
  /-- `acc` followed by the rewrite of the rest of a piece outside string literals and quoted
      symbols; the `Bool` says whether the next character begins a token. -/
  go : Bool → String → List Char → String
    | _, acc, [] => acc
    | start, acc, '@' :: rest =>
      if start then
        let sym := rest.takeWhile (fun c => !isResponseDelim c)
        go false ((acc ++ "|@" ++ String.ofList sym).push '|') (rest.drop sym.length)
      else go false (acc.push '@') rest
    | _, acc, c :: rest => go (isResponseDelim c) (acc.push c) rest
  termination_by _ _ l => l.length
  decreasing_by all_goals simp only [List.length_cons, List.length_drop] <;> omega

/-- Quote every bare `/` token of a solver response (`/` becomes `|/|`). A solver prints a
    non-integral real as `(/ p q)`, and the SMTResponse dialect does not read `/` as a
    symbol, so a bare one fails to parse and drops the whole model; a quoted one parses
    as the symbol `/`. A `/` inside a longer symbol, string literals and quoted symbols
    are copied unchanged. This works around the SMT dialect's symbol syntax
    (`Strata/DL/SMT/DDMTransform/Parse.lean`: the `("slash", "/")` entry left out of
    `specialCharsInSimpleSymbol`). -/
def quoteDivisionSymbol (s : String) : String :=
  rewriteResponseCode (go true "" ·.toList) s
where
  /-- `acc` followed by the rewrite of the rest of a piece outside string literals and quoted
      symbols; the `Bool` says whether the next character begins a token. -/
  go : Bool → String → List Char → String
    | _, acc, [] => acc
    | start, acc, '/' :: rest =>
      if start && rest.head?.all isResponseDelim then go false (acc ++ "|/|") rest
      else go false (acc.push '/') rest
    | _, acc, c :: rest => go (isResponseDelim c) (acc.push c) rest

/-- The parenthesized items directly inside the first parenthesized list of a solver
    response, as strings: `((x 1) (y 2))` becomes `["(x 1)", "(y 2)"]`. Parentheses inside
    string literals and quoted symbols (`responseChars`) do not count, and everything after
    the first list is ignored. -/
def valuationPairStrings (s : String) : List String := Id.run do
  let mut depth := 0
  let mut current : List Char := []
  let mut items : Array String := #[]
  for (c, code) in responseChars s do
    let before := depth
    if code then
      if c == '(' then depth := depth + 1
      else if c == ')' then
        depth := depth - 1
        if before == 1 then break
    if before ≥ 2 || depth ≥ 2 then current := c :: current
    if before ≥ 2 && depth == 1 then
      items := items.push (String.ofList current.reverse)
      current := []
  return items.toList

/-- The lines of a solver response (split at every `\n`), each with the `responseChars` of its
    characters and whether it starts outside string literals and quoted symbols. -/
def responseLines (s : String) : List (List (Char × Bool) × Bool) :=
  let (lines, line, start) := (responseChars s).foldl (init := (#[], #[], true))
    fun (lines, line, start) (c, code) =>
      if c == '\n' then (lines.push (line.toList, start), #[], code)
      else (lines, line.push (c, code), start)
  (lines.push (line.toList, start)).toList

/-- The lines of a solver response before its first verdict line: a line that is `sat`, `unsat`
    or `unknown` up to surrounding whitespace and starts outside every parenthesis, string
    literal and quoted symbol (`responseLines`). This is the part of the output that answers
    the current check, when the output goes on with the verdict and model of a later check; a
    line of a model value that reads like a verdict does not end it. -/
def beforeVerdictLine (s : String) : String := Id.run do
  let mut depth := 0
  let mut kept : Array String := #[]
  for (l, start) in responseLines s do
    let text := String.ofList (l.map (·.1))
    let t := text.trimAscii.toString
    if depth == 0 && start && (t == "sat" || t == "unsat" || t == "unknown") then break
    kept := kept.push text
    for (c, code) in l do
      if code then
        if c == '(' then depth := depth + 1
        else if c == ')' then depth := depth - 1
  return "\n".intercalate kept.toList

/--
Parse a `(get-value ...)` model response using the SMTResponse DDM dialect.
Uses `parseCategoryFromDialect` targeting `SMTResponse.GetValueResponse`
directly, which avoids the ambiguity that arises when parsing at the
`Command` level.

Returns the (key-string, value-Term) pairs, or a message saying why the response could not
be read.

The response dialect installs an SMT-LIB decoder for its `Str` category, so the parser
handles the response structure first and string values reach the term translation already
decoded.

`declaredNames` are the names the program already uses. A symbol the solver
invented for an element of an uninterpreted sort is renamed if it would collide
with one of them; see `Strata.SMT.Symbol.ofSolverSymbol`.

A response that does not parse as a whole is parsed one valuation pair at a time
(`valuationPairStrings`), so a pair the dialect cannot read loses only its own
binding. Only the text before the next verdict line (`beforeVerdictLine`) is read this way,
so the model of a later check in the same output is never taken for this one.
-/
def parseModelDDMExcept (modelStr : String) (declaredNames : Std.HashSet String := {}) :
    IO (Except String (List (String × Strata.SMT.Term))) := do
  let text := quoteSolverSymbols (quoteDivisionSymbol (rewriteBVLiterals modelStr))
  match ← parsePairs text with
  | .ok pairs => return .ok pairs
  | .error e =>
    let pairs ← (valuationPairStrings (beforeVerdictLine text)).flatMapM fun pair =>
      return (← parsePairs s!"({pair})").toOption.getD []
    return if pairs.isEmpty then .error e else .ok pairs
where
  /-- The pairs of one response, or why it does not parse. -/
  parsePairs (text : String) : IO (Except String (List (String × Strata.SMT.Term))) := do
    let inputCtx := StrataDDM.Parser.stringInputContext "solver-model" text
    let op ←
      try StrataDDM.Elab.parseCategoryFromDialect
            Strata.SMTResponseDDM.smtResponseDialects q`SMTResponse.GetValueResponse inputCtx
      catch e =>
        return .error s!"the response does not parse as a (get-value ...) response: {e}"
    match Strata.SMTResponseDDM.GetValueResponse.ofAst op with
    | .ok (.get_value_response _ vps) =>
      let pairs ← vps.val.toList.filterMapM fun vp =>
        match vp with
        | .valuation_pair _ t1 t2 => do
          match Strata.SMTResponseDDM.translateFromDDMTermToUntyped t2 declaredNames with
          | .ok t2' =>
            return .some
              (Strata.SMTResponseDDM.formatArg (.op (Strata.SMTResponseDDM.Term.toAst t1)), t2')
          | .error _ =>
            -- The model has an SMT expression (e.g., (lambda ...)) which cannot
            -- be represented in Strata.SMT.Term. Filter out this variable from
            -- the model.
            return .none
      return .ok pairs
    | .error _ =>
      return .error "the response parses but is not a (get-value ...) valuation list"

/--
Return true when a solver response carries no `(get-value …)` valuation to parse.

Empty output, an SMT-LIB `(error …)` response, and a bare verdict token can all represent
the absence of a model. Classifying them before parsing prevents a missing model from
being reported as a malformed counterexample.
-/
def noModelOffered (modelStr : String) : Bool :=
  let t := modelStr.trimAscii.toString
  t.isEmpty || t.startsWith "(error" || (Strata.SMT.decodeVerdict t.toList).isSome

/--
Best-effort parsing for solver-result paths where model absence must not change the verdict.
Returns an empty model when no model was offered or the response cannot be read. Call
`parseModelDDMExcept` when the caller needs the parse failure.
-/
def parseModelDDM (modelStr : String) (declaredNames : Std.HashSet String := {}) :
    IO (List (String × Strata.SMT.Term)) := do
  if noModelOffered modelStr then return []
  match ← parseModelDDMExcept modelStr declaredNames with
  | .ok pairs => return pairs
  | .error _ => return []

/-- The values of a parsed model, keyed by the unescaped name each key maps back to with
    `Strata.SMT.Symbol.ofSMTString`; for a name given twice, the first pair wins. -/
def modelValues (pairs : List (String × Strata.SMT.Term)) :
    Std.HashMap String Strata.SMT.Term :=
  pairs.foldr (fun p m => m.insert (Strata.SMT.Symbol.ofSMTString p.fst) p.snd) {}

/--
Process a parsed model (list of key-string / value-Term pairs) against the
expected variables, matching each variable's SMT-encoded name to its
value in the model. A variable with no SMT encoding or no value in `pairs` is
left out of the result; the other variables keep their values. The result is an
error only when `vars` is not empty and none of its variables has a value.

The keys of `pairs` are escaped spellings, since the solver echoes what the emitter
wrote through `Strata.SMT.Symbol.toSMTString`, while the `id` from `getSMTId` is the
unescaped name. `modelValues` maps each key back once, so each variable is a lookup.
-/
def processModel {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (pairs : List (String × Strata.SMT.Term))
    (E : Strata.SMT.EncoderState) : Except Format (Model P.Ident) :=
  let values := modelValues pairs
  let model := vars.filterMap fun (var, ty) =>
    ((@getSMTId P.Ident P.Ty _ typedVarToSMTFn var ty E).toOption.bind (values[·]?)).map (var, ·)
  if model.isEmpty && !vars.isEmpty then .error f!"No model value for any of {vars.length} ids"
  else .ok model

/-- The `check-sat` answer at the start of `input`: its first line, decoded
    (`Strata.SMT.splitFirstLine`), with the text after that line, where the answer's `get-value`
    response starts. `none` when the line is not an answer. -/
def answerAt (input : String) : Option (Strata.SMT.Decision × String) :=
  match Strata.SMT.splitFirstLine input.toList with
  | (some .timeout, _) | (none, _) => none
  | (some d, rest) => some (d, String.ofList rest)

/-- The satisfiability check's answer when it is asked (`answerAt`), with the text where the
    validity check's answer is read: after the responses that follow the satisfiability answer
    (`Strata.SMT.dropToVerdict`). A check not asked reads nothing. -/
def readSatAnswer (stdout : String) (satisfiabilityCheck : Bool) :
    Option (Option (Strata.SMT.Decision × String) × String) :=
  if satisfiabilityCheck then
    (answerAt stdout).map fun (d, rest) =>
      (some (d, rest), String.ofList (Strata.SMT.dropToVerdict 0 .code rest.toList))
  else some (none, stdout)

/-- The validity check's answer when it is asked: the answer at the start of `remaining`
    (`answerAt`). A check not asked reads nothing. -/
def readValidityAnswer (remaining : String) (validityCheck : Bool) :
    Option (Option (Strata.SMT.Decision × String)) :=
  if validityCheck then (answerAt remaining).map some else some none

/-- A check's result from its answer and the model that follows it, if any: `sat` and
    `unknown` carry the model, `unsat` none. -/
def Result.ofAnswer {Ident : Type} : Strata.SMT.Decision → Option (Model Ident) → Result Ident
  | .sat, m => .sat (m.getD [])
  | .unknown, m => .unknown m
  | .unsat, _ => .unsat
  | .timeout, _ => .unknown

/--
Interprets the output of SMT solver.

When two-sided checking is enabled, the solver output contains two verdict lines:
the first is the satisfiability check result (can the property be true?),
and the second is the validity check result (can the property be false?).
The satisfiability result is returned as the first element of the pair;
the validity result is the second element.

When only one check is enabled, the other is returned as `unknown`.

The first verdict must be the first line of the output: anything else there is an error, not
something to skip. Each later verdict is read after the responses that follow the previous one
(see `Strata.SMT.dropToVerdict`).
-/
def solverResult {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (output : IO.Process.Output)
    (E : Strata.SMT.EncoderState) (smtsolver : String)
    (satisfiabilityCheck validityCheck : Bool)
    : IO (Except SolverError (Result P.Ident × Result P.Ident)) := do
  let stdout := output.stdout

  -- The model in the `get-value` response that follows a `sat` or `unknown` answer, if it
  -- parses and gives a value to some variable (`processModel`); it decorates the answer and
  -- never changes it.
  let modelAfter (rest : String) : IO (Option (Model P.Ident)) := do
    let rawModel ← parseModelDDM rest E.usedNames
    match processModel typedVarToSMTFn vars rawModel E with
    | .ok model => return some model
    | .error _ => return none

  -- The result of one check: its answer (`readSatAnswer`, `readValidityAnswer`) with the model
  -- that follows it.
  let resultOf : Option (Strata.SMT.Decision × String) → IO (Result P.Ident)
    | none => return .unknown
    | some (d, rest) => do
      let m ← match d with
        | .sat | .unknown => modelAfter rest
        | .unsat | .timeout => pure none
      return Result.ofAnswer d m

  let mkError (output : IO.Process.Output) : SolverError :=
    let stderr := output.stderr
    let hasExecError := stderr.contains "could not execute external process"
    let hasFileError := stderr.contains "No such file or directory"
    let suggestion :=
      if (hasExecError || hasFileError) && smtsolver == Core.defaultSolver then
        s!" \nEnsure {Core.defaultSolver} is on your PATH or use --solver to specify another SMT solver."
      else ""
    let detail := s!"stderr:{stderr}{suggestion}\nsolver stdout: {output.stdout}\n"
    if isTimeoutOutput output then .timeout detail else .crash detail

  -- Parse results based on which checks are enabled
  match readSatAnswer stdout satisfiabilityCheck with
  | none => return .error (mkError output)
  | some (satAnswer, remaining) =>
    let satResult ← resultOf satAnswer
    match readValidityAnswer remaining validityCheck with
    | none => return .error (mkError output)
    | some valAnswer =>
      let validityResult ← resultOf valAnswer
      return .ok (satResult, validityResult)

/-- Emit a block of `set-info` attributes describing the source location and
    an optional application-specific `(name, rawValue)` pair. `message.snd` is
    a raw Lean string; it will be quoted and SMT-LIB-escaped (doubled `""`)
    before emission. -/
def addLocationInfo {P : PureExpr} [BEq P.Ident]
  (md : Imperative.MetaData P) (message : String × String)
  : Strata.SMT.SolverM Unit := do
  match Imperative.getFileRange md with
    | .some fileRange => do
      Strata.SMT.Solver.setInfoString "file" (toString (format fileRange.file))
      Strata.SMT.Solver.setInfo "start" s!"{fileRange.range.start}"
      Strata.SMT.Solver.setInfo "stop" s!"{fileRange.range.stop}"
      -- TODO: the following should probably be stored in metadata so it can be
      -- set in an application-specific way.
      Strata.SMT.Solver.setInfoString message.fst message.snd
    | .none => pure ()

/-- Result of encoding a proof obligation against an `AbstractSolver`.
    Returned by the encoder callback passed to `dischargeObligationIncremental`,
    consumed by the check-sat orchestration. -/
structure EncodedObligation where
  obligationId : Strata.SMT.Term
  assumptionIds : List String
  estate : Strata.SMT.EncoderState

/-- SMT terms for the given program variables, as `get-value` asks for them. The encoder
    state holds the declaration each variable received, and the variable's Core type is what
    names it there. Variables the encoder never declared are skipped. -/
def varTermsFor {P : PureExpr}
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (estate : Strata.SMT.EncoderState) : List Strata.SMT.Term :=
  vars.filterMap fun (var, ty) =>
    match typedVarToSMTFn var ty with
    | .error _ => none
    | .ok (smtName, termType) =>
      let key : Strata.SMT.UF := { id := smtName, args := [], out := termType }
      match estate.functions[key]? with
      | none => none
      | some encodedId => some (Strata.SMT.Term.var ⟨encodedId, termType⟩)

/-- Discharge a proof obligation using a live (incremental) SMT solver.
    The encoder callback runs against the spawned solver to emit declarations
    and assertions; this helper orchestrates check-sat calls and model parsing. -/
def dischargeObligationIncremental {P : PureExpr} [ToFormat P.Ident] [BEq P.Ident]
    (encodeDecl : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType
                    Strata.SMT.IncrementalEncodingM →
                  Strata.SMT.IncrementalEncodingM EncodedObligation)
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent)
    (smtsolver : String) (solverFlags : Array String)
    (satisfiabilityCheck validityCheck : Bool) (timeLimitMs : Nat := 0) :
    IO (Except SolverError (Result P.Ident × Result P.Ident × Strata.SMT.EncoderState)) := do
  -- A solver that cannot be started, or that answers something other than a verdict (as it does
  -- after rejecting an option), fails this obligation alone, as on the path that writes the query
  -- to a file.
  let failure (e : IO.Error) : SolverError := failureOfMessage s!"{e}"
  let solverState ← try Strata.SMT.IncrementalSolver.spawn smtsolver solverFlags timeLimitMs
    catch e => return .error (failure e)
  let solver := Strata.SMT.IncrementalSolver.mkIncrementalSolver solverState
  let action : Strata.SMT.IncrementalEncodingM
      (Except SolverError (Result P.Ident × Result P.Ident × Strata.SMT.EncoderState)) := do
    let { obligationId, assumptionIds := _, estate } ← encodeDecl solver
    -- Build SMT terms for the user-declared variables rather than the boolean
    -- assumption IDs, so get-value returns their concrete values.
    let userVarTerms := varTermsFor typedVarToSMTFn vars estate
    let getModelForVars : Strata.SMT.IncrementalEncodingM (Model P.Ident) := do
      if userVarTerms.isEmpty then return []
      -- A model is best effort: a term that cannot be written for the solver raises this
      -- monad's encoding error, and a solver that fails to answer raises an `IO.Error`. Either
      -- leaves the model empty, and the verdict stands.
      let fetch : Strata.SMT.IncrementalEncodingM (Model P.Ident) := do
        let pairs ← solver.getValue userVarTerms
        match pairs with
        | [(.prim (.string rawOutput), _)] =>
          let rawModel ← parseModelDDM rawOutput estate.usedNames
          match processModel typedVarToSMTFn vars rawModel estate with
          | .ok model => return model
          | .error _ => return []
        | _ => return []
      tryCatchThe IO.Error (tryCatchThe Strata.SMT.StringLit.EncodingError fetch fun _ => return [])
        fun _ => return []
    let decisionToResult (decision : Strata.SMT.Decision) :
        Strata.SMT.IncrementalEncodingM (Except SolverError (Result P.Ident)) := do
      match decision with
      | .sat => return .ok (.sat (← getModelForVars))
      | .unknown =>
        let model ← getModelForVars
        return .ok (if model.isEmpty then .unknown else .unknown (some model))
      | .unsat => return .ok .unsat
      | .timeout => return .error (.timeout "solver reported a timeout on the incremental check")
    let bothChecks := satisfiabilityCheck && validityCheck
    let mut satResult : Result P.Ident := .unknown
    let mut valResult : Result P.Ident := .unknown
    if bothChecks then
      match ← decisionToResult (← solver.checkSatAssuming [obligationId]) with
      | .error e => return .error e
      | .ok r => satResult := r
      let negObligation ← solver.mkNot obligationId
      match ← decisionToResult (← solver.checkSatAssuming [negObligation]) with
      | .error e => return .error e
      | .ok r => valResult := r
    else
      if satisfiabilityCheck then
        solver.assert obligationId
        match ← decisionToResult (← solver.checkSat) with
        | .error e => return .error e
        | .ok r => satResult := r
      else if validityCheck then
        let negObligation ← solver.mkNot obligationId
        solver.assert negObligation
        match ← decisionToResult (← solver.checkSat) with
        | .error e => return .error e
        | .ok r => valResult := r
    return .ok (satResult, valResult, estate)
  -- Closed on every exit, including an exception from encoding or from the solver, so a
  -- failure here never leaves the solver process running. A solver that has already died
  -- cannot be told to exit either, and that second failure must not hide the first.
  let result ←
    try Except.ok <$> action.run
    catch e => pure (.error (failure e))
    finally (try discard solver.close.run catch _ => pure ())
  match result with
  | .error failed => return .error failed
  | .ok (.ok result) => return result
  -- Serialization failed: the typed error is this obligation's result.
  | .ok (.error error) => return .error (.encoding error)

/--
Writes the proof obligation to file, discharge the obligation using SMT solver,
and parse the output of the SMT solver.

The solver reads the query from a file private to this call, which is renamed to `filename`
afterwards, so a verdict is always the answer to the query this call wrote, even when another
verification writes the same `filename` at the same time. The file left under `filename` is
then the query of whichever call renamed its file last.

When two-sided checking is enabled, the generated SMT file will contain two
`(check-sat-assuming)` commands, one for `P ∧ Q` and one for `P ∧ ¬Q`,
and the return value includes both decisions.

A validity verdict `unknown` that cvc5 gives for incompleteness is rerun once with
`retryOnIncomplete` added, when it is not empty (see `retryVerdict`).
-/
def dischargeObligationWithRetry {P : PureExpr} [ToFormat P.Ident] [BEq P.Ident]
  (encodeSMT : Strata.SMT.SolverEncodingM (List String × Strata.SMT.EncoderState))
  (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
  (vars : List P.TypedIdent)
  (smtsolver filename : String)
  (solver_options : Array String) (printFilename : Bool)
  (satisfiabilityCheck validityCheck : Bool)
  (skipSolver : Bool := false)
  -- Term→SMT-LIB string cache shared across a procedure's obligations; `none` on the parallel path.
  (termCache : Option (IO.Ref (Std.HashMap Strata.SMT.Term String)) := none)
  (pctx : Strata.Pipeline.PipelineContext)
  -- Flags of a rerun after an `unknown` for incompleteness; empty for no rerun.
  (retryOnIncomplete : Array String := #[]) :
  IO (Except SolverError (Result P.Ident × Result P.Ident × Strata.SMT.EncoderState)) := do
  -- Seed the solver's term-string cache from the shared ref (if any).
  let initState : Strata.SMT.SolverState ←
    match termCache with
    | some ref => do let m ← ref.get; pure { termStrings := m }
    | none => pure {}
  let query ← privateQueryPath filename
  -- Where the query is left: under `filename`, or where it was written if it cannot be moved.
  let publish : IO System.FilePath := do
    -- Nothing to move when the call failed before the file was created.
    if !(← query.pathExists) then return filename
    try
      IO.FS.rename query filename
      return filename
    catch e =>
      let warn := Strata.Pipeline.emitMessage { category := "vcFile", impact := .internalWarning }
        s!"could not rename {query} to {filename} ({e}); the query is kept at {query}"
      discard (warn.run pctx).toBaseIO
      return query
  -- Set once the query is completely written; until then the private file is incomplete.
  let written ← IO.mkRef false
  -- Set once this call has created the private file; a name already taken is another call's
  -- file, which this call must not touch.
  let created ← IO.mkRef false
  -- An incomplete query is removed rather than put under `filename`, where it would replace a
  -- complete query another run wrote.
  let finish : IO System.FilePath := do
    if ← written.get then publish
    else
      if ← created.get then try IO.FS.removeFile query catch _ => pure ()
      return filename
  let writeAndSolve :
      IO (Except SolverError (Option (IO.Process.Output × Option String) × Strata.SMT.EncoderState)) := do
    let (encoded, solverState) ← pctx.withPhase "writeSMTLib" do
      Strata.SMT.Solver.withFileWriter query.toString (state := initState) (mode := .writeNew) do
        created.set true
        let r ← encodeSMT.run
        pctx.withRepeatedPhase "flushFile" Strata.SMT.Solver.flush
        pure r
    let (_ids, estate) ← match encoded with
      | .ok value => pure value
      | .error error => return Except.error (SolverError.encoding error)
    written.set true
    -- Persist newly produced strings back to the shared ref.
    match termCache with
    | some ref => ref.set solverState.termStrings
    | none => pure ()
    if skipSolver then return .ok (none, estate)
    -- The solver names the file it read in its messages; they name the file the user keeps.
    let output ← pctx.withPhase "runSolver" do
      let out ← runSolver smtsolver (#[query.toString] ++ solver_options)
      pure { out with stdout := out.stdout.replace query.toString filename,
                      stderr := out.stderr.replace query.toString filename }
    -- A retry reruns this call's own query, so its text is read before the file takes the
    -- public name, which another run may write meanwhile. The retry is best effort, so a text
    -- that cannot be read only skips it.
    let text ← if retryOnIncomplete.isEmpty || !validityCheck then pure none
      else try some <$> IO.FS.readFile query catch _ => pure none
    return .ok (some (output, text), estate)
  let solved ← try writeAndSolve catch e => do discard finish; throw e
  let kept ← finish
  let (solver_output, estate) ← match solved with
    | .ok value => pure value
    | .error e => return .error e

  if printFilename then IO.println s!"Wrote problem to {kept}."

  let some (solver_output, queryText) := solver_output
    | return .ok (.unknown, .unknown, estate)
  let parsed ← pctx.withPhase "parseResult" do
    solverResult typedVarToSMTFn vars solver_output estate smtsolver
      satisfiabilityCheck validityCheck
  -- Only an `unknown` whose `:reason-unknown` is `incomplete` is retried: a timeout or a
  -- resource limit is not. The retry is best effort: if the probe or the retry fails (a file
  -- cannot be read, a solver cannot be run), the first verdict stands.
  let retry : IO (Except SolverError (Result P.Ident × Result P.Ident)) := match parsed with
    | .ok (satR, valR@(.unknown _)) => do
      let some queryText := queryText | return parsed
      if !(← reasonIsIncomplete smtsolver filename queryText solver_options) then return parsed
      -- The retry asks only the validity check: its satisfiability check, if any, is dropped,
      -- since only the validity verdict of the retry is used.
      let validityOnly := if satisfiabilityCheck then validityCheckOnly queryText else none
      let out2 ← pctx.withPhase "runSolverRetry" do
        runSolverOnText smtsolver (filename ++ ".retry.smt2") (validityOnly.getD queryText)
          (solver_options ++ retryOnIncomplete)
      let parsed2 ← solverResult typedVarToSMTFn vars out2 estate smtsolver
        (satisfiabilityCheck && validityOnly.isNone) validityCheck
      match parsed2 with
      | .ok (_, val2) => return .ok (satR, retryVerdict valR val2)
      | .error _ => return parsed
    | _ => return parsed
  let parsed ← orFirst parsed retry
  match parsed with
  | .error e => return .error e
  | .ok (satResult, validityResult) => return .ok (satResult, validityResult, estate)

/-- `dischargeObligationWithRetry` without a retry. -/
def dischargeObligation {P : PureExpr} [ToFormat P.Ident] [BEq P.Ident]
  (encodeSMT : Strata.SMT.SolverEncodingM (List String × Strata.SMT.EncoderState))
  (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
  (vars : List P.TypedIdent)
  (smtsolver filename : String)
  (solver_options : Array String) (printFilename : Bool)
  (satisfiabilityCheck validityCheck : Bool)
  (skipSolver : Bool := false)
  (termCache : Option (IO.Ref (Std.HashMap Strata.SMT.Term String)) := none)
  (pctx : Strata.Pipeline.PipelineContext) :
  IO (Except SolverError (Result P.Ident × Result P.Ident × Strata.SMT.EncoderState)) :=
  dischargeObligationWithRetry encodeSMT typedVarToSMTFn vars smtsolver filename solver_options
    printFilename satisfiabilityCheck validityCheck skipSolver termCache pctx

---------------------------------------------------------------------
end -- public section
end SMT

public section

/--
SMT solver's `result` along with an SMT encoder state `estate` for a given
verification condition `obligation`.
Currently, this data structure is only used in the Arith example of StrataTest.
-/
structure VCResult (P : Imperative.PureExpr) where
  obligation : Imperative.ProofObligation P
  result : SMT.Result P.Ident := .unknown
  estate : Strata.SMT.EncoderState := Strata.SMT.EncoderState.init

instance [ToFormat (SMT.Result P.Ident)] [ToFormat (SMT.Model P.Ident)]
  : ToFormat (VCResult P) where
  format r :=
    let result_fmt := match r.result with
      | .sat model  =>
        if model.isEmpty then
          f!"failed\nNo model available."
        else
          f!"failed\nModel: {model}"
      | .unsat => f!"verified"
      | .unknown _ => f!"unknown"
      | .err msg => f!"err {msg}"
    f!"Obligation: {r.obligation.label}\n\
                 Result: {result_fmt}"

/--
An array of `VCResult`s.
-/
abbrev VCResults (P : Imperative.PureExpr) := Array (VCResult P)

def VCResults.format [ToFormat (VCResult P)] (rs : VCResults P) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance [ToFormat (VCResult P)] : ToFormat (VCResults P) where
  format := VCResults.format

instance [ToFormat (VCResult P)] : ToString (VCResults P) where
  toString rs := toString (VCResults.format rs)

end -- public section
end Imperative
