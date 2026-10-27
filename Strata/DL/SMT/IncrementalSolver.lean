/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.AbstractSolver
import Strata.DL.SMT.Symbol
import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.Factory
import Strata.DL.SMT.StringLit

/-!
# Incremental SMT-LIB Backend

Implements `AbstractSolver Term (StateT IncrementalSolverState IO)` where the
state wraps a live solver process communicating via stdin/stdout. Unlike the
batch pipeline (write file, run solver), this backend sends commands
incrementally and reads responses interactively.

Variable shadowing is handled by appending `@N` suffixes to disambiguate
repeated declarations of the same name. The shadow depth is tracked per name.
-/

namespace Strata.SMT

public section

/-- State for the incremental SMT-LIB solver backend. Wraps a live solver
    process and tracks variable shadowing for `declareNew`.

    The mutable parts are refs, so this backend presents itself in `IO` like any other, and a
    call that re-enters the solver, as encoding a quantifier body does, keeps what it declared. -/
structure IncrementalSolverState where
  /-- The underlying SMT-LIB solver process. -/
  solver : SMTLibSolver
  /-- Caches `Term → SMT-LIB string` conversions. -/
  termStrings : IO.Ref (Std.HashMap Term String)
  /-- Caches `TermType → SMT-LIB string` conversions. -/
  typeStrings : IO.Ref (Std.HashMap TermType String)
  /-- Tracks how many times each variable name has been declared (for shadowing). -/
  shadowCounts : IO.Ref (Std.HashMap String Nat)
  /-- Maps SMT-LIB string → Term for the last `checkSatAssuming` call,
      used by `getUnsatAssumptions` to recover terms from solver output. -/
  lastAssumptions : IO.Ref (Std.HashMap String Term)
  /-- The per-check time limit the solver was started with, in milliseconds, 0 for none. The
      solver's own reason for an `unknown` is not asked: z3 may name the theory it gave up in,
      and a limit the user set as an option of their own belongs to the user. -/
  timeLimitMs : Nat := 0

/-- Incremental solver actions that preserve SMT text serialization failures
as structured values while ordinary process IO errors remain exceptions. -/
abbrev IncrementalEncodingM := ExceptT StringLit.EncodingError IO

namespace IncrementalSolver

/-- Write `str` followed by a newline to the solver input stream. -/
def emitln (st : IncrementalSolverState) (str : String) : IO Unit := do
  st.solver.smtLibInput.putStr str
  -- The newline is written as its own segment: appending it to `str` first
  -- would heap-copy the whole string.
  st.solver.smtLibInput.putStr "\n"

/-- Flush the solver input stream. Rarely needed: the output stream built by
    `Solver.spawn` flushes the input stream before every read, so commands
    are always delivered before a reply is awaited. Call this only after a
    command that gets no reply but must still reach the solver process. -/
def flush (st : IncrementalSolverState) : IO Unit := do
  st.solver.smtLibInput.flush

def readln (st : IncrementalSolverState) : IO String := do
  match st.solver.smtLibOutput with
  | .some stdout => return (← stdout.getLine).trimAscii.toString
  | .none => throw (IO.userError "no output stream available")

/-- The SMT-LIB text of a term, cached, for the commands `mkIncrementalSolver` sends. -/
private def termToStr (st : IncrementalSolverState) (t : Term) : IncrementalEncodingM String := do
  if let .some s := (← st.termStrings.get).get? t then return s
  match Strata.SMTDDM.termToString t with
  | .ok s =>
    st.termStrings.modify (·.insert t s)
    return s
  | .error msg => throwThe StringLit.EncodingError (.termSerialization msg)

/-- The SMT-LIB text of a sort, cached, for the commands `mkIncrementalSolver` sends. -/
private def typeToStr (st : IncrementalSolverState) (ty : TermType) :
    IncrementalEncodingM String := do
  if let .some s := (← st.typeStrings.get).get? ty then return s
  match Strata.SMTDDM.termTypeToString ty with
  | .ok s =>
    st.typeStrings.modify (·.insert ty s)
    return s
  | .error msg => throwThe StringLit.EncodingError (.typeSerialization msg)

/-- Get the disambiguated SMT-LIB name for a variable, handling shadowing. -/
private def disambiguatedName (name : String) (depth : Nat) : String :=
  if depth == 0 then name else s!"{name}@{depth}"

/-! ### Reading a response that may contain quoted symbols

A symbol we emit can contain any character, `(`, `)` and a space included, carried
inside `|…|`. Scanning a response as raw text therefore misreads it: a `)` in a
name looks like the end of the enclosing s-expression, and a space in one looks
like a token boundary. These two helpers scan with that in mind, and are shared by
the readers below so the rule lives in one place. -/

/-- Whether a scan is currently inside a `|…|` quoted symbol or a `"…"` string
    literal. SMT-LIB gives neither an escape mechanism, so the delimiters simply
    alternate and one flag each suffices. -/
structure QuoteScan where
  inSymbol : Bool := false
  inString : Bool := false
  deriving Inhabited

/-- Advance a scan over one character. -/
def QuoteScan.step (st : QuoteScan) (c : Char) : QuoteScan :=
  if st.inString then { st with inString := c != '"' }
  else if st.inSymbol then { st with inSymbol := c != '|' }
  else { inSymbol := c == '|', inString := c == '"' }

/-- Whether the scan sits inside a quoted symbol or string literal. -/
def QuoteScan.quoted (st : QuoteScan) : Bool := st.inSymbol || st.inString

/-- Net paren depth contributed by `s`, counting only parens outside a quoted
    symbol or string literal, together with the state to continue a later line
    from.

    Counting raw characters instead would end the response early on a name
    containing `)`, truncating the model with no diagnostic. -/
def scanParens (s : String) (st0 : QuoteScan) : Int × QuoteScan :=
  s.toList.foldl
    (fun (acc : Int × QuoteScan) c =>
      let (d, st) := acc
      let st' := st.step c
      if st.quoted || st'.quoted then (d, st')
      else if c == '(' then (d + 1, st')
      else if c == ')' then (d - 1, st')
      else (d, st'))
    (0, st0)

/-- State while tokenizing a response list: nesting depth, the token being built,
    the tokens so far, and the quoting scan. The lists are built reversed. -/
private structure TokState where
  depth : Int := 0
  cur : List Char := []
  acc : List (List Char) := []
  scan : QuoteScan := {}

/-- Finish the token being built, if there is one. -/
private def TokState.flush (st : TokState) : TokState :=
  if st.cur.isEmpty then st else { st with cur := [], acc := st.cur.reverse :: st.acc }

/-- Read one s-expression response, which may span lines, by balancing parentheses.
    Parentheses inside a quoted symbol or string do not count, which `scanParens` tracks across
    lines; an empty line still ends the read even if nothing has been received. -/
private def readSExpr (st : IncrementalSolverState) : IO String := do
  let mut out := ""
  let mut reading := true
  let mut depth : Int := 0
  let mut scan : QuoteScan := {}
  while reading do
    let line ← readln st
    if line.isEmpty then
      reading := false
    else
      out := out ++ line ++ "\n"
      let (delta, scan') := scanParens line scan
      depth := depth + delta
      scan := scan'
      if depth ≤ 0 then reading := false
  return out

/-- The elements of a response list `(e₁ e₂ …)`.

    An element is not always an atom: `check-sat-assuming` takes negated literals, so
    `((not p) q)` has to yield `(not p)` and `q` rather than three atoms. Nesting is
    therefore tracked, and a quoted symbol or string literal is opaque, so a name
    carrying a space or a paren survives as one token and still matches the spelling
    that was sent. -/
def splitTopLevelTokens (s : String) : List String :=
  let fin := s.toList.foldl
    (fun (st : TokState) c =>
      let scan' := st.scan.step c
      if st.scan.quoted || scan'.quoted then
        { st with cur := c :: st.cur, scan := scan' }
      else if c == '(' then
        if st.depth == 0 then { st with depth := 1, scan := scan' }
        else { st with depth := st.depth + 1, cur := c :: st.cur, scan := scan' }
      else if c == ')' then
        if st.depth ≤ 1 then { st.flush with depth := 0, scan := scan' }
        else
          let st := { st with depth := st.depth - 1, cur := c :: st.cur, scan := scan' }
          if st.depth == 1 then st.flush else st
      else if c == ' ' || c == '\t' then
        if st.depth ≤ 1 then { st.flush with scan := scan' } else { st with cur := c :: st.cur, scan := scan' }
      else { st with cur := c :: st.cur, scan := scan' })
    {}
  fin.flush.acc.reverse.map String.ofList

/-- Spawn an incremental solver process. -/
def spawn (path : String) (args : Array String) (timeLimitMs : Nat := 0) :
    IO IncrementalSolverState := do
  let solver ← Solver.spawn path args
  return { solver, termStrings := ← IO.mkRef {}, typeStrings := ← IO.mkRef {},
           shadowCounts := ← IO.mkRef {}, lastAssumptions := ← IO.mkRef {},
           timeLimitMs }

/-- Build a quantified term. -/
private def mkQuantHelper (qk : QuantifierKind)
    (bindings : List (String × TermType))
    (callback : List Term → IncrementalEncodingM (Term × List (List Term))) :
    IncrementalEncodingM Term := do
  let vars := bindings.map fun (name, ty) => TermVar.mk name ty
  let varTerms := vars.map Term.var
  let (body, triggers) ← callback varTerms
  return (Term.quant qk vars triggers body)

/-- Build a binary comparison. -/
private def mkBinCmp (op : Op) (opName : String) (ts : List Term) : IncrementalEncodingM Term :=
  match ts with
    | [] | [_] => throwThe IO.Error (IO.userError s!"{opName}: need at least two arguments")
    | [t1, t2] => return (Term.app op [t1, t2] .bool)
    | _ => throwThe IO.Error (IO.userError s!"{opName}: pairwise comparison not yet supported")

/-- Build a variadic arithmetic term. -/
private def mkVarArith (op : Op) (opName : String) (ts : List Term) :
    IncrementalEncodingM Term :=
  match ts with
    | [] => throwThe IO.Error (IO.userError s!"{opName}: empty argument list")
    | [t] => return t
    | t :: rest => return (rest.foldl (fun acc x => Term.app op [acc, x] acc.typeOf) t)

/-- For `checkSat` and `checkSatAssuming` in `mkIncrementalSolver`: an `unknown` on a check that
    ran to the time limit the solver was started with is a timeout. Both cvc5 and z3 report
    reaching a per-check limit only as `unknown`; the margin allows for
    their clock and this one disagreeing slightly. -/
private def refineUnknown (st : IncrementalSolverState) (elapsedMs : Nat) : Decision → Decision
  | .unknown =>
    if st.timeLimitMs > 0 && elapsedMs * 100 ≥ st.timeLimitMs * 95 then .timeout else .unknown
  | d => d

/-- Parse a solver check-sat response into a `Decision`, matching the whole
    response line so that only an exact verdict token is a verdict. A solver
    `(error "…")` diagnostic that contains the word `timeout` is not a verdict
    line and surfaces as an error. A per-call timeout arrives as a recognized
    verdict: z3 reports it as `unknown` on stdout (its check-sat response); cvc5
    prints `interrupted by timeout.` on stderr, not on this stdout line. The bare
    `timeout`/`timeout.` arms cover a solver that does emit such a line. -/
def parseDecision (line : String) : Except String Decision :=
  match line with
  | "sat" => .ok .sat
  | "unsat" => .ok .unsat
  | "unknown" => .ok .unknown
  | "timeout" => .ok .timeout
  | "timeout." => .ok .timeout
  | other => .error s!"unrecognized solver output: {other}"

#guard match parseDecision "timeout" with | .ok .timeout => true | _ => false
#guard match parseDecision "unknown" with | .ok .unknown => true | _ => false
#guard match parseDecision "sat" with | .ok .sat => true | _ => false
#guard match parseDecision "bogus" with | .error _ => true | _ => false
-- An error diagnostic that contains the word "timeout" surfaces as an error, not
-- a timeout verdict.
#guard match parseDecision "(error \"unknown parameter timeout\")" with | .error _ => true | _ => false

/-- Format datatype constructors as SMT-LIB strings. -/
private def formatConstrs (st : IncrementalSolverState)
    (constrs : List (String × List (String × TermType))) : IncrementalEncodingM (List String) := do
  let mut result := []
  for (cname, fields) in constrs.reverse do
    let cStr := Symbol.toSMTString cname
    if fields.isEmpty then
      result := s!"({cStr})" :: result
    else do
      let mut fieldStrs := []
      for (fname, fty) in fields.reverse do
        let tyStr ← typeToStr st fty
        fieldStrs := s!"({Symbol.toSMTString fname} {tyStr})" :: fieldStrs
      result := s!"({cStr} {String.intercalate " " fieldStrs})" :: result
  return result

/-- Construct the sort for a datatype given its name and type parameter names. -/
private def mkDatatypeSort (name : String) (params : List String) : TermType × List TermType :=
  let paramSorts := params.map fun p => TermType.constr p []
  (.constr name paramSorts, paramSorts)

/-- Build constructor/tester/selector handles for a list of constructors. -/
private def mkConstructorHandles (selfSort : TermType)
    (constrs : List (String × List (String × TermType)))
    : List (DatatypeConstructorHandles Term) :=
  constrs.map fun (cname, fields) =>
    { constr := Term.app (.datatype_op .constructor cname) [] selfSort
      tester := Term.app (.datatype_op .tester cname) [] .bool
      selectors := fields.map fun (fname, fty) =>
        Term.app (.datatype_op .selector fname) [] fty }

/-- Ask for the values of `ts` and return the solver's reply as text. `get-value`, not
    `get-model`, since that is the grammar `parseModelDDM` reads. -/
private def getValueText (st : IncrementalSolverState) (ts : List Term) :
    IncrementalEncodingM String := do
  emitln st s!"(get-value ({" ".intercalate (← ts.mapM (termToStr st))}))"
  readSExpr st

/-- Build the `AbstractSolver` implementation for incremental SMT-LIB. -/
def mkIncrementalSolver (st : IncrementalSolverState) :
    AbstractSolver Term TermType IncrementalEncodingM where
  setLogic logic := emitln st s!"(set-logic {logic})"
  setOption name value := emitln st s!"(set-option :{name} {value})"
  comment c := emitln st s!"; {c.replace "\n" " "}"

  boolSort := return .bool
  intSort := return .int
  realSort := return .real
  stringSort := return .string
  regexSort := return .regex
  bitvecSort n := return .bitvec n
  arraySort k v := return .constr "Array" [k, v]
  constrSort name args := return .constr name args

  mkBool b := return Term.bool b
  mkInt i := return Term.int i
  mkPrim p := return .prim p
  mkAppOp op args retTy := return .app op args retTy

  mkAnd ts := return (ts.foldl Factory.and (Term.bool true))
  mkOr ts := return (ts.foldl Factory.or (Term.bool false))
  mkNot t := return (Factory.not t)
  mkImplies t1 t2 := return (Factory.implies t1 t2)

  mkAdd ts := mkVarArith .add "mkAdd" ts
  mkSub ts := mkVarArith .sub "mkSub" ts
  mkMul ts := mkVarArith .mul "mkMul" ts
  mkDiv t1 t2 := return (Term.app .div [t1, t2] t1.typeOf)
  mkMod t1 t2 := return (Term.app .mod [t1, t2] t1.typeOf)
  mkNeg t := return (Term.app .neg [t] t.typeOf)
  mkAbs t := return (Term.app .abs [t] t.typeOf)

  mkEq ts := match ts with
    | [] | [_] => throwThe IO.Error (IO.userError "mkEq: need at least two arguments")
    | [t1, t2] => return (Factory.eq t1 t2)
    | t1 :: t2 :: rest =>
      return (rest.foldl (fun acc x => Factory.and acc (Factory.eq t1 x)) (Factory.eq t1 t2))
  mkLt ts := mkBinCmp .lt "mkLt" ts
  mkLe ts := mkBinCmp .le "mkLe" ts
  mkGt ts := mkBinCmp .gt "mkGt" ts
  mkGe ts := mkBinCmp .ge "mkGe" ts

  mkIte c t f := return (Factory.ite c t f)

  mkSelect arr idx := return (Term.app .select [arr, idx] arr.typeOf)
  mkStore arr idx val := return (Term.app .store [arr, idx, val] arr.typeOf)
  mkApp fn args := match fn with
    | .app (.uf uf) _ _ => return (Term.app (.uf uf) args uf.out)
    | .app (.datatype_op kind name) _ retTy => return (Term.app (.datatype_op kind name) args retTy)
    | _ => throwThe IO.Error
        (IO.userError "mkApp: expected a function handle (uninterpreted function or datatype op)")

  declareNew name ty := do
    let count := (← st.shadowCounts.get).getD name 0
    let smtName := disambiguatedName name count
    st.shadowCounts.modify (·.insert name (count + 1))
    let tyStr ← typeToStr st ty
    emitln st s!"(declare-const {Symbol.toSMTString smtName} {tyStr})"
    return Term.var ⟨smtName, ty⟩

  mkParam name ty := return Term.var ⟨name, ty⟩

  declareFun name argTys retTy := do
    let retStr ← typeToStr st retTy
    if argTys.isEmpty then
      emitln st s!"(declare-const {Symbol.toSMTString name} {retStr})"
    else
      let mut argStrs := []
      for ty in argTys.reverse do
        argStrs := (← typeToStr st ty) :: argStrs
      let inline := String.intercalate " " argStrs
      emitln st s!"(declare-fun {Symbol.toSMTString name} ({inline}) {retStr})"
    return Term.var ⟨name, retTy⟩

  defineFun name args retTy body := do
    let retStr ← typeToStr st retTy
    let mut typedArgs := []
    for (n, ty) in args.reverse do
      let tyStr ← typeToStr st ty
      typedArgs := s!"({Symbol.toSMTString n} {tyStr})" :: typedArgs
    let inline := String.intercalate " " typedArgs
    let bodyStr ← termToStr st body
    emitln st s!"(define-fun {Symbol.toSMTString name} ({inline}) {retStr} {bodyStr})"

  defineFunRec name args retTy body := do
    let retStr ← typeToStr st retTy
    let mut typedArgs := []
    for (n, ty) in args.reverse do
      let tyStr ← typeToStr st ty
      typedArgs := s!"({Symbol.toSMTString n} {tyStr})" :: typedArgs
    let inline := String.intercalate " " typedArgs
    let bodyStr ← termToStr st body
    emitln st s!"(define-fun-rec {Symbol.toSMTString name} ({inline}) {retStr} {bodyStr})"

  declareSort name arity := do
    emitln st s!"(declare-sort {Symbol.toSMTString name} {arity})"
    return (.constr name (List.replicate arity (.constr "_" [])))

  declareDatatype name params callback := do
    let (selfSort, paramSorts) := mkDatatypeSort name params
    match callback selfSort paramSorts with
    | .error msg => throwThe IO.Error (IO.userError msg)
    | .ok constrs =>
      let strs ← formatConstrs st constrs
      let cInline := "\n  " ++ String.intercalate "\n  " strs
      if params.isEmpty then
        emitln st s!"(declare-datatype {Symbol.toSMTString name} ({cInline}))"
      else
        let pInline := String.intercalate " " (params.map Symbol.toSMTString)
        emitln st s!"(declare-datatype {Symbol.toSMTString name} (par ({pInline}) ({cInline})))"
      return { sort := selfSort, constructors := mkConstructorHandles selfSort constrs }

  declareDatatypes dts callback := do
    if dts.isEmpty then return []
    let sortsAndParams := dts.map fun (name, params) => mkDatatypeSort name params
    let selfSorts := sortsAndParams.map (·.1)
    let paramSorts := sortsAndParams.map (·.2)
    match callback selfSorts paramSorts with
    | .error msg => throwThe IO.Error (IO.userError msg)
    | .ok allConstrs =>
      let sortDecls := dts.map fun (name, params) => s!"({Symbol.toSMTString name} {params.length})"
      let sortDeclStr := String.intercalate " " sortDecls
      let mut bodies := []
      for ((_, params), constrs) in (dts.zip allConstrs).reverse do
        let strs ← formatConstrs st constrs
        let cInline := String.intercalate " " strs
        if params.isEmpty then
          bodies := s!"({cInline})" :: bodies
        else
          let pInline := String.intercalate " " (params.map Symbol.toSMTString)
          bodies := s!"(par ({pInline}) ({cInline}))" :: bodies
      let bodyStr := String.intercalate "\n  " bodies
      emitln st s!"(declare-datatypes ({sortDeclStr})\n  ({bodyStr}))"
      return (selfSorts.zip allConstrs |>.map fun (sort, constrs) =>
        { sort, constructors := mkConstructorHandles sort constrs })

  mkForall bindings callback := do
    mkQuantHelper .all bindings callback

  mkExists bindings callback := do
    mkQuantHelper .exist bindings callback

  assert t := do
    let s ← termToStr st t
    emitln st s!"(assert {s})"

  checkSat := do
    let t0 ← IO.monoMsNow
    emitln st "(check-sat)"
    let result ← readln st
    let t1 ← IO.monoMsNow
    match parseDecision result with
    | .ok d => pure (refineUnknown st (t1 - t0) d)
    | .error msg => throwThe IO.Error (IO.userError msg)

  checkSatAssuming assumptions := do
    let mut strs := []
    let mut assumptionMap : Std.HashMap String Term := {}
    for t in assumptions.reverse do
      let s ← termToStr st t
      strs := s :: strs
      assumptionMap := assumptionMap.insert s t
    st.lastAssumptions.set assumptionMap
    let inline := String.intercalate " " strs
    let t0 ← IO.monoMsNow
    emitln st s!"(check-sat-assuming ({inline}))"
    let result ← readln st
    let t1 ← IO.monoMsNow
    match parseDecision result with
    | .ok d => pure (refineUnknown st (t1 - t0) d)
    | .error msg => throwThe IO.Error (IO.userError msg)

  getModel :=
    throwThe IO.Error (IO.userError "getModel: not yet implemented for incremental backend")

  getModelText ts := getValueText st ts

  getUnsatAssumptions := do
    emitln st "(get-unsat-assumptions)"
    let response ← readln st
    -- The literals are the symbols that were emitted, so one may carry a space or
    -- a paren inside `|…|`; the response is tokenized with that in mind.
    let literals := splitTopLevelTokens response
    let assumptionMap ← st.lastAssumptions.get
    let mut result := []
    for lit in literals.reverse do
      match assumptionMap.get? lit with
      | some t => result := t :: result
      | none => throwThe IO.Error (IO.userError s!"getUnsatAssumptions: unknown literal '{lit}'")
    return result

  getValue ts := do
    -- The raw reply as a single pair, which the verifier parses.
    let modelOutput ← getValueText st ts
    return [(Term.string modelOutput, Term.string modelOutput)]

  termToSMTLibString t := return (← termToStr st t)

  reset := do
    emitln st "(reset)"
    -- `(reset)` empties the solver, so the bookkeeping that mirrors what the solver
    -- holds has to go with it. `shadowCounts` is the one that matters: it decides the
    -- name `declareNew` hands back, so a stale count renames a variable the caller
    -- still prints under its original name, and the solver rejects the definition.
    -- The `termStrings` and `typeStrings` caches survive deliberately, since they map
    -- a term to its rendering and a term already carries whatever name it was given.
    st.shadowCounts.set {}
    st.lastAssumptions.set {}

  close := do
    emitln st "(exit)"
    -- flush so it actually receives the command rather than
    -- lingering until pipe EOF.
    flush st

end IncrementalSolver

end

end Strata.SMT
