/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.AbstractSolver
import Strata.DL.SMT.Symbol
import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.Factory

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
    process and tracks variable shadowing for `declareNew`. -/
structure IncrementalSolverState where
  /-- The underlying SMT-LIB solver process. -/
  solver : SMTLibSolver
  /-- Caches `Term → SMT-LIB string` conversions. -/
  termStrings : Std.HashMap Term String := {}
  /-- Caches `TermType → SMT-LIB string` conversions. -/
  typeStrings : Std.HashMap TermType String := {}
  /-- Tracks how many times each variable name has been declared (for shadowing). -/
  shadowCounts : Std.HashMap String Nat := {}
  /-- Maps SMT-LIB string → Term for the last `checkSatAssuming` call,
      used by `getUnsatAssumptions` to recover terms from solver output. -/
  lastAssumptions : Std.HashMap String Term := {}

/-- The monad for the incremental solver backend. -/
abbrev IncrementalSolverM := StateT IncrementalSolverState IO

namespace IncrementalSolver

/-- Write `str` followed by a newline to the solver input stream. -/
def emitln (str : String) : IncrementalSolverM Unit := do
  let st ← get
  st.solver.smtLibInput.putStr str
  -- The newline is written as its own segment: appending it to `str` first
  -- would heap-copy the whole string.
  st.solver.smtLibInput.putStr "\n"

/-- Flush the solver input stream. Rarely needed: the output stream built by
    `Solver.spawn` flushes the input stream before every read, so commands
    are always delivered before a reply is awaited. Call this only after a
    command that gets no reply but must still reach the solver process. -/
def flush : IncrementalSolverM Unit := do
  (← get).solver.smtLibInput.flush

def readln : IncrementalSolverM String := do
  let st ← get
  match st.solver.smtLibOutput with
  | .some stdout => return (← stdout.getLine).trimAscii.toString
  | .none => throw (IO.userError "no output stream available")

private def termToStr (t : Term) : IncrementalSolverM String := do
  let st ← get
  if let .some s := st.termStrings.get? t then return s
  match Strata.SMTDDM.termToString t with
  | .ok s =>
    modify fun st => { st with termStrings := st.termStrings.insert t s }
    return s
  | .error msg => throw (IO.userError s!"term serialization failed: {msg}")

private def typeToStr (ty : TermType) : IncrementalSolverM String := do
  let st ← get
  if let .some s := st.typeStrings.get? ty then return s
  match Strata.SMTDDM.termTypeToString ty with
  | .ok s =>
    modify fun st => { st with typeStrings := st.typeStrings.insert ty s }
    return s
  | .error msg => throw (IO.userError s!"type serialization failed: {msg}")

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

/-- State while tokenising a response list: nesting depth, the token being built,
    the tokens so far, and the quoting scan. The lists are built reversed. -/
private structure TokState where
  depth : Int := 0
  cur : List Char := []
  acc : List (List Char) := []
  scan : QuoteScan := {}

/-- Finish the token being built, if there is one. -/
private def TokState.flush (st : TokState) : TokState :=
  if st.cur.isEmpty then st else { st with cur := [], acc := st.cur.reverse :: st.acc }

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
def spawn (path : String) (args : Array String) : IO IncrementalSolverState := do
  let solver ← Solver.spawn path args
  return { solver }

/-- Shared helper for constructing quantified terms. -/
private def mkQuantHelper (qk : QuantifierKind)
    (bindings : List (String × TermType))
    (callback : List Term → IncrementalSolverM (Term × List (List Term)))
    : IncrementalSolverM Term := do
  let vars := bindings.map fun (name, ty) => TermVar.mk name ty
  let varTerms := vars.map Term.var
  let (body, triggers) ← callback varTerms
  return (Term.quant qk vars triggers body)

/-- Shared helper for binary comparison operations. -/
private def mkBinCmp (op : Op) (opName : String) (ts : List Term)
    : IncrementalSolverM Term :=
  match ts with
    | [] | [_] => throw (IO.userError s!"{opName}: need at least two arguments")
    | [t1, t2] => return (Term.app op [t1, t2] .bool)
    | _ => throw (IO.userError s!"{opName}: pairwise comparison not yet supported")

/-- Shared helper for variadic arithmetic operations. -/
private def mkVarArith (op : Op) (opName : String) (ts : List Term)
    : IncrementalSolverM Term :=
  match ts with
    | [] => throw (IO.userError s!"{opName}: empty argument list")
    | [t] => return t
    | t :: rest => return (rest.foldl (fun acc x => Term.app op [acc, x] acc.typeOf) t)

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
private def formatConstrs (constrs : List (String × List (String × TermType)))
    : IncrementalSolverM (List String) := do
  let mut result := []
  for (cname, fields) in constrs.reverse do
    let cStr := Symbol.toSMTString cname
    if fields.isEmpty then
      result := s!"({cStr})" :: result
    else do
      let mut fieldStrs := []
      for (fname, fty) in fields.reverse do
        let tyStr ← typeToStr fty
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

/-- Build the `AbstractSolver` implementation for incremental SMT-LIB. -/
def mkIncrementalSolver : AbstractSolver Term TermType IncrementalSolverM where
  setLogic logic := emitln s!"(set-logic {logic})"
  setOption name value := emitln s!"(set-option :{name} {value})"
  comment c := emitln s!"; {c.replace "\n" " "}"

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
    | [] | [_] => throw (IO.userError "mkEq: need at least two arguments")
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
    | _ => throw (IO.userError "mkApp: expected a function handle (uninterpreted function or datatype op)")

  declareNew name ty := do
    let st ← get
    let count := st.shadowCounts.getD name 0
    let smtName := disambiguatedName name count
    set { st with shadowCounts := st.shadowCounts.insert name (count + 1) }
    let tyStr ← typeToStr ty
    emitln s!"(declare-const {Symbol.toSMTString smtName} {tyStr})"
    return Term.var ⟨smtName, ty⟩

  declareFun name argTys retTy := do
    let retStr ← typeToStr retTy
    if argTys.isEmpty then
      emitln s!"(declare-const {Symbol.toSMTString name} {retStr})"
    else
      let mut argStrs := []
      for ty in argTys.reverse do
        argStrs := (← typeToStr ty) :: argStrs
      let inline := String.intercalate " " argStrs
      emitln s!"(declare-fun {Symbol.toSMTString name} ({inline}) {retStr})"
    return Term.var ⟨name, retTy⟩

  defineFun name args retTy body := do
    let retStr ← typeToStr retTy
    let mut typedArgs := []
    for (n, ty) in args.reverse do
      let tyStr ← typeToStr ty
      typedArgs := s!"({Symbol.toSMTString n} {tyStr})" :: typedArgs
    let inline := String.intercalate " " typedArgs
    let bodyStr ← termToStr body
    emitln s!"(define-fun {Symbol.toSMTString name} ({inline}) {retStr} {bodyStr})"

  defineFunRec name args retTy body := do
    let retStr ← typeToStr retTy
    let mut typedArgs := []
    for (n, ty) in args.reverse do
      let tyStr ← typeToStr ty
      typedArgs := s!"({Symbol.toSMTString n} {tyStr})" :: typedArgs
    let inline := String.intercalate " " typedArgs
    let bodyStr ← termToStr body
    emitln s!"(define-fun-rec {Symbol.toSMTString name} ({inline}) {retStr} {bodyStr})"

  declareSort name arity := do
    emitln s!"(declare-sort {Symbol.toSMTString name} {arity})"
    return (.constr name (List.replicate arity (.constr "_" [])))

  declareDatatype name params callback := do
    let (selfSort, paramSorts) := mkDatatypeSort name params
    match callback selfSort paramSorts with
    | .error msg => throw (IO.userError msg)
    | .ok constrs =>
      let strs ← formatConstrs constrs
      let cInline := "\n  " ++ String.intercalate "\n  " strs
      if params.isEmpty then
        emitln s!"(declare-datatype {Symbol.toSMTString name} ({cInline}))"
      else
        let pInline := String.intercalate " " (params.map Symbol.toSMTString)
        emitln s!"(declare-datatype {Symbol.toSMTString name} (par ({pInline}) ({cInline})))"
      return { sort := selfSort, constructors := mkConstructorHandles selfSort constrs }

  declareDatatypes dts callback := do
    if dts.isEmpty then return []
    let sortsAndParams := dts.map fun (name, params) => mkDatatypeSort name params
    let selfSorts := sortsAndParams.map (·.1)
    let paramSorts := sortsAndParams.map (·.2)
    match callback selfSorts paramSorts with
    | .error msg => throw (IO.userError msg)
    | .ok allConstrs =>
      let sortDecls := dts.map fun (name, params) => s!"({Symbol.toSMTString name} {params.length})"
      let sortDeclStr := String.intercalate " " sortDecls
      let mut bodies := []
      for ((_, params), constrs) in (dts.zip allConstrs).reverse do
        let strs ← formatConstrs constrs
        let cInline := String.intercalate " " strs
        if params.isEmpty then
          bodies := s!"({cInline})" :: bodies
        else
          let pInline := String.intercalate " " (params.map Symbol.toSMTString)
          bodies := s!"(par ({pInline}) ({cInline}))" :: bodies
      let bodyStr := String.intercalate "\n  " bodies
      emitln s!"(declare-datatypes ({sortDeclStr})\n  ({bodyStr}))"
      return (selfSorts.zip allConstrs |>.map fun (sort, constrs) =>
        { sort, constructors := mkConstructorHandles sort constrs })

  mkForall bindings callback := do
    mkQuantHelper .all bindings callback

  mkExists bindings callback := do
    mkQuantHelper .exist bindings callback

  assert t := do
    let s ← termToStr t
    emitln s!"(assert {s})"

  checkSat := do
    emitln "(check-sat)"
    let result ← readln
    match parseDecision result with
    | .ok d => return d
    | .error msg => throw (IO.userError msg)

  checkSatAssuming assumptions := do
    let mut strs := []
    let mut assumptionMap : Std.HashMap String Term := {}
    for t in assumptions.reverse do
      let s ← termToStr t
      strs := s :: strs
      assumptionMap := assumptionMap.insert s t
    modify fun st => { st with lastAssumptions := assumptionMap }
    let inline := String.intercalate " " strs
    emitln s!"(check-sat-assuming ({inline}))"
    let result ← readln
    match parseDecision result with
    | .ok d => return d
    | .error msg => throw (IO.userError msg)

  getModel := throw (IO.userError "getModel: not yet implemented for incremental backend")

  getUnsatAssumptions := do
    emitln "(get-unsat-assumptions)"
    let response ← readln
    -- The literals are the symbols that were emitted, so one may carry a space or
    -- a paren inside `|…|`; the response is tokenised with that in mind.
    let literals := splitTopLevelTokens response
    let assumptionMap := (← get).lastAssumptions
    let mut result := []
    for lit in literals.reverse do
      match assumptionMap.get? lit with
      | some t => result := t :: result
      | none => throw (IO.userError s!"getUnsatAssumptions: unknown literal '{lit}'")
    return result

  getValue ts := do
    -- Send get-value command with the given terms
    let mut strs := []
    for t in ts.reverse do
      strs := (← termToStr t) :: strs
    let inline := String.intercalate " " strs
    emitln s!"(get-value ({inline}))"
    -- Read the response (a single s-expression, possibly multi-line)
    let mut modelOutput := ""
    let mut reading := true
    let mut parenDepth : Int := 0
    let mut scan : QuoteScan := {}
    while reading do
      let respLine ← readln
      if respLine.isEmpty then
        reading := false
      else
        modelOutput := modelOutput ++ respLine ++ "\n"
        let (delta, scan') := scanParens respLine scan
        parenDepth := parenDepth + delta
        scan := scan'
        if parenDepth ≤ 0 then reading := false
    -- Return the raw output as a single pair (the verifier parses it)
    return [(Term.string modelOutput, Term.string modelOutput)]

  termToSMTLibString t := return (← termToStr t)

  reset := emitln "(reset)"

  close := do
    emitln "(exit)"
    -- flush so it actually receives the command rather than
    -- lingering until pipe EOF.
    flush

end IncrementalSolver

end

end Strata.SMT
