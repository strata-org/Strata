/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.AbstractSolver
public import Strata.DL.SMT.Factory
import Strata.DDM.Format
import Std.Data.HashMap

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

def emitln (str : String) : IncrementalSolverM Unit := do
  let st ← get
  st.solver.smtLibInput.putStr s!"{str}\n"
  st.solver.smtLibInput.flush

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
  let tr := match triggers with
    | [] => Term.app .triggers [] .trigger
    | groups =>
      let triggerTerms := groups.map fun group => Term.app .triggers group .trigger
      Term.app .triggers triggerTerms .trigger
  return Term.quant qk vars tr body

/-- Shared helper for binary comparison operations. -/
private def mkBinCmp (op : Op) (opName : String) (ts : List Term)
    : IncrementalSolverM Term :=
  match ts with
  | [] | [_] => throw (IO.userError s!"{opName}: need at least two arguments")
  | [t1, t2] => return Term.app op [t1, t2] .bool
  | _ => throw (IO.userError s!"{opName}: pairwise comparison not yet supported")

/-- Shared helper for variadic arithmetic operations. -/
private def mkVarArith (op : Op) (opName : String) (ts : List Term)
    : IncrementalSolverM Term :=
  match ts with
  | [] => throw (IO.userError s!"{opName}: empty argument list")
  | [t] => return t
  | t :: rest => return rest.foldl (fun acc x => Term.app op [acc, x] acc.typeOf) t

/-- Parse a solver check-sat response into a `Decision`. -/
def parseDecision (line : String) : IncrementalSolverM Decision :=
  match line with
  | "sat" => return .sat
  | "unsat" => return .unsat
  | "unknown" => return .unknown
  | other => throw (IO.userError s!"unrecognized solver output: {other}")

/-- Format datatype constructors as SMT-LIB strings. -/
private def formatConstrs (constrs : List (String × List (String × TermType)))
    : IncrementalSolverM (List String) := do
  let mut result := []
  for (cname, fields) in constrs.reverse do
    if fields.isEmpty then
      result := s!"({cname})" :: result
    else do
      let mut fieldStrs := []
      for (fname, fty) in fields.reverse do
        let tyStr ← typeToStr fty
        fieldStrs := s!"({fname} {tyStr})" :: fieldStrs
      result := s!"({cname} {String.intercalate " " fieldStrs})" :: result
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

  mkAnd ts := return ts.foldl Factory.and (Term.bool true)
  mkOr ts := return ts.foldl Factory.or (Term.bool false)
  mkNot t := return Factory.not t
  mkImplies t1 t2 := return Factory.implies t1 t2

  mkAdd ts := mkVarArith .add "mkAdd" ts
  mkSub ts := mkVarArith .sub "mkSub" ts
  mkMul ts := mkVarArith .mul "mkMul" ts
  mkDiv t1 t2 := return Term.app .div [t1, t2] t1.typeOf
  mkMod t1 t2 := return Term.app .mod [t1, t2] t1.typeOf
  mkNeg t := return Term.app .neg [t] t.typeOf
  mkAbs t := return Term.app .abs [t] t.typeOf

  mkEq ts := match ts with
    | [] | [_] => throw (IO.userError "mkEq: need at least two arguments")
    | [t1, t2] => return Factory.eq t1 t2
    | t1 :: t2 :: rest =>
      return rest.foldl (fun acc x => Factory.and acc (Factory.eq t1 x)) (Factory.eq t1 t2)
  mkLt ts := mkBinCmp .lt "mkLt" ts
  mkLe ts := mkBinCmp .le "mkLe" ts
  mkGt ts := mkBinCmp .gt "mkGt" ts
  mkGe ts := mkBinCmp .ge "mkGe" ts

  mkIte c t f := return Factory.ite c t f

  mkSelect arr idx := return Term.app .select [arr, idx] arr.typeOf
  mkStore arr idx val := return Term.app .store [arr, idx, val] arr.typeOf
  mkApp fn args := match fn with
    | .app (.uf uf) _ _ => return Term.app (.uf uf) args uf.out
    | .app (.datatype_op kind name) _ retTy => return Term.app (.datatype_op kind name) args retTy
    | _ => throw (IO.userError "mkApp: expected a function handle (uninterpreted function or datatype op)")

  declareNew name ty := do
    let st ← get
    let count := st.shadowCounts.getD name 0
    let smtName := disambiguatedName name count
    set { st with shadowCounts := st.shadowCounts.insert name (count + 1) }
    let tyStr ← typeToStr ty
    emitln s!"(declare-const {quoteIdent smtName} {tyStr})"
    return Term.var ⟨smtName, ty⟩

  declareFun name argTys retTy := do
    let retStr ← typeToStr retTy
    if argTys.isEmpty then
      emitln s!"(declare-const {quoteIdent name} {retStr})"
      return Term.var ⟨name, retTy⟩
    else
      let mut argStrs := []
      for ty in argTys.reverse do
        argStrs := (← typeToStr ty) :: argStrs
      let inline := String.intercalate " " argStrs
      emitln s!"(declare-fun {quoteIdent name} ({inline}) {retStr})"
      return Term.var ⟨name, retTy⟩

  defineFun name args retTy body := do
    let retStr ← typeToStr retTy
    let mut typedArgs := []
    for (n, ty) in args.reverse do
      let tyStr ← typeToStr ty
      typedArgs := s!"({quoteIdent n} {tyStr})" :: typedArgs
    let inline := String.intercalate " " typedArgs
    let bodyStr ← termToStr body
    emitln s!"(define-fun {quoteIdent name} ({inline}) {retStr} {bodyStr})"

  declareSort name arity := do
    emitln s!"(declare-sort {name} {arity})"
    return .constr name (List.replicate arity (.constr "_" []))

  declareDatatype name params callback := do
    let (selfSort, paramSorts) := mkDatatypeSort name params
    match callback selfSort paramSorts with
    | .error msg => throw (IO.userError s!"declareDatatype: {msg}")
    | .ok constrs =>
      let strs ← formatConstrs constrs
      let cInline := "\n  " ++ String.intercalate "\n  " strs
      if params.isEmpty then
        emitln s!"(declare-datatype {name} ({cInline}))"
      else
        let pInline := String.intercalate " " params
        emitln s!"(declare-datatype {name} (par ({pInline}) ({cInline})))"
      return { sort := selfSort, constructors := mkConstructorHandles selfSort constrs }

  declareDatatypes dts callback := do
    if dts.isEmpty then return []
    let sortsAndParams := dts.map fun (name, params) => mkDatatypeSort name params
    let selfSorts := sortsAndParams.map (·.1)
    let paramSorts := sortsAndParams.map (·.2)
    match callback selfSorts paramSorts with
    | .error msg => throw (IO.userError s!"declareDatatypes: {msg}")
    | .ok allConstrs =>
      let sortDecls := dts.map fun (name, params) => s!"({name} {params.length})"
      let sortDeclStr := String.intercalate " " sortDecls
      let mut bodies := []
      for ((_, params), constrs) in (dts.zip allConstrs).reverse do
        let strs ← formatConstrs constrs
        let cInline := String.intercalate " " strs
        if params.isEmpty then
          bodies := s!"({cInline})" :: bodies
        else
          let pInline := String.intercalate " " params
          bodies := s!"(par ({pInline}) ({cInline}))" :: bodies
      let bodyStr := String.intercalate "\n  " bodies
      emitln s!"(declare-datatypes ({sortDeclStr})\n  ({bodyStr}))"
      return selfSorts.zip allConstrs |>.map fun (sort, constrs) =>
        { sort, constructors := mkConstructorHandles sort constrs }

  mkForall bindings callback := mkQuantHelper .all bindings callback
  mkExists bindings callback := mkQuantHelper .exist bindings callback

  assert t := do
    let s ← termToStr t
    emitln s!"(assert {s})"

  checkSat := do
    emitln "(check-sat)"
    let result ← readln
    parseDecision result

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
    parseDecision result

  getModel := throw (IO.userError "getModel: not yet implemented for incremental backend")

  getUnsatAssumptions := do
    emitln "(get-unsat-assumptions)"
    let response ← readln
    -- Response is "(lit1 lit2 ...)" — strip parens and split
    let inner := response.replace "(" "" |>.replace ")" ""
    if inner.trimAscii.toString.isEmpty then return []
    let literals := inner.trimAscii.toString.splitOn " " |>.filter (!·.isEmpty)
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
    while reading do
      let respLine ← readln
      if respLine.isEmpty then
        reading := false
      else
        modelOutput := modelOutput ++ respLine ++ "\n"
        for c in respLine.toList do
          if c == '(' then parenDepth := parenDepth + 1
          else if c == ')' then parenDepth := parenDepth - 1
        if parenDepth ≤ 0 then reading := false
    -- Return the raw output as a single pair (the verifier parses it)
    return [(Term.string modelOutput, Term.string modelOutput)]

  termToSMTLibString t := termToStr t

  reset := emitln "(reset)"

  close := emitln "(exit)"

end IncrementalSolver

end

end Strata.SMT
