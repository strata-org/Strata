/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.FunctionSignatures
import Strata.Languages.Python.Regex.ReToBoogie
import StrataTest.Internal.InternalFunctionSignatures

namespace Strata

namespace Python

structure ErrorMsg where
  loc : SourceRange
  message : String
deriving Inhabited

def throwPyError {m α} [MonadExcept ErrorMsg m] (loc : SourceRange) (msg : String) : m α :=
  throw { loc := loc, message := msg }

open Lambda.LTy.Syntax
-- Some hard-coded things we'll need to fix later:

def clientType : Boogie.Expression.Ty := .forAll [] (.tcons "Client" [])
def dummyClient : Boogie.Expression.Expr := .fvar () "DUMMY_CLIENT" none

def dictStrAnyType : Boogie.Expression.Ty := .forAll [] (.tcons "DictStrAny" [])
def dummyDictStrAny : Boogie.Expression.Expr := .fvar () "DUMMY_DICT_STR_ANY" none

def strType : Boogie.Expression.Ty := .forAll [] (.tcons "string" [])
def dummyStr : Boogie.Expression.Expr := .fvar () "DUMMY_STR" none

def listStrType : Boogie.Expression.Ty := .forAll [] (.tcons "ListStr" [])
def dummyListStr : Boogie.Expression.Expr := .fvar () "DUMMY_LIST_STR" none


-------------------------------------------------------------------------------


def toPyCommands (a : Array Operation) : Array (Python.Command SourceRange) :=
  a.map (λ op => match Python.Command.ofAst op with
    | .error e => panic! s!"Failed to translate to Python.Command: {e}"
    | .ok cmd => cmd)

def unwrapModule (c : Python.Command SourceRange) : Array (Python.stmt SourceRange) :=
  match c with
  | Python.Command.Module _ body _ => body.val
  | _ => panic! "Expected module"

def strToBoogieExpr (s: String) : Boogie.Expression.Expr :=
  .strConst () s

def intToBoogieExpr (i: Int) : Boogie.Expression.Expr :=
  .intConst () i

def PyIntToInt (i : Python.int SourceRange) : Int :=
  match i with
  | .IntPos _ n => n.val
  | .IntNeg _ n => -n.val

def PyConstToBoogie (c: Python.constant SourceRange) : Boogie.Expression.Expr :=
  match c with
  | .ConString _ s => .strConst () s.val
  | .ConPos _ i => .intConst () i.val
  | .ConNeg _ i => .intConst () (-i.val)
  | .ConBytes _ _b => .const () (.strConst "") -- TODO: fix
  | _ => panic! s!"Unhandled Constant: {repr c}"

def PyAliasToBoogieExpr (a : Python.alias SourceRange) : Boogie.Expression.Expr :=
  match a with
  | .mk_alias _ n as_n =>
  assert! as_n.val.isNone
  .strConst () n.val

def handleAdd (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let lty : Lambda.LMonoTy := mty[string]
  let rty : Lambda.LMonoTy := mty[string]
  match lty, rty with
  | (.tcons "string" []), (.tcons "string" []) => .app () (.app () (.op () "Str.Concat" mty[string → (string → string)]) lhs) rhs
  | _, _ => panic! s!"Unimplemented add op for {lhs} + {rhs}"

def handleNot (arg: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let ty : Lambda.LMonoTy := (.tcons "ListStr" [])
  match ty with
  | (.tcons "ListStr" []) => .eq () arg (.op () "ListStr_nil" none)
  | _ => panic! s!"Unimplemented not op for {arg}"

def handleDict (_keys: Array (Python.opt_expr SourceRange)) (_values: Array (Python.expr SourceRange)) : Boogie.Expression.Expr :=
  .app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")

structure SubstitutionRecord where
  pyExpr : Python.expr SourceRange
  boogieExpr : Boogie.Expression.Expr

instance : Repr (List SubstitutionRecord) where
  reprPrec xs _ :=
    let py_exprs := xs.map (λ r => r.pyExpr)
    s!"{repr py_exprs}"

def PyExprIdent (e1 e2: Python.expr SourceRange) : Bool :=
  match e1, e2 with
  | .Call sr1 _ _ _, .Call sr2 _ _ _ => sr1 == sr2
  | _ , _ => false

partial def PyExprToBoogie (e : Python.expr SourceRange) (substitution_records : Option (List SubstitutionRecord) := none) : Boogie.Expression.Expr :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    record.boogieExpr
  else
    match e with
    | .Call _ f _ _ => panic! s!"Call should be handled at stmt level: \n(func: {repr f}) \n(Records: {repr substitution_records}) \n(AST: {repr e.toAst})"
    | .Constant _ c _ => PyConstToBoogie c
    | .Name _ n _ =>
      match n.val with
      | "AssertionError" | "Exception" => .strConst () n.val
      | _ => .fvar () n.val none
    | .JoinedStr _ ss => PyExprToBoogie ss.val[0]! -- TODO: need to actually join strings
    | .BinOp _ lhs op rhs => match op with
      | .Add _ => handleAdd (PyExprToBoogie lhs) (PyExprToBoogie rhs)
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare _ lhs op rhs =>
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ =>
          let l := PyExprToBoogie lhs
          assert! rhs.val.size == 1
          let r := PyExprToBoogie rhs.val[0]!
          (.eq () l r)
        | Strata.Python.cmpop.In _ =>
          let l := PyExprToBoogie lhs
          assert! rhs.val.size == 1
          let r := PyExprToBoogie rhs.val[0]!
          .app () (.app () (.op () "str_in_dict_str_any" none) l) r
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values => handleDict keys.val values.val
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp _ op arg => match op with
      | .Not _ => handleNot (PyExprToBoogie arg)
      | _ => panic! "Unsupported UnaryOp: {repr e}"
    | .Subscript _ v slice _ =>
      let l := PyExprToBoogie v
      let k := PyExprToBoogie slice
      .app () (.app () (.op () "dict_str_any_get" none) l) k
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyExprToBoogieWithSubst (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : Boogie.Expression.Expr :=
  PyExprToBoogie e substitution_records

partial def PyExprToString (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Attribute _ v attr _ => s!"{PyExprToString v}_{attr.val}"
  | .Subscript _ v slice _ =>
    let v_name := PyExprToString v
    match v_name with
    | "Dict" =>
      match slice with
      | .Tuple _ elts _ =>
        assert! elts.val.size == 2
        s!"Dict[{PyExprToString elts.val[0]!} {PyExprToString elts.val[1]!}]"
      | _ => panic! s!"Unsupported slice: {repr slice}"
    | "List" =>
      match slice with
      | .Name _ id _ => s!"List[{id.val}]"
      | _ => panic! s!"Unsupported slice: {repr slice}"
    | _ => panic! s!"Unsupported subscript to string: {repr e}"
  | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyKWordsToBoogie (substitution_records : Option (List SubstitutionRecord)) (kw : Python.keyword SourceRange) : (String × Boogie.Expression.Expr) :=
  match kw with
  | .mk_keyword _ name expr =>
    match name.val with
    | some n => (n.val, PyExprToBoogieWithSubst substitution_records expr)
    | none => panic! "Keyword arg should have a name"

structure PythonFunctionDecl where
  name : String
  args : List (String × String) -- Elements are (arg_name, arg_ty) where `arg_ty` is the string representation of the type in Python
deriving Repr, BEq, Inhabited

/--
Structure that stores information required to translate PythonAST expresions/stamts into
Boogie.
-/
structure PyTransContext where
  sig_db : Python.FuncSigDB
  func_info : Std.HashMap String PythonFunctionDecl := {}
deriving Inhabited

namespace PyTransContext

protected def add! (ctx : PyTransContext) (d : PythonFunctionDecl) : PyTransContext :=
  assert! d.name ∉ ctx.func_info
  { ctx with func_info := ctx.func_info.insert d.name d }

end PyTransContext

-- This information should come from our prelude. For now, we use the fact that
-- these functions are exactly the ones
-- represented as `Call(Attribute(Name(...)))` in the AST (instead of `Call(Name(...))`).
def callCanThrow (ctx : PyTransContext) (stmt: Python.stmt SourceRange) : Bool :=
  match stmt with
  | .Expr _ (.Call _ (.Attribute _ _ _ _) _ _) | .Assign _ _ (.Call _ (.Attribute _ _ _ _) _ _) _ => true
  | .Expr _ (.Call _ f _ _) | .Assign _ _ (.Call _ f _ _) _ => match f with
    | .Name _ f _ =>
      match ctx.func_info[f.val]? with
      | some _ => true
      | none => false
    | _ => false
  | _ => false

abbrev PyTransM := ReaderT PyTransContext (StateT (Array Boogie.Statement) (Except ErrorMsg))

def add_stmt (stmt : Boogie.Statement) : PyTransM Unit := do
  modify (·.push stmt)

def liftPyTrans (m : PyTransM Unit) : PyTransM (List Boogie.Statement) := do
  match m |>.run (←read) |>.run #[] with
  | .ok (_, a) => pure <| a.toList
  | .error msg => throw msg

def runPyTrans (ctx : PyTransContext) (m : PyTransM Unit) : Except ErrorMsg (List Boogie.Statement) :=
  match m |>.run ctx |>.run #[] with
  | .ok (_, a) => pure a.toList
  | .error msg => throw msg

open Strata.Python.Internal in
def noneOrExpr (e: Boogie.Expression.Expr) (tp : PyType) : Boogie.Expression.Expr :=
  if tp.allowNone then
    -- Optional param. Need to wrap e.g., string into StrOrNone
    match tp  with
    | .IntOrNone => .app () (.op () "IntOrNone_mk_int" none) e
    | .StrOrNone => .app () (.op () "StrOrNone_mk_str" none) e
    | .BytesOrStrOrNone => .app () (.op () "BytesOrStrOrNone_mk_str" none) e
    | _ => panic! "Unsupported type_str: "++ tp.toString
  else
    e

-- TODO: we should be checking that args are right
open Strata.Python.Internal in
def argsAndKWordsToCanonicalList (ctx : PyTransContext)
                                 (func : Python.expr SourceRange)
                                 (args : Array (Python.expr SourceRange))
                                 (kwords: Array (Python.keyword SourceRange))
                                 (substitution_records : Option (List SubstitutionRecord) := none)
                                : Except ErrorMsg (String × List Boogie.Expression.Expr) :=
  -- TODO: we need a more general solution for other functions
  let fname := PyExprToString func
  if fname ∈ ctx.func_info then
    .ok (fname, args.toList.map (PyExprToBoogieWithSubst substitution_records))
  else do
    let some fsig := ctx.sig_db[fname]?
      | throwPyError func.ann s!"Missing function signature : {fname}"
    assert! args.size <= fsig.args.size
    let remaining := fsig.args.drop args.size
    let kws_and_exprs := kwords.toList.map (PyKWordsToBoogie substitution_records)
    let ordered_remaining_args := remaining.map (λ (n, tp) =>
      match kws_and_exprs.find? (λ(l, _) => l == n) with
      | .some p =>
        noneOrExpr p.snd tp
      | .none => Strata.Python.TypeStrToBoogieExpr tp.toString)
    let args := args.map (PyExprToBoogieWithSubst substitution_records)
    let args := (List.range fsig.args.size).filterMap (λ n =>
        if h: n < args.size then
          let (_, arg_type) := fsig.args[n]! -- Guaranteed by range. Using finRange causes breaking coercions to Nat.
          some (noneOrExpr (args[n]'h) arg_type)
        else
          none)
    pure <| (fname, args ++ ordered_remaining_args.toList)

def handleCallThrow (jmp_target : String) : Boogie.Statement :=
  let cond := .eq () (.app () (.op () "ExceptOrNone_tag" none) (.fvar () "maybe_except" none)) (.op () "EN_STR_TAG" none)
  .ite cond {ss := [.goto jmp_target]} {ss := []}

-- TODO: handle rest of names
def PyListStrToBoogie (names : Array (Python.alias SourceRange)) : Boogie.Expression.Expr :=
  -- ListStr_cons names[0]! (ListStr_nil)
  .app () (.app () (.op () "ListStr_cons" mty[string → (ListStr → ListStr)]) (PyAliasToBoogieExpr names[0]!))
       (.op () "ListStr_nil" mty[ListStr])

def deduplicateTypeAnnotations (l : List (String × Option String)) : List (String × String) := Id.run do
  let mut m : Map String String := []
  for p in l do
    let name := p.fst
    let oty := p.snd
    match oty with
    | .some ty =>
      match m.find? name with
      | .some other_ty =>
        if ty != other_ty then
          panic! s!"Type annotation mismatch: {other_ty} vs {ty}"
      | .none => m := (name, ty) :: m
    | .none => ()
  let names := l.map (λ p => p.fst)
  let unique_names := names.dedup
  unique_names.map (λ n =>
    match m.find? n with
    | .some ty => (n, ty)
    | .none => panic s!"Missing type annotations for {n}")

partial def collectVarDecls (stmts: Array (Python.stmt SourceRange)) : List Boogie.Statement :=
  let rec go (s : Python.stmt SourceRange) : List (String × Option String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := lhs.val.toList.map PyExprToString
      names.map (λ n => (n, none))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body _ => body.val.toList.flatMap go
    | _ => []
  let dup := stmts.toList.flatMap go
  let dedup := deduplicateTypeAnnotations dup
  let toBoogie (p: String × String) : List Boogie.Statement :=
    let name := p.fst
    let ty_name := p.snd
    match ty_name with
    | "bool" => [(.init name t[bool] (.boolConst () false)), (.havoc name)]
    | "str" => [(.init name t[string] (.strConst () "")), (.havoc name)]
    | "int" => [(.init name t[int] (.intConst () 0)), (.havoc name)]
    | "bytes" => [(.init name t[string] (.strConst () "")), (.havoc name)]
    | "Client" => [(.init name clientType dummyClient), (.havoc name)]
    | "Dict[str Any]" => [(.init name dictStrAnyType dummyDictStrAny), (.havoc name)]
    | "List[str]" => [(.init name listStrType dummyListStr), (.havoc name)]
    | _ => panic! s!"Unsupported type annotation: `{ty_name}`"
  let foo := dedup.map toBoogie
  foo.flatten

def isCall (e: Python.expr SourceRange) : Bool :=
  match e with
  | .Call _ _ _ _ => true
  | _ => false

def initTmpParam (p: Python.expr SourceRange × String) : List Boogie.Statement :=
-- [.call lhs fname (argsAndKWordsToCanonicalList func_infos fname args.val kwords.val substitution_records)]
  match p.fst with
  | .Call _ _f _args _ =>
    [(.init p.snd t[string] (.strConst () "")), .call [p.snd, "maybe_except"] "json_dumps" [(.app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")), (Strata.Python.TypeStrToBoogieExpr "IntOrNone")]]
  | _ => panic! "Expected Call"

mutual

partial def exceptHandlersToBoogie (jmp_targets: List String) (h : Python.excepthandler SourceRange) : PyTransM Unit :=
  assert! jmp_targets.length >= 2
  match h with
  | .ExceptHandler _ ex_ty _ body => do
    match ex_ty.val with
    | .some ex_ty =>
      let inherits_from : Boogie.BoogieIdent := "inheritsFrom"
      let get_ex_tag : Boogie.BoogieIdent := "ExceptOrNone_code_val"
      let exception_ty : Boogie.Expression.Expr := .app () (.op () get_ex_tag none) (.fvar () "maybe_except" none)
      let rhs_curried : Boogie.Expression.Expr := .app () (.op () inherits_from none) exception_ty
      let rhs : Boogie.Expression.Expr := .app () rhs_curried ((PyExprToBoogie ex_ty))
      add_stmt <| .set "exception_ty_matches" rhs
    | .none =>
      add_stmt <| .set "exception_ty_matches" (.boolConst () false)
    let cond := .fvar () "exception_ty_matches" none
    let body_if_matches ← liftPyTrans do
          body.val.forM (PyStmtToBoogie jmp_targets)
          add_stmt <| .goto jmp_targets[1]!
    add_stmt <| .ite cond {ss := body_if_matches} {ss := []}

partial def handleFunctionCall (lhs: List Boogie.Expression.Ident)
                               (func : Python.expr SourceRange)
                               (args: Ann (Array (Python.expr SourceRange)) SourceRange)
                               (kwords: Ann (Array (Python.keyword SourceRange)) SourceRange)
                               (_jmp_targets: List String)
                               (_s : Python.stmt SourceRange) : PyTransM Unit := do
  -- Boogie doesn't allow nested function calls, so we need to introduce temporary variables for each nested call
  let nested_args_calls := args.val.filterMap (λ a => if isCall a then some a else none)
  let args_calls_to_tmps := nested_args_calls.map (λ a => (a, s!"call_arg_tmp_{a.toAst.ann.start}"))
  let nested_kwords_calls := kwords.val.filterMap (λ a =>
    let arg := match a with
      | .mk_keyword _ _ f => f
    if isCall arg then some arg else none)
  let kwords_calls_to_tmps := nested_kwords_calls.map (λ a => (a, s!"call_kword_tmp_{a.toAst.ann.start}"))

  let substitution_records : List SubstitutionRecord := args_calls_to_tmps.toList.map (λ p => {pyExpr := p.fst, boogieExpr := .fvar () p.snd none}) ++
                                                        kwords_calls_to_tmps.toList.map (λ p => {pyExpr := p.fst, boogieExpr := .fvar () p.snd none})
  let (fname, r) ←
    match argsAndKWordsToCanonicalList (←read) func args.val kwords.val substitution_records with
    | .ok p => pure p
    | .error msg => throw msg

  for c in args_calls_to_tmps do
    initTmpParam c |>.forM add_stmt
  for c in kwords_calls_to_tmps do
    initTmpParam c |>.forM add_stmt
  add_stmt <| .call lhs fname r

partial def PyStmtToBoogie (jmp_targets: List String) (s : Python.stmt SourceRange) : PyTransM Unit := do
  assert! jmp_targets.length > 0
  match s with
    | .Import _ names =>
      add_stmt <| .call [] "import" [PyListStrToBoogie names.val]
    | .ImportFrom _ s names i =>
      let n := match s.val with
      | some s => [strToBoogieExpr s.val]
      | none => []
      let i := match i.val with
      | some i => [intToBoogieExpr (PyIntToInt i)]
      | none => []
      add_stmt <| .call [] "importFrom" (n ++ [PyListStrToBoogie names.val] ++ i)
    | .Expr _ (.Call _ func args kwords) =>
      if callCanThrow (←read) s then
        handleFunctionCall ["maybe_except"] func args kwords jmp_targets s
      else
        handleFunctionCall [] func args kwords jmp_targets s
    | .Expr _ _ =>
      panic! "Can't handle Expr statements that aren't calls"
    | .Assign _ lhs (.Call _ func args kwords) _ =>
      assert! lhs.val.size == 1
      handleFunctionCall [PyExprToString lhs.val[0]!, "maybe_except"] func args kwords jmp_targets s
    | .Assign _ lhs rhs _ =>
      assert! lhs.val.size == 1
      add_stmt <| .set (PyExprToString lhs.val[0]!) (PyExprToBoogie rhs)
    | .AnnAssign _ lhs _ { ann := _ , val := (.some (.Call _ func args kwords))} _ =>
      handleFunctionCall [PyExprToString lhs, "maybe_except"] func args kwords jmp_targets s
    | .AnnAssign _ lhs _ { ann := _ , val := (.some (.ListComp _ _ _))} _ =>
      -- TODO: check for errors first
      add_stmt <| .havoc (PyExprToString lhs)
    | .AnnAssign _ lhs _ {ann := _, val := (.some e)} _ =>
      add_stmt <| .set (PyExprToString lhs) (PyExprToBoogie e)
    | .Try _ body handlers _orelse _finalbody =>
        let new_target := s!"excepthandlers_{jmp_targets[0]!}"
        let new_jmp_stack := new_target :: jmp_targets
        let body_stmts ← liftPyTrans do
              collectVarDecls body.val |>.forM add_stmt
              body.val.forM (PyStmtToBoogie new_jmp_stack)
              add_stmt <| .block new_target {ss := []}
              handlers.val.forM (exceptHandlersToBoogie new_jmp_stack)
        add_stmt <| .block "try_block" {ss := body_stmts}
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Boogie statement"
    | .If _ test then_b else_b =>
      add_stmt <| .ite (PyExprToBoogie test)
        (← ArrPyStmtToBoogieM then_b.val)
        (← ArrPyStmtToBoogieM else_b.val) -- TODO: fix this
    | .Return _ v =>
      match v.val with
      | .some v =>
        add_stmt <| .set "ret" (PyExprToBoogie v)
        add_stmt <| .goto jmp_targets[0]! -- TODO: need to thread return value name here. For now, assume "ret"
      | .none =>
        add_stmt <| .goto jmp_targets[0]!
    | .For _ _tgt itr body _ _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToBoogie itr)) (.intConst () 0))
      -- let guard := .boolConst () true
      add_stmt <| .ite guard (← ArrPyStmtToBoogieM body.val) {ss := []}
      -- TODO: missing havoc
    | _ =>
      panic! s!"Unsupported {repr s}"
  if callCanThrow (←read) s then
    add_stmt <| handleCallThrow jmp_targets[0]!

partial def ArrPyStmtToBoogieM (a : Array (Python.stmt SourceRange)) : PyTransM Boogie.Block := do
  return { ss := ← liftPyTrans (a.forM (PyStmtToBoogie ["end"])) }

partial def leanBug : List Nat := []

end --mutual



partial def ArrPyStmtToBoogie (ctx : PyTransContext) (a : Array (Python.stmt SourceRange)) : Except ErrorMsg (List Boogie.Statement) :=
  runPyTrans ctx <| a.forM (PyStmtToBoogie ["end"])

def translateFunctions (a : Array (Python.stmt SourceRange)) (ctx : PyTransContext) : Except ErrorMsg (List Boogie.Decl) :=
  a.toList.filterMapM λ s => match s with
    | .FunctionDef _ name _args body _ _ret _ _ => do

      let varDecls : List Boogie.Statement := []
      let proc : Boogie.Procedure := {
        header := {
               name := name.val,
               typeArgs := [],
               inputs := [],
               outputs := [("maybe_except", (.tcons "ExceptOrNone" []))]},
        spec := default,
        body := varDecls ++ (← ArrPyStmtToBoogie ctx body.val) ++ [.block "end" {ss := []}]
      }
      return some (.proc proc)
    | _ => return none

def pyTyStrToLMonoTy (ty_str: String) : Lambda.LMonoTy :=
  match ty_str with
  | "str" => mty[string]
  | _ => panic! s!"Unsupported type: {ty_str}"

def pythonFuncToBoogie (name : String) (args: List (String × String)) (body: Array (Python.stmt SourceRange)) (ret : Option (Python.expr SourceRange)) (spec : Boogie.Procedure.Spec) (ctx : PyTransContext) : Except ErrorMsg Boogie.Procedure := do
  let inputs : List (Lambda.Identifier Boogie.Visibility × Lambda.LMonoTy) := args.map (λ p => (p.fst, pyTyStrToLMonoTy p.snd))
  let varDecls := collectVarDecls body ++ [(.init "exception_ty_matches" t[bool] (.boolConst () false)), (.havoc "exception_ty_matches")]
  let stmts ← ArrPyStmtToBoogie ctx body
  let body := varDecls ++ stmts ++ [.block "end" {ss := []}]
  let outputs : Lambda.LMonoTySignature := match ret with
  | .some _ => [("ret", (.tcons "DictStrAny" [])), ("maybe_except", (.tcons "ExceptOrNone" []))]
  | .none => [("maybe_except", (.tcons "ExceptOrNone" []))]
  return {
    header := {name,
               typeArgs := [],
               inputs,
               outputs},
    spec,
    body
  }

def unpackPyArguments (args: Python.arguments SourceRange) : List (String × String) :=
-- Python AST:
-- arguments = (arg* posonlyargs, arg* args, arg? vararg, arg* kwonlyargs,
--                  expr* kw_defaults, arg? kwarg, expr* defaults)
  match args with -- TODO: Error if any other types of args
  | .mk_arguments _ _ args _ _ _ _ _ => args.val.toList.map (λ a =>
    match a with
    | .mk_arg _ name oty _ =>
      match oty.val with
      | .some ty => (name.val, PyExprToString ty)
      | _ => panic! s!"Missing type annotation on arg: {repr a} ({repr args})")

def PyFuncDefToBoogie (s: Python.stmt SourceRange) (ctx : PyTransContext) : Except ErrorMsg (Boogie.Decl × PythonFunctionDecl) :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ => do
    let args := unpackPyArguments args
    pure (.proc (← pythonFuncToBoogie name.val args body.val ret.val default ctx), {name := name.val, args})
  | _ => panic! s!"Expected function def: {repr s}"

def pythonToBoogie (sig_db : Python.FuncSigDB) (pgm: Strata.Program): Boogie.Program × Array ErrorMsg :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | _ => false)

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | _ => true)

  let globals := #[(.var "__name__" (.forAll [] mty[string]) (.strConst () "__main__"))]

  let rec helper (f : Python.stmt SourceRange → PyTransContext → Except ErrorMsg (Boogie.Decl × PythonFunctionDecl))
                 (decls : Array Boogie.Decl)
                 (acc : PyTransContext)
                 (errors : Array ErrorMsg) :
                 List (Python.stmt SourceRange) → (Array Boogie.Decl × PyTransContext × Array ErrorMsg)
  | [] =>
    (decls, acc, errors)
  | x :: xs =>
    let ctx := acc
    match f x ctx with
    | .ok (y, new_fn) =>
      let new_ctx :=  ctx.add! new_fn
      helper f (decls.push y) new_ctx errors xs
    | .error msg =>
      helper f decls ctx (errors.push msg) xs

  let (decls, ctx, errors) := helper PyFuncDefToBoogie globals { sig_db := sig_db } #[] func_defs.toList
  let (decls, errors) :=
        match pythonFuncToBoogie "__main__" [] non_func_blocks none default ctx with
        | .ok d => (decls.push (.proc d), errors)
        | .error msg => (decls, errors.push msg)
  ({decls := decls.toList}, errors)

end Python


end Strata
