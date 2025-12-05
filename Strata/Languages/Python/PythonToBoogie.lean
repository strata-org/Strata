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
import Strata.Languages.Python.PyFactory
import StrataTest.Internal.InternalFunctionSignatures

namespace Strata
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

def handleMult (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let lty : Lambda.LMonoTy := mty[string]
  let rty : Lambda.LMonoTy := mty[int]
  match lty, rty with
  | (.tcons "string" []), (.tcons "int" []) =>
    match lhs, rhs with
    | .strConst () s, .intConst () i => .strConst () (String.join (List.replicate i.toNat s))
    | _, _ => panic! s!"We only handle str * int for constant strings and ints. Got: {lhs} and {rhs}"
  | _, _ => panic! s!"Unimplemented add op for {lhs} + {rhs}"

def handleNot (arg: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let ty : Lambda.LMonoTy := (.tcons "ListStr" [])
  match ty with
  | (.tcons "ListStr" []) => .eq () arg (.op () "ListStr_nil" none)
  | _ => panic! s!"Unimplemented not op for {arg}"

def handleDict (keys: Array (Python.opt_expr SourceRange)) (values: Array (Python.expr SourceRange)) : Boogie.Expression.Expr :=
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

-- Translating a Python expression can require Boogie statements, e.g., a function call
-- We translate these by first defining temporary variables to store the results of the stmts
-- and then using those variables in the expression.
structure PyExprTranslated where
  stmts : List Boogie.Statement
  expr: Boogie.Expression.Expr
deriving Inhabited

partial def PyExprToBoogie (e : Python.expr SourceRange) (substitution_records : Option (List SubstitutionRecord) := none) : PyExprTranslated :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    {stmts := [], expr := record.boogieExpr}
  else
    match e with
    | .Call _ f _ _ => panic! s!"Call should be handled at stmt level: \n(func: {repr f}) \n(Records: {repr substitution_records}) \n(AST: {repr e.toAst})"
    | .Constant _ c _ => {stmts := [], expr :=  PyConstToBoogie c}
    | .Name _ n _ =>
      match n.val with
      | "AssertionError" | "Exception" => {stmts := [], expr := .strConst () n.val}
      | _ => {stmts := [], expr := .fvar () n.val none}
    | .JoinedStr _ ss => PyExprToBoogie ss.val[0]! -- TODO: need to actually join strings
    | .BinOp _ lhs op rhs =>
      let lhs := (PyExprToBoogie lhs)
      let rhs := (PyExprToBoogie rhs)
      match op with
      | .Add _ =>
        {stmts := lhs.stmts ++ rhs.stmts, expr := handleAdd lhs.expr rhs.expr}
      | .Mult _ =>
        {stmts := lhs.stmts ++ rhs.stmts, expr := handleMult lhs.expr rhs.expr}
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare _ lhs op rhs =>
      let lhs := PyExprToBoogie lhs
      assert! rhs.val.size == 1
      let rhs := PyExprToBoogie rhs.val[0]!
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := (.eq () lhs.expr rhs.expr)}
        | Strata.Python.cmpop.In _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := .app () (.app () (.op () "str_in_dict_str_any" none) lhs.expr) rhs.expr}
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values => {stmts := [], expr := handleDict keys.val values.val}
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp _ op arg => match op with
      | .Not _ => {stmts := [], expr := handleNot (PyExprToBoogie arg).expr}
      | _ => panic! "Unsupported UnaryOp: {repr e}"
    | .Subscript _ v slice _ =>
      let l := PyExprToBoogie v
      let k := PyExprToBoogie slice
      let access_check : Boogie.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
      {stmts := l.stmts ++ k.stmts ++ [access_check], expr := .app () (.app () (.op () "dict_str_any_get" none) l.expr) k.expr}
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyExprToBoogieWithSubst (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : Boogie.Expression.Expr :=
  (PyExprToBoogie e substitution_records).expr

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

-- This information should come from our prelude. For now, we use the fact that
-- these functions are exactly the ones
-- represented as `Call(Attribute(Name(...)))` in the AST (instead of `Call(Name(...))`).
def callCanThrow (func_infos : List PythonFunctionDecl) (stmt: Python.stmt SourceRange) : Bool :=
  match stmt with
  | .Expr _ (.Call _ (.Attribute _ _ _ _) _ _) | .Assign _ _ (.Call _ (.Attribute _ _ _ _) _ _) _ => true
  | .Expr _ (.Call _ f _ _) | .Assign _ _ (.Call _ f _ _) _ => match f with
    | .Name _ f _ => func_infos.any (λ fi => fi.name == f.val)
    | _ => false
  | _ => false

open Strata.Python.Internal in
def noneOrExpr (fname n : String) (e: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let type_str := getFuncSigType fname n
  if type_str.endsWith "OrNone" then
    -- Optional param. Need to wrap e.g., string into StrOrNone
    match type_str with
    | "IntOrNone" => .app () (.op () "IntOrNone_mk_int" none) e
    | "StrOrNone" => .app () (.op () "StrOrNone_mk_str" none) e
    | "BytesOrStrOrNone" => .app () (.op () "BytesOrStrOrNone_mk_str" none) e
    | _ => panic! "Unsupported type_str: "++ type_str
  else
    e

-- TODO: we should be checking that args are right
open Strata.Python.Internal in
def argsAndKWordsToCanonicalList (func_infos : List PythonFunctionDecl)
                                 (fname: String)
                                 (args : Array (Python.expr SourceRange))
                                 (kwords: Array (Python.keyword SourceRange))
                                 (substitution_records : Option (List SubstitutionRecord) := none) : List Boogie.Expression.Expr :=
  if func_infos.any (λ e => e.name == fname) then
    args.toList.map (PyExprToBoogieWithSubst substitution_records)
  else
    let required_order := getFuncSigOrder fname
    assert! args.size <= required_order.length
    let remaining := required_order.drop args.size
    let kws_and_exprs := kwords.toList.map (PyKWordsToBoogie substitution_records)
    let ordered_remaining_args := remaining.map (λ n => match kws_and_exprs.find? (λ p => p.fst == n) with
      | .some p =>
        noneOrExpr fname n p.snd
      | .none => Strata.Python.TypeStrToBoogieExpr (getFuncSigType fname n))
    let args := args.map (PyExprToBoogieWithSubst substitution_records)
    let args := (List.range required_order.length).filterMap (λ n =>
        if n < args.size then
          let arg_name := required_order[n]! -- Guaranteed by range. Using finRange causes breaking coercions to Nat.
          some (noneOrExpr fname arg_name args[n]!)
        else
          none)
    args ++ ordered_remaining_args

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
  | .Call _ f args _ =>
    [(.init p.snd t[string] (.strConst () "")), .call [p.snd, "maybe_except"] "json_dumps" [(.app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")), (Strata.Python.TypeStrToBoogieExpr "IntOrNone")]]
  | _ => panic! "Expected Call"

mutual

partial def exceptHandlersToBoogie (jmp_targets: List String) (func_infos : List PythonFunctionDecl) (h : Python.excepthandler SourceRange) : List Boogie.Statement :=
  assert! jmp_targets.length >= 2
  match h with
  | .ExceptHandler _ ex_ty _ body =>
    let set_ex_ty_matches := match ex_ty.val with
    | .some ex_ty =>
      let inherits_from : Boogie.BoogieIdent := "inheritsFrom"
      let get_ex_tag : Boogie.BoogieIdent := "ExceptOrNone_code_val"
      let exception_ty : Boogie.Expression.Expr := .app () (.op () get_ex_tag none) (.fvar () "maybe_except" none)
      let rhs_curried : Boogie.Expression.Expr := .app () (.op () inherits_from none) exception_ty
      let res := PyExprToBoogie ex_ty
      let rhs : Boogie.Expression.Expr := .app () rhs_curried (res.expr)
      let call := .set "exception_ty_matches" rhs
      res.stmts ++ [call]
    | .none =>
      [.set "exception_ty_matches" (.boolConst () false)]
    let cond := .fvar () "exception_ty_matches" none
    let body_if_matches := body.val.toList.flatMap (PyStmtToBoogie jmp_targets func_infos) ++ [.goto jmp_targets[1]!]
    set_ex_ty_matches ++ [.ite cond {ss := body_if_matches} {ss := []}]

partial def handleFunctionCall (lhs: List Boogie.Expression.Ident)
                               (fname: String)
                               (args: Ann (Array (Python.expr SourceRange)) SourceRange)
                               (kwords: Ann (Array (Python.keyword SourceRange)) SourceRange)
                               (_jmp_targets: List String)
                               (func_infos : List PythonFunctionDecl)
                               (_s : Python.stmt SourceRange) : List Boogie.Statement :=
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
  args_calls_to_tmps.toList.flatMap initTmpParam ++
    kwords_calls_to_tmps.toList.flatMap initTmpParam ++
    [.call lhs fname (argsAndKWordsToCanonicalList func_infos fname args.val kwords.val substitution_records)]

partial def handleComprehension (lhs: Python.expr SourceRange) (gen: Array (Python.comprehension SourceRange)) : List Boogie.Statement :=
  assert! gen.size == 1
  match gen[0]! with
  | .mk_comprehension _ _ itr _ _ =>
    let res := PyExprToBoogie itr
    let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) res.expr) (.intConst () 0))
    let then_ss: List Boogie.Statement := [.havoc (PyExprToString lhs)]
    let else_ss: List Boogie.Statement := [.set (PyExprToString lhs) (.op () "ListStr_nil" none)]
    res.stmts ++ [.ite guard {ss := then_ss} {ss := else_ss}]

partial def PyStmtToBoogie (jmp_targets: List String) (func_infos : List PythonFunctionDecl) (s : Python.stmt SourceRange) : List Boogie.Statement :=
  assert! jmp_targets.length > 0
  let non_throw := match s with
    | .Import _ names =>
      [.call [] "import" [PyListStrToBoogie names.val]]
    | .ImportFrom _ s names i =>
      let n := match s.val with
      | some s => [strToBoogieExpr s.val]
      | none => []
      let i := match i.val with
      | some i => [intToBoogieExpr (PyIntToInt i)]
      | none => []
      [.call [] "importFrom" (n ++ [PyListStrToBoogie names.val] ++ i)]
    | .Expr _ (.Call _ func args kwords) =>
      let fname := PyExprToString func
      if callCanThrow func_infos s then
        handleFunctionCall ["maybe_except"] fname args kwords jmp_targets func_infos s
      else
        handleFunctionCall [] fname args kwords jmp_targets func_infos s
    | .Expr _ _ =>
      panic! "Can't handle Expr statements that aren't calls"
    | .Assign _ lhs (.Call _ func args kwords) _ =>
      assert! lhs.val.size == 1
      let fname := PyExprToString func
      handleFunctionCall [PyExprToString lhs.val[0]!, "maybe_except"] fname args kwords jmp_targets func_infos s
    | .Assign _ lhs rhs _ =>
      assert! lhs.val.size == 1
      let res := PyExprToBoogie rhs
      res.stmts ++ [.set (PyExprToString lhs.val[0]!) res.expr]
    | .AnnAssign _ lhs _ { ann := _ , val := (.some (.Call _ func args kwords))} _ =>
      let fname := PyExprToString func
      handleFunctionCall [PyExprToString lhs, "maybe_except"] fname args kwords jmp_targets func_infos s
    | .AnnAssign _ lhs _ { ann := _ , val := (.some (.ListComp _ _ gen))} _ =>
      handleComprehension lhs gen.val
    | .AnnAssign _ lhs _ {ann := _, val := (.some e)} _ =>
      let res := (PyExprToBoogie e)
      res.stmts ++ [.set (PyExprToString lhs) res.expr]
    | .Try _ body handlers _orelse _finalbody =>
        let new_target := s!"excepthandlers_{jmp_targets[0]!}"
        let entry_except_handlers := [.block new_target {ss := []}]
        let new_jmp_stack := new_target :: jmp_targets
        let except_handlers := handlers.val.toList.flatMap (exceptHandlersToBoogie new_jmp_stack func_infos)
        let var_decls := collectVarDecls body.val
        [.block "try_block" {ss := var_decls ++ body.val.toList.flatMap (PyStmtToBoogie new_jmp_stack func_infos) ++ entry_except_handlers ++ except_handlers}]
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Boogie statement"
    | .If _ test then_b else_b =>
      [.ite (PyExprToBoogie test).expr {ss := (ArrPyStmtToBoogie func_infos then_b.val)} {ss := (ArrPyStmtToBoogie func_infos else_b.val)}] -- TODO: fix this
    | .Return _ v =>
      match v.val with
      | .some v => [.set "ret" (PyExprToBoogie v).expr, .goto jmp_targets[0]!] -- TODO: need to thread return value name here. For now, assume "ret"
      | .none => [.goto jmp_targets[0]!]
    | .For _ _tgt itr body _ _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToBoogie itr).expr) (.intConst () 0))
      [.ite guard {ss := (ArrPyStmtToBoogie func_infos body.val)} {ss := []}]
      -- TODO: missing havoc
    | _ =>
      panic! s!"Unsupported {repr s}"
  if callCanThrow func_infos s then
    non_throw ++ [handleCallThrow jmp_targets[0]!]
  else
    non_throw

partial def ArrPyStmtToBoogie (func_infos : List PythonFunctionDecl) (a : Array (Python.stmt SourceRange)) : List Boogie.Statement :=
  a.toList.flatMap (PyStmtToBoogie ["end"] func_infos)

end --mutual



def translateFunctions (a : Array (Python.stmt SourceRange)) (func_infos : List PythonFunctionDecl) : List Boogie.Decl :=
  a.toList.filterMap (λ s => match s with
    | .FunctionDef _ name _args body _ _ret _ _ =>

      let varDecls : List Boogie.Statement := []
      let proc : Boogie.Procedure := {
        header := {
               name := name.val,
               typeArgs := [],
               inputs := [],
               outputs := [("maybe_except", (.tcons "ExceptOrNone" []))]},
        spec := default,
        body := varDecls ++ ArrPyStmtToBoogie func_infos body.val ++ [.block "end" {ss := []}]
      }
      some (.proc proc)
    | _ => none)

def pyTyStrToLMonoTy (ty_str: String) : Lambda.LMonoTy :=
  match ty_str with
  | "str" => mty[string]
  | _ => panic! s!"Unsupported type: {ty_str}"

def pythonFuncToBoogie (name : String) (args: List (String × String)) (body: Array (Python.stmt SourceRange)) (ret : Option (Python.expr SourceRange)) (spec : Boogie.Procedure.Spec) (func_infos : List PythonFunctionDecl) : Boogie.Procedure :=
  let inputs : List (Lambda.Identifier Boogie.Visibility × Lambda.LMonoTy) := args.map (λ p => (p.fst, pyTyStrToLMonoTy p.snd))
  let varDecls := collectVarDecls body ++ [(.init "exception_ty_matches" t[bool] (.boolConst () false)), (.havoc "exception_ty_matches")]
  let stmts := ArrPyStmtToBoogie func_infos body
  let body := varDecls ++ stmts ++ [.block "end" {ss := []}]
  let outputs : Lambda.LMonoTySignature := match ret with
  | .some v => [("ret", (.tcons "DictStrAny" [])), ("maybe_except", (.tcons "ExceptOrNone" []))]
  | .none => [("maybe_except", (.tcons "ExceptOrNone" []))]
  {
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

def PyFuncDefToBoogie (s: Python.stmt SourceRange) (func_infos : List PythonFunctionDecl) : Boogie.Decl × PythonFunctionDecl :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ =>
    let args := unpackPyArguments args
    (.proc (pythonFuncToBoogie name.val args body.val ret.val default func_infos), {name := name.val, args})
  | _ => panic! s!"Expected function def: {repr s}"

def pythonToBoogie (pgm: Strata.Program): Boogie.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | _ => false)

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | _ => true)

  let globals := [(.var "__name__" (.forAll [] mty[string]) (.strConst () "__main__"))]

  let rec helper (f : Python.stmt SourceRange → List PythonFunctionDecl → Boogie.Decl × PythonFunctionDecl)
                 (acc : List PythonFunctionDecl) :
                 List (Python.stmt SourceRange) → List Boogie.Decl × List PythonFunctionDecl
  | [] => ([], acc)
  | x :: xs =>
    let (y, acc') := f x acc
    let new_acc := acc' :: acc
    let (ys, acc'') := helper f new_acc xs
    (y :: ys, acc'')

  let func_defs_and_infos := (helper PyFuncDefToBoogie [] func_defs.toList)
  let func_defs := func_defs_and_infos.fst
  let func_infos := func_defs_and_infos.snd

  {decls := globals ++ func_defs ++ [.proc (pythonFuncToBoogie "__main__" [] non_func_blocks none default func_infos)]}

end Strata
