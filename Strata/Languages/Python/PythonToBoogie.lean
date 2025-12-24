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
import Strata.Languages.Python.FunctionSignatures

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

def datetimeType : Boogie.Expression.Ty := .forAll [] (.tcons "Datetime" [])
def dummyDatetime : Boogie.Expression.Expr := .fvar () "DUMMY_DATETIME" none

def dateType : Boogie.Expression.Ty := .forAll [] (.tcons "Date" [])
def dummyDate : Boogie.Expression.Expr := .fvar () "DUMMY_DATE" none

def timedeltaType : Boogie.Expression.Ty := .forAll [] (.tcons "int" [])
def dummyTimedelta : Boogie.Expression.Expr := .fvar () "DUMMY_Timedelta" none

-------------------------------------------------------------------------------

-- Translating a Python expression can require Boogie statements, e.g., a function call
-- We translate these by first defining temporary variables to store the results of the stmts
-- and then using those variables in the expression.
structure PyExprTranslated where
  stmts : List Boogie.Statement
  expr: Boogie.Expression.Expr
  post_stmts : List Boogie.Statement := []
deriving Inhabited

structure PythonFunctionDecl where
  name : String
  args : List (String × String) -- Elements are (arg_name, arg_ty) where `arg_ty` is the string representation of the type in Python
  ret : String
deriving Repr, BEq, Inhabited

structure PythonClassDecl where
  name : String
deriving Repr, BEq, Inhabited

structure TranslationContext where
  signatures : Python.Signatures
  expectedType : Option (Lambda.LMonoTy) := none
  variableTypes : List (String × Lambda.LMonoTy) := []
  func_infos : List PythonFunctionDecl := []
  class_infos : List PythonClassDecl := []
deriving Inhabited

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
  | .ConFloat _ f => .strConst () (f.val)
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

def handleSub (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let lty : Lambda.LMonoTy := (.tcons "Datetime" [])
  let rty : Lambda.LMonoTy := (.tcons "int" [])
  match lty, rty with
  | (.tcons "Datetime" []), (.tcons "int" []) => .app () (.app () (.op () "Datetime_sub" none) lhs) rhs
  | _, _ => panic! s!"Unimplemented add op for {lhs} + {rhs}"

def handleMult (translation_ctx: TranslationContext) (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  match lhs, rhs with
  | .strConst () s, .intConst () i => .strConst () (String.join (List.replicate i.toNat s))
  | .intConst () l, .intConst () r => .intConst () (l * r)
  | .fvar () l _, .fvar () r _ =>
    let l := translation_ctx.variableTypes.find? (λ p => p.fst == l.name)
    let r := translation_ctx.variableTypes.find? (λ p => p.fst == r.name)
    match l, r with
    | .some lty, .some rty =>
      match lty.snd, rty.snd with
      | .tcons "int" [], .tcons "int" [] => .app () (.app () (.op () "Int.Mul" mty[int → (int → int)]) lhs) rhs
      | _, _ => panic! s!"Unsupported types for fvar *. Types: {lty} and {rty}"
    | _, _ => panic! s!"Missing needed type information for *. Exprs: {lhs} and {rhs}"
  | _ , _ => panic! s!"Unsupported args for * . Got: {lhs} and {rhs}"

def handleFloorDiv (_translation_ctx: TranslationContext) (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs) rhs

def handleNot (arg: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let ty : Lambda.LMonoTy := (.tcons "ListStr" [])
  match ty with
  | (.tcons "ListStr" []) => .eq () arg (.op () "ListStr_nil" none)
  | _ => panic! s!"Unimplemented not op for {arg}"

def handleLtE (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let eq := (.eq () lhs rhs)
  let lt := (.app () (.app () (.op () "Datetime_lt" none) lhs) rhs)
  (.app () (.app () (.op () "Bool.Or" none) eq) lt)

def handleGt (lhs rhs: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  (.app () (.app () (.op () "Float_gt" none) lhs) rhs)

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

-- TODO: handle rest of names
def PyListStrToBoogie (names : Array (Python.alias SourceRange)) : Boogie.Expression.Expr :=
  .app () (.app () (.op () "ListStr_cons" mty[string → (ListStr → ListStr)]) (PyAliasToBoogieExpr names[0]!))
       (.op () "ListStr_nil" mty[ListStr])

def handleList (_elmts: Array (Python.expr SourceRange)) (expected_type : Lambda.LMonoTy): PyExprTranslated :=
  match expected_type with
  | (.tcons "ListStr" _) => {stmts := [], expr := (.op () "ListStr_nil" expected_type)}
  | (.tcons "ListDictStrAny" _) => {stmts := [], expr := (.op () "ListDictStrAny_nil" expected_type)}
  | _ => panic! s!"Unexpected type : {expected_type}"

def PyOptExprToString (e : Python.opt_expr SourceRange) : String :=
  match e with
  | .some_expr _ (.Constant _ (.ConString _ s) _) => s.val
  | _ => panic! "Expected some constant string: {e}"

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

def PyExprToMonoTy (e : Python.expr SourceRange) : Lambda.LMonoTy :=
  match e with
  | .Name _ n _ =>
    match n.val with
    | "bool" => .tcons "bool" []
    | "int" => .tcons "int" []
    | "str" => .tcons "string" []
    | "float" => .tcons "string" []
    | "Dict[str Any]" => .tcons "DictStrAny" []
    | "List[str]" => .tcons "ListStr" []
    | "datetime" => .tcons "Datetime" []
    | "date" => .tcons "Date" []
    | "timedelta" => .tcons "Timedelta" []
    | "Client" => .tcons "Client" []
    | "LatencyAnalyzer" => .tcons "LatencyAnalyzer" []
    | _ => panic! s!"Unhandled name: {repr e}"
  | .Subscript _ val _slice _ =>
    match val with
    | .Name _ n _ =>
      match n.val with
      | "Dict" => .tcons "DictStrAny" []
      | "List" => .tcons "ListStr" []
      | _ => panic! s!"Unsupported name: {repr n}"
    | _ => panic! s!"Expected name: {repr e}"
  | _ => panic! s!"Unhandled Expr: {repr e}"


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

def noneOrExpr (translation_ctx : TranslationContext) (fname n : String) (e: Boogie.Expression.Expr) : Boogie.Expression.Expr :=
  let type_str := translation_ctx.signatures.getFuncSigType fname n
  if type_str.endsWith "OrNone" then
    -- Optional param. Need to wrap e.g., string into StrOrNone
    match type_str with
    | "IntOrNone" => .app () (.op () "IntOrNone_mk_int" none) e
    | "StrOrNone" => .app () (.op () "StrOrNone_mk_str" none) e
    | "BytesOrStrOrNone" => .app () (.op () "BytesOrStrOrNone_mk_str" none) e
    | _ => panic! "Unsupported type_str: "++ type_str
  else
    e

def handleCallThrow (jmp_target : String) : Boogie.Statement :=
  let cond := .eq () (.app () (.op () "ExceptOrNone_tag" none) (.fvar () "maybe_except" none)) (.op () "EN_STR_TAG" none)
  .ite cond [.goto jmp_target] []

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

partial def collectVarDecls (translation_ctx : TranslationContext) (stmts: Array (Python.stmt SourceRange)) : List Boogie.Statement :=
  let rec go (s : Python.stmt SourceRange) : List (String × Option String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := lhs.val.toList.map PyExprToString
      names.map (λ n => (n, none))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body _ => body.val.toList.flatMap go
    | .For _ _ _ body _ _ => body.val.toList.flatMap go
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
    | "float" => [(.init name t[string] (.strConst () "0.0")), (.havoc name)] -- Floats as strs for now
    | "bytes" => [(.init name t[string] (.strConst () "")), (.havoc name)]
    | "Client" => [(.init name clientType dummyClient), (.havoc name)]
    | "Dict[str Any]" => [(.init name dictStrAnyType dummyDictStrAny), (.havoc name)]
    | "List[str]" => [(.init name listStrType dummyListStr), (.havoc name)]
    | "datetime" => [(.init name datetimeType dummyDatetime), (.havoc name)]
    | "date" => [(.init name dateType dummyDate), (.havoc name)]
    | "timedelta" => [(.init name timedeltaType dummyTimedelta), (.havoc name)]
    | _ =>
      let user_defined_class := translation_ctx.class_infos.find? (λ i => i.name == ty_name)
      match user_defined_class with
      | .some i =>
        let user_defined_class_ty := .forAll [] (.tcons i.name [])
        let user_defined_class_dummy := .fvar () ("DUMMY_" ++ i.name) none
        [(.init name user_defined_class_ty user_defined_class_dummy), (.havoc name)]
      | .none => panic! s!"Unsupported type annotation: `{ty_name}`"
  let foo := dedup.map toBoogie
  foo.flatten

def isCall (e: Python.expr SourceRange) : Bool :=
  match e with
  | .Call _ _ _ _ => true
  | _ => false

def remapFname (translation_ctx: TranslationContext) (fname: String) : String :=
  match translation_ctx.class_infos.find? (λ i => i.name == fname) with
  | .some i =>
    i.name ++ "___init__"
  | _ =>
    match fname with
    | "float" => "str_to_float"
    | _ => fname

mutual

partial def PyExprToBoogieWithSubst (translation_ctx : TranslationContext)  (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : PyExprTranslated :=
  PyExprToBoogie translation_ctx e substitution_records

partial def PyKWordsToBoogie (substitution_records : Option (List SubstitutionRecord)) (kw : Python.keyword SourceRange) : (String × PyExprTranslated) :=
  match kw with
  | .mk_keyword _ name expr =>
    match name.val with
    | some n => (n.val, PyExprToBoogieWithSubst default substitution_records expr)
    | none => panic! "Keyword arg should have a name"

-- TODO: we should be checking that args are right
partial def argsAndKWordsToCanonicalList (translation_ctx : TranslationContext)
                                 (fname: String)
                                 (args : Array (Python.expr SourceRange))
                                 (kwords: Array (Python.keyword SourceRange))
                                 (substitution_records : Option (List SubstitutionRecord) := none) : List Boogie.Expression.Expr × List Boogie.Statement :=
  if translation_ctx.func_infos.any (λ e => e.name == fname) || translation_ctx.class_infos.any (λ e => e.name++"___init__" == fname) then
    if translation_ctx.func_infos.any (λ e => e.name == fname) then
      (args.toList.map (λ a => (PyExprToBoogieWithSubst default substitution_records a).expr), [])
    else
      (args.toList.map (λ a => (PyExprToBoogieWithSubst default substitution_records a).expr), [])
  else
    let required_order := translation_ctx.signatures.getFuncSigOrder fname
    assert! args.size <= required_order.length
    let remaining := required_order.drop args.size
    let kws_and_exprs := kwords.toList.map (PyKWordsToBoogie substitution_records)
    let ordered_remaining_args := remaining.map (λ n => match kws_and_exprs.find? (λ p => p.fst == n) with
      | .some p =>
        noneOrExpr translation_ctx fname n p.snd.expr
      | .none => Strata.Python.TypeStrToBoogieExpr (translation_ctx.signatures.getFuncSigType fname n))
    let args := args.map (PyExprToBoogieWithSubst default substitution_records)
    let args := (List.range required_order.length).filterMap (λ n =>
        if n < args.size then
          let arg_name := required_order[n]! -- Guaranteed by range. Using finRange causes breaking coercions to Nat.
          some (noneOrExpr translation_ctx fname arg_name args[n]!.expr)
        else
          none)
    (args ++ ordered_remaining_args, kws_and_exprs.flatMap (λ p => p.snd.stmts))

partial def handleDict (keys: Array (Python.opt_expr SourceRange)) (values: Array (Python.expr SourceRange)) : PyExprTranslated :=
  let dict := .app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict") -- TODO: need to generate unique dict arg
  assert! keys.size == values.size
  let zipped := Array.zip keys values

  let res := zipped.toList.flatMap (λ (k, v) =>
    let n := PyOptExprToString k
    let in_dict := (.assume s!"assume_{n}_in_dict" (.app () (.app () (.op () "str_in_dict_str_any" none) (.strConst () n)) dict))
    match v with
    | .Call _ f args _ =>
      match f with
      | .Name _ {ann := _ , val := "str"} _ =>
        assert! args.val.size == 1
        let dt := (.app () (.op () "datetime_to_str" none) ((PyExprToBoogie default args.val[0]!).expr))
        let dict_of_v_is_k := (.assume s!"assume_{n}_key" (.eq () (.app () (.app () (.op () "dict_str_any_get_str" none) dict) (.strConst () n)) dt))
        [in_dict, dict_of_v_is_k]
      | _ => panic! "Unsupported function when constructing map"
    | _ =>
      let dict_of_v_is_k := (.assume s!"assume_{n}_key" (.eq () (.app () (.app () (.op () "dict_str_any_get_str" none) dict) (.strConst () n)) (.strConst () "DummyVal")))
      [in_dict, dict_of_v_is_k])

  {stmts := res , expr := dict, post_stmts := []}

partial def PyExprToBoogie (translation_ctx : TranslationContext) (e : Python.expr SourceRange) (substitution_records : Option (List SubstitutionRecord) := none) : PyExprTranslated :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    {stmts := [], expr := record.boogieExpr}
  else
    match e with
    | .Call _ f args kwords =>
      panic! s!"Call should be handled at stmt level: \n(func: {repr f}) \n(Records: {repr substitution_records}) \n(AST: {repr e.toAst})"
    | .Constant _ c _ => {stmts := [], expr :=  PyConstToBoogie c}
    | .Name _ n _ =>
      match n.val with
      | "AssertionError" | "Exception" => {stmts := [], expr := .strConst () n.val}
      | s =>
        match translation_ctx.variableTypes.find? (λ p => p.fst == s) with
        | .some p =>
          if translation_ctx.expectedType == some (.tcons "bool" []) && p.snd == (.tcons "DictStrAny" []) then
            let a := .fvar () n.val none
            let e := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) a) (.intConst () 0))
            {stmts := [], expr := e}
          else
            {stmts := [], expr := .fvar () n.val none}
        | .none => {stmts := [], expr := .fvar () n.val none}
    | .JoinedStr _ ss => PyExprToBoogie translation_ctx ss.val[0]! -- TODO: need to actually join strings
    | .BinOp _ lhs op rhs =>
      let lhs := (PyExprToBoogie translation_ctx lhs)
      let rhs := (PyExprToBoogie translation_ctx rhs)
      match op with
      | .Add _ =>
        {stmts := lhs.stmts ++ rhs.stmts, expr := handleAdd lhs.expr rhs.expr}
      | .Sub _ =>
        {stmts := lhs.stmts ++ rhs.stmts, expr := handleSub lhs.expr rhs.expr}
      | .Mult _ =>
        {stmts := lhs.stmts ++ rhs.stmts, expr := handleMult translation_ctx lhs.expr rhs.expr}
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare _ lhs op rhs =>
      let lhs := PyExprToBoogie translation_ctx lhs
      assert! rhs.val.size == 1
      let rhs := PyExprToBoogie translation_ctx rhs.val[0]!
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := (.eq () lhs.expr rhs.expr)}
        | Strata.Python.cmpop.In _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := .app () (.app () (.op () "str_in_dict_str_any" none) lhs.expr) rhs.expr}
        | Strata.Python.cmpop.LtE _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := handleLtE lhs.expr rhs.expr}
        | Strata.Python.cmpop.Gt _ =>
          {stmts := lhs.stmts ++ rhs.stmts, expr := handleGt lhs.expr rhs.expr}
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values =>
      let res := handleDict keys.val values.val
      res
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp _ op arg => match op with
      | .Not _ => {stmts := [], expr := handleNot (PyExprToBoogie translation_ctx arg).expr}
      | _ => panic! "Unsupported UnaryOp: {repr e}"
    | .Subscript _ v slice _ =>
      let l := PyExprToBoogie translation_ctx v
      let k := PyExprToBoogie translation_ctx slice
      -- TODO: we need to plumb the type of `v` here
      match s!"{repr l.expr}" with
      | "LExpr.fvar () { name := \"keys\", metadata := Boogie.Visibility.unres } none" =>
          -- let access_check : Boogie.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts, expr := .app () (.app () (.op () "list_str_get" none) l.expr) k.expr}
      | "LExpr.fvar () { name := \"blended_cost\", metadata := Boogie.Visibility.unres } none" =>
          -- let access_check : Boogie.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts, expr := .app () (.app () (.op () "dict_str_any_get_str" none) l.expr) k.expr}
      | _ =>
        match translation_ctx.expectedType with
        | .some (.tcons "ListStr" []) =>
          let access_check : Boogie.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts ++ [access_check], expr := .app () (.app () (.op () "dict_str_any_get_list_str" none) l.expr) k.expr}
        | _ =>
          let access_check : Boogie.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts ++ [access_check], expr := .app () (.app () (.op () "dict_str_any_get" none) l.expr) k.expr}
    | .List _ elmts _ =>
      match elmts.val[0]! with
      | .Constant _ expr _ => match expr with
        | .ConString _ s => handleList elmts.val (.tcons "ListStr" [])
        | _ => panic! s!"Expr: {repr expr}"
      | .Dict _ _ _ => handleList elmts.val (.tcons "ListDictStrAny" [])
      | _ => panic! s!"Unexpected element: {repr elmts.val[0]!}"
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def initTmpParam (p: Python.expr SourceRange × String) : List Boogie.Statement :=
  match p.fst with
  | .Call _ f args _ =>
    match f with
    | .Name _ n _ =>
      match n.val with
      | "json_dumps" => [(.init p.snd t[string] (.strConst () "")), .call [p.snd, "maybe_except"] "json_dumps" [(.app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")), (Strata.Python.TypeStrToBoogieExpr "IntOrNone")]]
      | "str" =>
        assert! args.val.size == 1
        [(.init p.snd t[string] (.strConst () "")), .set p.snd (.app () (.op () "datetime_to_str" none) ((PyExprToBoogie default args.val[0]!).expr))]
      | "int" => [(.init p.snd t[int] (.intConst () 0)), .set p.snd (.op () "datetime_to_int" none)]
      | _ => panic! s!"Unsupported name {n.val}"
    | _ => panic! s!"Unsupported tmp param init call: {repr f}"
  | _ => panic! "Expected Call"

partial def exceptHandlersToBoogie (jmp_targets: List String) (translation_ctx: TranslationContext) (h : Python.excepthandler SourceRange) : List Boogie.Statement :=
  assert! jmp_targets.length >= 2
  match h with
  | .ExceptHandler _ ex_ty _ body =>
    let set_ex_ty_matches := match ex_ty.val with
    | .some ex_ty =>
      let inherits_from : Boogie.BoogieIdent := "inheritsFrom"
      let get_ex_tag : Boogie.BoogieIdent := "ExceptOrNone_code_val"
      let exception_ty : Boogie.Expression.Expr := .app () (.op () get_ex_tag none) (.fvar () "maybe_except" none)
      let rhs_curried : Boogie.Expression.Expr := .app () (.op () inherits_from none) exception_ty
      let res := PyExprToBoogie translation_ctx ex_ty
      let rhs : Boogie.Expression.Expr := .app () rhs_curried (res.expr)
      let call := .set "exception_ty_matches" rhs
      res.stmts ++ [call]
    | .none =>
      [.set "exception_ty_matches" (.boolConst () false)]
    let cond := .fvar () "exception_ty_matches" none
    let body_if_matches := body.val.toList.flatMap (λ s => (PyStmtToBoogie jmp_targets translation_ctx s).fst) ++ [.goto jmp_targets[1]!]
    set_ex_ty_matches ++ [.ite cond body_if_matches []]

partial def handleFunctionCall (lhs: List Boogie.Expression.Ident)
                               (fname: String)
                               (args: Ann (Array (Python.expr SourceRange)) SourceRange)
                               (kwords: Ann (Array (Python.keyword SourceRange)) SourceRange)
                               (_jmp_targets: List String)
                               (translation_ctx: TranslationContext)
                               (_s : Python.stmt SourceRange) : List Boogie.Statement :=

  let fname := remapFname translation_ctx fname

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
  let res := argsAndKWordsToCanonicalList translation_ctx fname args.val kwords.val substitution_records
  args_calls_to_tmps.toList.flatMap initTmpParam ++
    kwords_calls_to_tmps.toList.flatMap initTmpParam ++
    res.snd ++ [.call lhs fname res.fst]

partial def handleComprehension (lhs: Python.expr SourceRange) (gen: Array (Python.comprehension SourceRange)) : List Boogie.Statement :=
  assert! gen.size == 1
  match gen[0]! with
  | .mk_comprehension _ _ itr _ _ =>
    let res := PyExprToBoogie default itr
    let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) res.expr) (.intConst () 0))
    let then_ss: List Boogie.Statement := [.havoc (PyExprToString lhs)]
    let else_ss: List Boogie.Statement := [.set (PyExprToString lhs) (.op () "ListStr_nil" none)]
    res.stmts ++ [.ite guard then_ss else_ss]

partial def PyStmtToBoogie (jmp_targets: List String) (translation_ctx : TranslationContext) (s : Python.stmt SourceRange) : List Boogie.Statement × TranslationContext :=
  assert! jmp_targets.length > 0
  let non_throw : List Boogie.Statement × Option (String × Lambda.LMonoTy) := match s with
    | .Import _ names =>
      ([.call [] "import" [PyListStrToBoogie names.val]], none)
    | .ImportFrom _ s names i =>
      let n := match s.val with
      | some s => [strToBoogieExpr s.val]
      | none => []
      let i := match i.val with
      | some i => [intToBoogieExpr (PyIntToInt i)]
      | none => []
      ([.call [] "importFrom" (n ++ [PyListStrToBoogie names.val] ++ i)], none)
    | .Expr _ (.Call _ func args kwords) =>
      let fname := PyExprToString func
      if callCanThrow translation_ctx.func_infos s then
        (handleFunctionCall ["maybe_except"] fname args kwords jmp_targets translation_ctx s, none)
      else
        (handleFunctionCall [] fname args kwords jmp_targets translation_ctx s, none)
    | .Expr _ (.Constant _ (.ConString _ _) _) =>
      -- TODO: Check that it's a doc string
      ([], none) -- Doc string
    | .Expr _ _ =>
      panic! s!"Can't handle Expr statements that aren't calls: {repr s}"
    | .Assign _ lhs (.Call _ func args kwords) _ =>
      assert! lhs.val.size == 1
      let fname := PyExprToString func
      (handleFunctionCall [PyExprToString lhs.val[0]!, "maybe_except"] fname args kwords jmp_targets translation_ctx s, none)
    | .Assign _ lhs rhs _ =>
      assert! lhs.val.size == 1
      let res := PyExprToBoogie translation_ctx rhs
      (res.stmts ++ [.set (PyExprToString lhs.val[0]!) res.expr], none)
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.Call _ func args kwords))} _ =>
      let fname := PyExprToString func
      (handleFunctionCall [PyExprToString lhs, "maybe_except"] fname args kwords jmp_targets translation_ctx s, some (PyExprToString lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.ListComp _ _ gen))} _ =>
      (handleComprehension lhs gen.val, some (PyExprToString lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty {ann := _, val := (.some e)} _ =>
      let res := (PyExprToBoogie {translation_ctx with expectedType := PyExprToMonoTy ty} e)
      (res.stmts ++ [.set (PyExprToString lhs) res.expr], some (PyExprToString lhs, PyExprToMonoTy ty))
    | .Try _ body handlers _orelse _finalbody =>
        let new_target := s!"excepthandlers_{jmp_targets[0]!}"
        let entry_except_handlers := [.block new_target []]
        let new_jmp_stack := new_target :: jmp_targets
        let except_handlers := handlers.val.toList.flatMap (exceptHandlersToBoogie new_jmp_stack translation_ctx)
        let var_decls := collectVarDecls translation_ctx body.val
        ([.block "try_block" (var_decls ++ body.val.toList.flatMap (λ s => (PyStmtToBoogie new_jmp_stack translation_ctx s).fst) ++ entry_except_handlers ++ except_handlers)], none)
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Boogie statement"
    | .If _ test then_b else_b =>
      let guard_ctx := {translation_ctx with expectedType := some (.tcons "bool" [])}
      ([.ite (PyExprToBoogie guard_ctx test).expr (ArrPyStmtToBoogie translation_ctx then_b.val).fst (ArrPyStmtToBoogie translation_ctx else_b.val).fst], none)
    | .Return _ v =>
      match v.val with
      | .some v => ([.set "ret" (PyExprToBoogie translation_ctx v).expr, .goto jmp_targets[0]!], none) -- TODO: need to thread return value name here. For now, assume "ret"
      | .none => ([.goto jmp_targets[0]!], none)
    | .For _ tgt itr body _ _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToBoogie default itr).expr) (.intConst () 0))
      match tgt with
      | .Name _ n _ =>
        let assign_tgt := [(.init n.val dictStrAnyType dummyDictStrAny)]
        ([.ite guard (assign_tgt ++ (ArrPyStmtToBoogie translation_ctx body.val).fst) []], none)
      | _ => panic! s!"tgt must be single name: {repr tgt}"
      -- TODO: missing havoc
    | .While _ test body _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToBoogie default test).expr) (.intConst () 0))
      ([.ite guard (ArrPyStmtToBoogie translation_ctx body.val).fst []], none)
      -- TODO: missing havoc
    | .Assert _ a _ =>
      let res := PyExprToBoogie translation_ctx a
      ([(.assert "py_assertion" res.expr)], none)
    | .AugAssign _ lhs op rhs =>
      match op with
      | .Add _ =>
        match lhs with
        | .Name _ n _ =>
          let rhs := PyExprToBoogie translation_ctx rhs
          let new_lhs := (.strConst () "DUMMY_FLOAT")
          (rhs.stmts ++ [.set n.val new_lhs], none)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | .FloorDiv _ =>
        match lhs with
        | .Name _ n _ =>
          let lhs := PyExprToBoogie translation_ctx lhs
          let rhs := PyExprToBoogie translation_ctx rhs
          let new_lhs := .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs.expr) rhs.expr
          (rhs.stmts ++ [.set n.val new_lhs], none)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | _ => panic! s!"Unsupported AugAssign op: {repr op}"
    | _ =>
      panic! s!"Unsupported {repr s}"
  let new_translation_ctx := match non_throw.snd with
  | .some s => {translation_ctx with variableTypes := s :: translation_ctx.variableTypes}
  | .none => translation_ctx
  if callCanThrow translation_ctx.func_infos s then
    (non_throw.fst ++ [handleCallThrow jmp_targets[0]!], new_translation_ctx)
  else
    (non_throw.fst, new_translation_ctx)

partial def ArrPyStmtToBoogie (translation_ctx: TranslationContext) (a : Array (Python.stmt SourceRange)) : (List Boogie.Statement × TranslationContext) :=
  a.foldl (fun (stmts, ctx) stmt =>
    let (newStmts, newCtx) := PyStmtToBoogie ["end"] ctx stmt
    (stmts ++ newStmts, newCtx)
  ) ([], translation_ctx)

end --mutual


def translateFunctions (a : Array (Python.stmt SourceRange)) (translation_ctx: TranslationContext) : List Boogie.Decl :=
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
        body := varDecls ++ (ArrPyStmtToBoogie translation_ctx body.val).fst ++ [.block "end" []]
      }
      some (.proc proc)
    | _ => none)

def pyTyStrToLMonoTy (ty_str: String) : Lambda.LMonoTy :=
  match ty_str with
  | "str" => mty[string]
  | "int" => mty[int]
  | "datetime" => (.tcons "Datetime" [])
  | _ => panic! s!"Unsupported type: {ty_str}"

def pythonFuncToBoogie (name : String) (args: List (String × String)) (body: Array (Python.stmt SourceRange)) (ret : Option (Python.expr SourceRange)) (spec : Boogie.Procedure.Spec) (translation_ctx : TranslationContext) : Boogie.Procedure :=
  let inputs : List (Lambda.Identifier Boogie.Visibility × Lambda.LMonoTy) := args.map (λ p => (p.fst, pyTyStrToLMonoTy p.snd))
  let varDecls := collectVarDecls translation_ctx body ++ [(.init "exception_ty_matches" t[bool] (.boolConst () false)), (.havoc "exception_ty_matches")]
  let stmts := (ArrPyStmtToBoogie translation_ctx body).fst
  let body := varDecls ++ stmts ++ [.block "end" []]
  let constructor := name.endsWith "___init__"
  let outputs : Lambda.LMonoTySignature := if not constructor then
    match ret with
    | .some _v => [("ret", (.tcons "DictStrAny" [])), ("maybe_except", (.tcons "ExceptOrNone" []))]
    | .none => [("maybe_except", (.tcons "ExceptOrNone" []))]
  else
    let class_ty_name := name.dropRight ("___init__".length)
    [("ret", (.tcons s!"{class_ty_name}" [])), ("maybe_except", (.tcons "ExceptOrNone" []))]
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
  | .mk_arguments _ _ args _ _ _ _ _ =>
    let combined := args.val
    combined.toList.filterMap (λ a =>
    match a with
    | .mk_arg _ name oty _ =>
      if name.val == "self" then
        none
      else
        match oty.val with
        | .some ty => some (name.val, PyExprToString ty)
        | _ => panic! s!"Missing type annotation on arg: {repr a} ({repr args})")

def PyFuncDefToBoogie (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Boogie.Decl × PythonFunctionDecl :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ =>
    let args := unpackPyArguments args
    ([.proc (pythonFuncToBoogie name.val args body.val ret.val default translation_ctx)], {name := name.val, args, ret := s!"{repr ret}"})
  | _ => panic! s!"Expected function def: {repr s}"

def PyClassDefToBoogie (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Boogie.Decl × PythonClassDecl :=
  match s with
  | .ClassDef _ c_name _ _ body _ _ =>
    let member_fn_defs := body.val.toList.filterMap (λ s => match s with
      | .FunctionDef _ name args body _ ret _ _ => some (name, args, body, ret)
      | _ => none)
    (member_fn_defs.map (λ f =>
      let name := f.fst.val
      let args := unpackPyArguments f.snd.fst
      let body := f.snd.snd.fst.val
      let ret := f.snd.snd.snd.val
      .proc (pythonFuncToBoogie (c_name.val++"_"++name) args body ret default translation_ctx)), {name := c_name.val})
  | _ => panic! s!"Expected function def: {repr s}"

def pythonToBoogie (signatures : Python.Signatures) (pgm: Strata.Program): Boogie.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | _ => false)

  let class_defs := insideMod.filter (λ s => match s with
  | .ClassDef _ _ _ _ _ _ _ => true
  | _ => false)

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | .ClassDef _ _ _ _ _ _ _ => false
  | _ => true)

  let globals := [(.var "__name__" (.forAll [] mty[string]) (.strConst () "__main__"))]

  let rec helper {α : Type} (f : Python.stmt SourceRange → TranslationContext → List Boogie.Decl × α)
               (update : TranslationContext → α → TranslationContext)
               (acc : TranslationContext) :
               List (Python.stmt SourceRange) → List Boogie.Decl × TranslationContext
  | [] => ([], acc)
  | x :: xs =>
    let (y, info) := f x acc
    let new_acc := update acc info
    let (ys, acc'') := helper f update new_acc xs
    (y ++ ys, acc'')
  let func_info : TranslationContext := { signatures }

  let func_defs_and_infos := helper PyFuncDefToBoogie (fun acc info => {acc with func_infos := info :: acc.func_infos}) func_info func_defs.toList
  let func_defs := func_defs_and_infos.fst
  let func_infos := func_defs_and_infos.snd

  let class_defs_and_infos := helper PyClassDefToBoogie (fun acc info => {acc with class_infos := info :: acc.class_infos}) func_infos class_defs.toList
  let class_defs := class_defs_and_infos.fst
  let class_infos := class_defs_and_infos.snd
  let class_ty_decls := [(.type (.con {name := "LatencyAnalyzer", numargs := 0})) ]

  {decls := globals ++ class_ty_decls ++ func_defs ++ class_defs ++ [.proc (pythonFuncToBoogie "__main__" [] non_func_blocks none default class_infos)]}

end Strata
