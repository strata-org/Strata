/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse

import Strata.Languages.Core.Core
import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.FunctionSignatures
import Strata.Languages.Python.Regex.ReToCore
import Strata.Languages.Python.PyFactory
import Strata.Languages.Python.FunctionSignatures
import Strata.Languages.Python.CoreTypePrelude
import StrataTest.Transform.ProcedureInlining
import Strata.Languages.Core.Verifier
import Strata.DDM.Ion
import Strata.Util.IO

namespace Strata
open Lambda.LTy.Syntax
open Rat
-- Some hard-coded things we'll need to fix later:
#check Core.Statement
def datetimeType : Core.Expression.Ty := .forAll [] (.tcons "Datetime" [])
def dummyDatetime : Core.Expression.Expr := .fvar () "DUMMY_DATETIME" none


def timedeltaType : Core.Expression.Ty := .forAll [] (.tcons "int" [])
def dummyTimedelta : Core.Expression.Expr := .fvar () "DUMMY_Timedelta" none


def AnyTy : Core.Expression.Ty := .forAll [] (.tcons "Any" [])
def KwargsTy : Core.Expression.Ty := .forAll [] (.tcons "kwargs" [])
def ErrorTy : Core.Expression.Ty := .forAll [] (.tcons "Error" [])
def ClassInstanceTy : Core.Expression.Ty := .forAll [] (.tcons "ClassInstance" [])

def DictTy : Core.Expression.Ty := .forAll [] (.tcons "Dict" [])
def FVar(name: String) : Core.Expression.Expr := .fvar () name none
def exceptvar : Core.Expression.Expr := .fvar () "exceptvar" none
def UndefinedError : Core.Expression.Expr := .app () (.op () "UndefinedError" none) (.strConst () "")

-------------------------------------------------------------------------------

-- Translating a Python expression can require Core statements, e.g., a function call
-- We translate these by first defining temporary variables to store the results of the stmts
-- and then using those variables in the expression.
structure PyExprTranslated where
  stmts : List Core.Statement
  args : List Core.Expression.Expr := []
  expr: Core.Expression.Expr
  post_stmts : List Core.Statement := []
deriving Inhabited

structure PythonFunctionDecl where
  name : String
  args : List (String × String × Option (Python.expr SourceRange)) -- Elements are (arg_name, arg_ty) where `arg_ty` is the string representation of the type in Python
  ret : String
deriving Repr, Inhabited

structure PythonClassDecl where
  name : String
  --ClassAttributes: List String
  --InstanceAttribute: List String
deriving Repr, BEq, Inhabited

structure TryBlockInfo where
  ErrorTypes: List String
  TryBlockIndex: String
deriving Inhabited

structure TranslationContext where
  signatures : Python.Signatures
  expectedType : Option (Lambda.LMonoTy) := none
  variableTypes : Std.HashMap String String:= {}
  currentTryBlock: Option TryBlockInfo
  func_infos : List PythonFunctionDecl := []
  class_infos : List PythonClassDecl := []
  currentclassname : String := ""
  classinstance_attributetype: Std.HashMap (String × String) String := {}
deriving Inhabited

def isVar_inContext (trans_ctx: TranslationContext) (varname: String) : Bool :=
  varname ∈ trans_ctx.variableTypes.keys

-------------------------------------------------------------------------------
def getFunctions (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.func => decl.name.name::getFunctions t
        | _ => getFunctions t

def PreludeFunctions : List String := getFunctions Core.Typeprelude.decls

def getProcedures (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.proc => decl.name.name::getProcedures t
        | _ => getProcedures t

def getExceptProcedures (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match h: decl.kind with
      |.proc =>
          let p := decl.getProc h
          if p.header.outputs.length > 0 then
            let lastret := p.header.outputs.getLast!.fst.name
            if (lastret == "exception") || (lastret == "error") then
              p.header.name.name :: (getExceptProcedures t)
            else getExceptProcedures t
          else getExceptProcedures t
      | _ => getExceptProcedures t


def PreludeProcedures : List String := getProcedures Core.Typeprelude.decls

def PreludeExceptProcedures : List String := getExceptProcedures Core.Typeprelude.decls


def IgnoredProcedures : List String := ["print", "import", "importFrom"]

--#eval PreludeExceptProcedures

def create_function_app_acc (args: List Core.Expression.Expr) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match args with
  | [] => acc
  | arg :: t => create_function_app_acc t (.app () acc arg)

def create_function_app (fn: String) (args: List Core.Expression.Expr): Core.Expression.Expr :=
  create_function_app_acc args (.op () fn none)

def toPyCommands (a : Array Operation) : Array (Python.Command SourceRange) :=
  a.map (λ op => match Python.Command.ofAst op with
    | .error e => panic! s!"Failed to translate to Python.Command: {e}"
    | .ok cmd => cmd)

def unwrapModule (c : Python.Command SourceRange) : Array (Python.stmt SourceRange) :=
  match c with
  | Python.Command.Module _ body _ => body.val
  | _ => panic! "Expected module"

def strToCoreExpr (s: String) : Core.Expression.Expr :=
  .strConst () s

def intToCoreExpr (i: Int) : Core.Expression.Expr :=
  .intConst () i

def PyIntToInt (i : Python.int SourceRange) : Int :=
  match i with
  | .IntPos _ n => n.val
  | .IntNeg _ n => -n.val

def PyConstToCore (c: Python.constant SourceRange) : Core.Expression.Expr :=
  match c with
  | .ConString _ s => .strConst () s.val
  | .ConPos _ i => .intConst () i.val
  | .ConNeg _ i => .intConst () (-i.val)
  | .ConBytes _ _b => .const () (.strConst "") -- TODO: fix
  | .ConFloat _ f => .strConst () (f.val)
  | .ConTrue _ => .boolConst () true
  | .ConFalse _ => .boolConst () false
  | _ => panic! s!"Unhandled Constant: {repr c}"

def PyAliasToCoreExpr (a : Python.alias SourceRange) : Core.Expression.Expr :=
  match a with
  | .mk_alias _ n as_n =>
  assert! as_n.val.isNone
  .strConst () n.val

-------------------------------------------------------------------------------

def strToAny (s: String) : Core.Expression.Expr :=
  .app () (.op () "from_string" none) (.strConst () s)

def intToAny (i: Int) : Core.Expression.Expr :=
  .app () (.op () "from_int" none) (.intConst () i)

def boolToAny (b: Bool) : Core.Expression.Expr :=
  .app () (.op () "from_bool" none) (.boolConst () b)

def Any_toBool (b: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.op () "Any_to_bool" none) b

def strVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_string" none) (.fvar () varname none)

def intVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_int" none) (.fvar () varname none)

def boolVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_bool" none) (.fvar () varname none)

def DictVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_Dict" none) (.fvar () varname none)

def AnyNoneExpr : Core.Expression.Expr :=
  .op () "from_none" none

def classVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_Class" none) (.fvar () varname none)

def emptyClassInstance (classname: String) : Core.Expression.Expr :=
  .app () (.op () "ClassInstance_empty" none) (.strConst () classname)

def stringToRat (s : String) : Rat :=
  match s.toInt? with
  | some n => n
  | none =>
    let parts := s.splitOn "."
    if parts.length == 2 then
      match parts[0]!.toInt?, parts[1]!.toNat? with
      | some whole, some frac =>
        (mkRat whole frac)
      | _, _ => panic! s!"Cannot convert: {s} to Rat"
    else panic! s!"Cannot convert: {s} to Rat"

def PyConstToAny (c: Python.constant SourceRange) : Core.Expression.Expr :=
  match c with
  | .ConString _ s => strToAny s.val
  | .ConPos _ i => intToAny i.val
  | .ConNeg _ i => intToAny (-i.val)
  | .ConBytes _ _b => .const () (.strConst "") -- TODO: fix
  | .ConFloat _ f => .app () (.op () "from_Float" none) (.realConst () (stringToRat f.val))
  | .ConTrue _ => boolToAny true
  | .ConFalse _ => boolToAny false
  | .ConNone _ => (.op () "from_none" none)
  | _ => panic! s!"Unhandled Constant: {repr c}"


-------------------------------------------------------------------------------

def handleFloorDiv (_translation_ctx: TranslationContext) (lhs rhs: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs) rhs

def handleDictIn (lhs rhs: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (.op () "Any_in_Dict" none) lhs) rhs

def handleAttribute (var: Core.Expression.Expr) (attr: String) : Core.Expression.Expr :=
  .app () (.op () "AnyExcept_unwrap" none) (.app () (.app () (.op () "get_InstanceAttribute" none) var) (strToCoreExpr attr))


-------------------------------------------------------------------------------

structure SubstitutionRecord where
  pyExpr : Python.expr SourceRange
  boogieExpr : Core.Expression.Expr

instance : Repr (List SubstitutionRecord) where
  reprPrec xs _ :=
    let py_exprs := xs.map (λ r => r.pyExpr)
    s!"{repr py_exprs}"

def PyExprIdent (e1 e2: Python.expr SourceRange) : Bool :=
  match e1, e2 with
  | .Call sr1 _ _ _, .Call sr2 _ _ _ => sr1 == sr2
  | _ , _ => false

-- TODO: handle rest of names
def PyListStrToCore (names : Array (Python.alias SourceRange)) : Core.Expression.Expr :=
  .app () (.app () (.op () "ListStr_cons" mty[string → (ListStr → ListStr)]) (PyAliasToCoreExpr names[0]!))
       (.op () "ListStr_nil" mty[ListStr])


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
      | _ => "List[Any]"
    | _ => panic! s!"Unsupported subscript to string: {repr e}"
  | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyExprGetRoot (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Attribute _ v _ _ => PyExprGetRoot v
  | .Subscript _ v _ _ => PyExprGetRoot v
  | _ => panic! s!"Unhandled Expr: {repr e}"

def PyExprToMonoTy (e : Python.expr SourceRange) : Lambda.LMonoTy :=
  match e with
  | .Name _ n _ =>
    match n.val with
    | "bool" => .tcons "bool" []
    | "int" => .tcons "int" []
    | "str" => .tcons "string" []
    | "float" => .tcons "real" []
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
  | .Attribute _ _ _ _ => .tcons "Any" []
  | _ => panic! s!"Unhandled Expr: {repr e}"

def AnyTy_var (var: String) := (var, "Any")

def isFunctionWithException (funname: String) : Bool :=
  (funname ∈ PreludeExceptProcedures) || (¬ funname ∈ PreludeProcedures)

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

partial def collectVarDecls (stmts: Array (Python.stmt SourceRange)) : List Core.Statement :=
  let rec go (s : Python.stmt SourceRange) : List (String × Option String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := lhs.val.toList.map PyExprToString
      names.map (λ n => (n, "Any"))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body _ => body.val.toList.flatMap go
    | .For _ _ _ body _ _ => body.val.toList.flatMap go
    | .Try _ body handlers _orelse finalbody =>
        let handlers_bodies := handlers.val.toList.map (λ h => match h with
          | .ExceptHandler _ _ _ body => body.val.toList)
        (body.val.toList.flatMap go) ++ (handlers_bodies.flatten.flatMap go) ++ (finalbody.val.toList.flatMap go)
    | _ => []
  let dup := stmts.toList.flatMap go
  let dedup := deduplicateTypeAnnotations dup
  let toCore (p: String × String) : List Core.Statement :=
    let name := p.fst
    let corename := name ++ "_coreval"
    let ty_name := p.snd
    match ty_name with
    | "bool" => [(.init corename t[bool] (.boolConst () false)), (.havoc corename), (.init name AnyTy (boolVarToAny corename))]
    | "str" => [(.init corename t[string] (.strConst () "")), (.havoc corename), (.init name AnyTy (strVarToAny corename))]
    | "int" => [(.init corename t[int] (.intConst () 0)), (.havoc corename), (.init name AnyTy (intVarToAny corename))]
    | "float" => [(.init name t[string] (.strConst () "0.0")), (.havoc name)] -- Floats as strs for now
    | "bytes" => [(.init name t[string] (.strConst () "")), (.havoc name)]
    | "Dict[str Any]" => [(.init corename DictTy (.op () "Dict_empty" none)), (.havoc corename), (.init name AnyTy (DictVarToAny corename))]
    | "List[str]" => [(.init name AnyTy AnyNoneExpr), (.havoc name)]
    | "datetime" => [(.init name datetimeType dummyDatetime), (.havoc name)]
    | "timedelta" => [(.init name timedeltaType dummyTimedelta), (.havoc name)]
    | "Any" => [(.init name AnyTy AnyNoneExpr), (.havoc name)]
    | _ => [(.init corename ClassInstanceTy (emptyClassInstance ty_name) ), (.havoc corename), (.init name AnyTy (classVarToAny corename))]
  let foo := dedup.map toCore
  foo.flatten

partial def collectVars (stmts: Array (Python.stmt SourceRange)) : List (String × String) :=
  let rec go (s : Python.stmt SourceRange) : List (String × String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := lhs.val.toList.map PyExprToString
      names.map (λ n => (n, "Any"))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body _ => body.val.toList.flatMap go
    | .For _ _ _ body _ _ => body.val.toList.flatMap go
    | .Try _ body handlers _orelse finalbody =>
        let handlers_bodies := handlers.val.toList.map (λ h => match h with
          | .ExceptHandler _ _ _ body => body.val.toList)
        (body.val.toList.flatMap go) ++ (handlers_bodies.flatten.flatMap go) ++ (finalbody.val.toList.flatMap go)
    | _ => []
  let dup := stmts.toList.flatMap go
  dup

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

structure TryCatchContext where
  Err_Label : List (String × String)
deriving Inhabited

def ErrTyToGuard (err_expr: Core.Expression.Expr) (errty: String) : Core.Expression.Expr := match errty with
  | "TypeError" => .app () (.op () "Error..isTypeError" none) err_expr
  | "ZeroDivisionError" => .app () (.op () "Error..isUndefinedError" none) err_expr
  | "AssertionError" => .app () (.op () "Error..isAssertionError" none) err_expr
  | "Exception" => .app () (.op () "Bool.Not" none) (.app () (.op () "Error..isNoError" none) err_expr)
  | _ => .app () (.op () "Bool.Not" none) (.app () (.op () "Error..isNoError" none) err_expr)

def create_ErrorHandle_stmt (err_expr: Core.Expression.Expr) (tryblockindex : String) (errtys : List String) : Core.Statement :=
  match errtys with
  | [] => panic! "Cannot be null"
  | errty::[] =>
        let label := errty ++ tryblockindex
        let guard := ErrTyToGuard err_expr errty
        .ite guard [.goto label] []
  | errty::t =>
        let label := errty ++ tryblockindex
        let guard := ErrTyToGuard err_expr errty
        .ite guard [.goto label] [create_ErrorHandle_stmt err_expr tryblockindex t]

def MaybeErrorStmts_to_Stmts (maybe_err_stmts: List (Core.Statement ×  Option Core.Expression.Expr))
                              (errtys : List String)
                              (tryblockindex : String): List Core.Statement :=
  let create_errhandlestmts := maybe_err_stmts.map (λ (stmt, err) =>
      match err with
      | none => [stmt]
      | some err =>  [stmt, create_ErrorHandle_stmt err tryblockindex errtys])
  create_errhandlestmts.flatten

def addExceptionHandle (translation_ctx : TranslationContext) (callstmt: Core.Statement) (sr: SourceRange): List Core.Statement :=
  match callstmt with
  | .call lhs fnname args =>
      if isFunctionWithException fnname then
        let exceptionhandling_stmt := match translation_ctx.currentTryBlock with
          | some tryblockinfo => create_ErrorHandle_stmt exceptvar tryblockinfo.TryBlockIndex tryblockinfo.ErrorTypes
          | _ =>
              let nonerrassert : Core.Expression.Expr := .app () (.op () "Error..isNoError" none) exceptvar
              (.assert s!"safety_assert_{sr.start}_{sr.stop}" nonerrassert)
        let exceptvarident : Core.Expression.Ident := "exceptvar"
        [.call (lhs ++ [exceptvarident]) fnname args, exceptionhandling_stmt]
      else [callstmt]
  | _ => panic s!"Not a call statement "

mutual

partial def PyExprToCoreWithSubst (translation_ctx : TranslationContext)  (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : PyExprTranslated :=
  PyExprToCore translation_ctx e substitution_records

partial def PyKWordsToCore (kw : Python.keyword SourceRange) : (String × PyExprTranslated) :=
  match kw with
  | .mk_keyword sr name expr =>
    match name.val with
    | some n => (n.val, PyExprToCore default expr)
    | none => panic! s!"Keyword arg should have a name {sr.start} {sr.stop}"

partial def PyKWordsToHashMap (kwords : Array (Python.keyword SourceRange)) : Std.HashMap String (Python.expr SourceRange) :=
  kwords.foldl (λ hashmap kw =>
    match kw with
      | .mk_keyword sr name expr =>
        match name.val with
        | some n => hashmap.insert n.val expr
        | none => hashmap)
    {}


partial def kwargs_mk
    (kv: List (String × PyExprTranslated)) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := .strConst () k
      let val := v.expr
      let dict_insert := .app () (.app () (.app () (.op () "kwargs_set" none) acc) key) val
      kwargs_mk t dict_insert

partial def isDictKwargs (kwords : Array (Python.keyword SourceRange)) : Bool :=
  if kwords.size == 0 then false else
  match kwords[0]! with
  | .mk_keyword _ name _ =>
    match name.val with
    | some _ => false
    | none => true

partial def DictKwargsToCore (kwords : Array (Python.keyword SourceRange)) : PyExprTranslated :=
  match kwords[0]! with
  | .mk_keyword _ name expr =>
    match name.val with
    | some _ => panic! s!"Keyword arg should be a Dict"
    | none => PyExprToCore default expr

partial def KwargsToCore  (kwords : Array (Python.keyword SourceRange)): PyExprTranslated :=
  if isDictKwargs kwords then DictKwargsToCore kwords else
    let kws_and_exprs := kwords.toList.map (PyKWordsToCore)
    let ret := kwargs_mk  kws_and_exprs (.op () "kwargs_empty" none)
    let stmts_all := (kws_and_exprs.map (λ (_, pe) => pe.stmts)).flatten
    {stmts := stmts_all , expr := ret, args := []}

partial def KwargsFilter (kwords : Array (Python.keyword SourceRange)) (funcdecl: PythonFunctionDecl) : Array (Python.keyword SourceRange) :=
  kwords.filter (λ kw => match kw with
    | .mk_keyword _ name _ =>
      match name.val with
        | some n => n.val ∉ funcdecl.args.unzip.fst
        | none => True)

partial def CombinePositionalAndKeywordArgs
    (posargs: List (Python.expr SourceRange))
    (kwords : Array (Python.keyword SourceRange))
    (funcdecl: PythonFunctionDecl) : List (Python.expr SourceRange) :=
  --let nondefaultargs := funcdecl.args.filter (λ (_, _, default) => default.isSome);
  let kwords := PyKWordsToHashMap kwords
  let posargs := funcdecl.args.unzip.fst.zip posargs
  let funcdeclsargs:= funcdecl.args
  let funcdeclsargs := if funcdeclsargs.getLast!.fst == "kw" then funcdeclsargs.dropLast else funcdeclsargs
  let funcdeclsargs := funcdeclsargs.drop posargs.length
  let args := funcdeclsargs.map (λ (name, _, default) =>
    match kwords.get? name with
    | some expr => (name, expr)
    | none => match default with | .some default => (name, default) | _ => panic! "Must have a default")
  posargs.unzip.snd ++ args.unzip.snd

partial def Dict_mk (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (kv: List ((Python.opt_expr SourceRange) × (Python.expr SourceRange))) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := strToAny (PyOptExprToString k)
      let val := (PyExprToCore translation_ctx v substitution_records).expr
      let dict_insert := .app () (.app () (.app () (.op () "Dict_set_func" none) acc) key) val
      Dict_mk translation_ctx substitution_records t dict_insert

partial def handleDict (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (keys: Array (Python.opt_expr SourceRange)) (values: Array (Python.expr SourceRange)) : PyExprTranslated :=
  assert! keys.size == values.size
  let kv := keys.toList.zip values.toList
  let dict :=  Dict_mk translation_ctx substitution_records kv (.op () "Dict_empty" none)
  let valueDict := .app () (.op () "from_Dict" none) dict
  {stmts := [] , expr := valueDict, post_stmts := []}

partial def List_mk (es: List Core.Expression.Expr) : Core.Expression.Expr := match es with
  | [] => .op () "ListAny_nil" none
  | e::t => .app () (.app () (.op () "ListAny_cons" none) e) (List_mk t)

partial def handleList (elmts: Array (Python.expr SourceRange)) (translation_ctx : TranslationContext): PyExprTranslated :=
  let trans_elmts := elmts.toList.map (PyExprToCore translation_ctx)
  let stmts := (trans_elmts.map (λ x => x.stmts)).flatten
  let expr := .app () (.op () "from_ListAny" none) (List_mk (trans_elmts.map (λ x => x.expr)))
  {stmts, expr}

partial def Attribute_to_Listname (expr: Python.expr SourceRange): List String :=
  match expr with
  | .Name _ n _ => [n.val]
  | .Attribute _ v attr _ => (Attribute_to_Listname v) ++ [attr.val]
  | _ => []

partial def getFunctionReturnType (translation_ctx : TranslationContext) (func: Python.expr SourceRange) : String :=
  let fname := match func with
    | .Name _ n _ => n.val
    | .Attribute _ v attr _ =>
        if (PyExprToString v) == "self" then translation_ctx.currentclassname ++ "_" ++ attr.val else
        match v with
        | .Attribute _ v1 attr1 _ =>
          if (PyExprToString v1) == "self" then
            match translation_ctx.classinstance_attributetype.get? (translation_ctx.currentclassname, attr1.val) with
            | some ty =>
              if ty == "Any" then "UnknownType" ++ "_" ++ attr.val else
                  ty ++ "_" ++ attr.val
            | none => "UnknownType" ++ "_" ++ attr.val
          else
            match translation_ctx.variableTypes.get? (PyExprGetRoot v)  with
              | none => s!"{PyExprToString v}_{attr.val}"
              | some x =>
                  if x == "Any" then "UnknownType" ++ "_" ++ attr.val else
                    x ++ "_" ++ attr.val
        | _ =>  match translation_ctx.variableTypes.get? (PyExprToString v)  with
              | none => s!"{PyExprToString v}_{attr.val}"
              | some x =>
                  if x == "Any" then "UnknownType" ++ "_" ++ attr.val else
                    x ++ "_" ++ attr.val
    | _ => panic! s!"{repr func} is not a function"
  let fname := remapFname translation_ctx fname
  --dbg_trace s!"{fname}"
  --dbg_trace s!"{repr translation_ctx.func_infos}"
  match translation_ctx.func_infos.find? (λ f => f.name == fname) with
  | some funcinfo => funcinfo.ret
  | _ => "UnknownType"


partial def PyCallToCore  (translation_ctx : TranslationContext)
                            (func: Python.expr SourceRange) (sr: SourceRange)
                            (args: Ann (Array (Python.expr SourceRange)) SourceRange)
                            (kwords : Ann (Array (Python.keyword SourceRange)) SourceRange): PyExprTranslated:=
  let (fname, args) := match func with
    | .Name _ n _ =>
      if n.val.endsWith "___init__" then
        (n.val, args.val.toList.drop 1)
      else (n.val, args.val.toList)
    | .Attribute _ v attr _ =>
        if (PyExprToString v) == "self" then (translation_ctx.currentclassname ++ "_" ++ attr.val, [v] ++ args.val.toList) else
        match v with
        | .Attribute _ v1 attr1 _ =>
          if (PyExprToString v1) == "self" then
            match translation_ctx.classinstance_attributetype.get? (translation_ctx.currentclassname, attr1.val) with
            | some ty =>
              if ty == "Any" then ("UnknownType" ++ "_" ++ attr.val, [v] ++ args.val.toList) else
                  (ty ++ "_" ++ attr.val, [v] ++ args.val.toList)
            | none => ("UnknownType" ++ "_" ++ attr.val, [v] ++ args.val.toList)
          else
            match translation_ctx.variableTypes.get? (PyExprGetRoot v)  with
              | none => (s!"{PyExprToString v}_{attr.val}", args.val.toList)
              | some x =>
                  if x == "Any" then ("UnknownType" ++ "_" ++ attr.val, [v] ++ args.val.toList) else
                    (x ++ "_" ++ attr.val, [v] ++ args.val.toList)

        | _ => match translation_ctx.variableTypes.get? (PyExprGetRoot v)  with
                | none => (s!"{PyExprToString v}_{attr.val}", args.val.toList)
                | some x =>
                    if x == "Any" then ("UnknownType" ++ "_" ++ attr.val, [v] ++ args.val.toList) else
                      (x ++ "_" ++ attr.val, [v] ++ args.val.toList)
    | _ => panic! s!"{repr func} is not a function"
  let fname := remapFname translation_ctx fname
  let args := match translation_ctx.func_infos.find? (λ x => x.name == fname) with
    | .some funcdecl => CombinePositionalAndKeywordArgs args kwords.val funcdecl
    | _ => args
  let kwords := match translation_ctx.func_infos.find? (λ x => x.name == fname) with
    | .some funcdecl => KwargsFilter kwords.val funcdecl
    | _ => kwords.val
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let trans_kwords := KwargsToCore kwords
  let trans_kwords_exprs := if kwords.size == 0 then [] else [trans_kwords.expr]
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs ++ trans_kwords_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs ++ trans_kwords_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ trans_kwords.stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs ++ trans_kwords_exprs)}
  res

partial def PyBinOpToCore (translation_ctx : TranslationContext)
                        (fname: String)
                        (sr: SourceRange)
                        (lhs: Python.expr SourceRange)
                        (rhs: Python.expr SourceRange): PyExprTranslated:=
  let args:= [lhs, rhs]
  let fname := remapFname translation_ctx fname
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs)}
  res

partial def PyUnOpToCore (translation_ctx : TranslationContext)
                        (fname: String)
                        (sr: SourceRange)
                        (arg: Python.expr SourceRange): PyExprTranslated:=
  let args:= [arg]
  let fname := remapFname translation_ctx fname
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs)}
  res

partial def PyExprToCore (translation_ctx : TranslationContext) (e : Python.expr SourceRange)
    (substitution_records : Option (List SubstitutionRecord) := none) : PyExprTranslated :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    {stmts := [], expr := record.boogieExpr}
  else
    match e with
    | .Call sr f args kwords => PyCallToCore translation_ctx f sr args kwords
    | .Constant _ c _ => {stmts := [], expr :=  PyConstToAny c}
    | .Name _ n _ =>
      match n.val with
      | "AssertionError" | "Exception" => {stmts := [], expr := .strConst () n.val}
      | s =>
        match translation_ctx.variableTypes.get? s with
        | .some p =>
          if translation_ctx.expectedType == some (.tcons "bool" []) && p == "DictStrAny"  then
            let a := .fvar () n.val none
            let e := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) a) (.intConst () 0))
            {stmts := [], expr := e}
          else
            {stmts := [], expr := .fvar () n.val none}
        | .none => {stmts := [], expr := .fvar () n.val none}
    | .JoinedStr _ ss => PyExprToCore translation_ctx ss.val[0]! -- TODO: need to actually join strings
    | .BinOp sr lhs op rhs =>
      match op with
      | .Add _ => PyBinOpToCore translation_ctx "PAdd" sr lhs rhs
      | .Sub _ => PyBinOpToCore translation_ctx "PSub" sr lhs rhs
      | .Mult _ => PyBinOpToCore translation_ctx "PMul" sr lhs rhs
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare sr lhs op rhs =>
      assert! rhs.val.size == 1
      let rhs := rhs.val[0]!
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ => PyBinOpToCore translation_ctx "PEq" sr lhs rhs
        | Strata.Python.cmpop.In _ => PyBinOpToCore translation_ctx "PIn" sr lhs rhs
        | Strata.Python.cmpop.Lt _ => PyBinOpToCore translation_ctx "PLt" sr lhs rhs
        | Strata.Python.cmpop.LtE _ => PyBinOpToCore translation_ctx "PLe" sr lhs rhs
        | Strata.Python.cmpop.Gt _ => PyBinOpToCore translation_ctx "PGt" sr lhs rhs
        | Strata.Python.cmpop.GtE _ => PyBinOpToCore translation_ctx "PGt" sr lhs rhs
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values =>
      let res := handleDict translation_ctx substitution_records keys.val values.val
      res
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp sr op arg => match op with
      | .Not _ => PyUnOpToCore translation_ctx "PNot" sr arg
      | _ => panic! "Unsupported UnaryOp: {repr e}"
    | .Subscript sr v slice ctx =>
      let sr := slice.toAst.ann
      PyBinOpToCore translation_ctx "Any_get" sr v slice
    | .List _ elmts _ => handleList elmts.val translation_ctx
    | .Attribute sr v attr _ =>
        let vCore := PyExprToCore translation_ctx v
        let tmpvar := s!"tmpvar_{sr.start}_{sr.stop}"
        let inittmpvar : Core.Statement := .init tmpvar AnyTy AnyNoneExpr
        let getattributestmt : Core.Statement :=
          .call [tmpvar] "ClassInstance_get_InstanceAttribute" [vCore.expr, .strConst () attr.val]
        let getattributestmt := addExceptionHandle translation_ctx getattributestmt sr
        {stmts:= vCore.stmts ++ [inittmpvar] ++ getattributestmt, expr:= FVar tmpvar}
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def initTmpParam (p: Python.expr SourceRange × String) : List Core.Statement :=
  match p.fst with
  | .Call _ f args _ =>
    match f with
    | .Name _ n _ =>
      match n.val with
      | "json_dumps" => [(.init p.snd t[string] (.strConst () "")),
                          .call [p.snd, "maybe_except"] "json_dumps" [(.app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")),
                          (Strata.Python.TypeStrToCoreExpr "IntOrNone")]]
      | "str" =>
        assert! args.val.size == 1
        [(.init p.snd t[string] (.strConst () "")), .set p.snd (.app () (.op () "datetime_to_str" none) ((PyExprToCore default args.val[0]!).expr))]
      | "int" => [(.init p.snd t[int] (.intConst () 0)), .set p.snd (.op () "datetime_to_int" none)]
      | _ => panic! s!"Unsupported name {n.val}"
    | _ => panic! s!"Unsupported tmp param init call: {repr f}"
  | _ => panic! "Expected Call"

partial def exceptHandlersToCoreBlock
        (translation_ctx: TranslationContext)
        (tryblockindex: String)
        (h : Python.excepthandler SourceRange) : Core.Statement :=
  match h with
  | .ExceptHandler _ ex_ty _ body =>
    let finalblocklabel := "finalblock" ++ tryblockindex
    let handler_body := body.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst) ++ [.goto finalblocklabel]
    let blockname := match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty ++ tryblockindex
      | .none => "exception" ++ tryblockindex
    (.block blockname handler_body)

partial def getErrorTypes_fromexceptHandlers (hs : List (Python.excepthandler SourceRange)) : List String :=
  hs.map (λ h =>
  match h with
  | .ExceptHandler _ ex_ty _ _ => match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty
      | .none => "exception")



partial def handleComprehension (lhs: Python.expr SourceRange) (gen: Array (Python.comprehension SourceRange)) : List Core.Statement :=
  assert! gen.size == 1
  match gen[0]! with
  | .mk_comprehension _ _ itr _ _ =>
    let res := PyExprToCore default itr
    let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) res.expr) (.intConst () 0))
    let then_ss: List Core.Statement := [.havoc (PyExprToString lhs)]
    let else_ss: List Core.Statement := [.set (PyExprToString lhs) (.op () "ListStr_nil" none)]
    res.stmts ++ [.ite guard then_ss else_ss]


partial def handleFunctionCall
        (translation_ctx : TranslationContext)
        (call_expr: Python.expr SourceRange): List Core.Statement :=
  let call_trans := PyExprToCore translation_ctx call_expr
  match call_expr with
  | (.Call sr _ _ _) =>
      let lhs : List Core.Expression.Ident := []
      match call_trans.stmts.getLast! with
      | .call _ fn args =>
          let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
          call_trans.stmts.dropLast.dropLast  ++ newcall
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call _ fn args =>
              let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
              call_trans.stmts.dropLast.dropLast.dropLast ++  newcall
          | _ => panic! s!"Expect a Call expr"
      | .init _ _ expr => call_trans.stmts.dropLast  ++  [.set lhs[0]! expr]
      | _ => panic! "expect a Call"
  | _ => panic! s!"Expect a Call expr, get {repr call_expr}"


partial def get_tempvarname_of_call_trans  (call_trans: PyExprTranslated) : String :=
  match call_trans.stmts.getLast! with
      | .call tempvarname _ _ => tempvarname[0]!.name
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call tempvarname _ _ =>tempvarname[0]!.name
          | _ => panic! s!"Expect a Call expr"
      | .init tempvarname _ _ => tempvarname.name
      | _ => panic! "expect a Call"

partial def handleAssignFunctionCall
        (translation_ctx : TranslationContext)
        (lhs:  Python.expr SourceRange)
        (call_expr: Python.expr SourceRange): List Core.Statement :=
  let call_trans := PyExprToCore translation_ctx call_expr
  match call_expr with
  | (.Call sr _ _ _) =>
    match lhs with
    | .Name _ n _ =>
      let lhs : List Core.Expression.Ident := [n.val]
      match call_trans.stmts.getLast! with
      | .call _ fn args =>
          let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
          call_trans.stmts.dropLast.dropLast  ++ newcall
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call _ fn args =>
              let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
              call_trans.stmts.dropLast.dropLast.dropLast ++  newcall
          | _ => panic! s!"Expect a Call expr"
      | .init _ _ expr => call_trans.stmts.dropLast  ++  [.set lhs[0]! expr]
      | _ => panic! "expect a Call"
    | .Subscript _ val slice _ =>
      let dictvar := FVar (PyExprToString val)
      let key := PyExprToCore translation_ctx slice
      let tempvarname := get_tempvarname_of_call_trans call_trans
      let dictset := Core.Statement.call [PyExprToString val] "Dict_set" [dictvar, key.expr, FVar tempvarname]
      let newcall := addExceptionHandle translation_ctx dictset sr
      call_trans.stmts ++ key.stmts ++ newcall
    | .Attribute _ val att _ =>
        let tempvarname := get_tempvarname_of_call_trans call_trans
        let classvar := FVar (PyExprToString val)
        let attr : Core.Expression.Expr := .strConst () att.val
        call_trans.stmts ++ [.call [PyExprToString val, "exceptvar"] "ClassInstance_init_InstanceAttribute" [classvar, attr, FVar tempvarname]]
    | _ => panic! s!"Unexpected LHS"
  | _ => panic! s!"Expect a Call expr, get {repr call_expr}"

partial def PyStmtToCore (translation_ctx : TranslationContext) (s : Python.stmt SourceRange)
        : List Core.Statement × TranslationContext :=
  --dbg_trace s!"Handling: {repr s}"
  match s with
    | .Import _ names => ([], translation_ctx)
      --([.call [] "import" [PyListStrToCore names.val]], translation_ctx)
    | .ImportFrom _ s names i => ([], translation_ctx)
      /-
      let n := match s.val with
      | some s => [strToCoreExpr s.val]
      | none => []
      let i := match i.val with
      | some i => [intToCoreExpr (PyIntToInt i)]
      | none => []
      ([.call [] "importFrom" (n ++ [PyListStrToCore names.val] ++ i)], translation_ctx)
      -/
    | .Expr _ (.Call sr func args kwords) =>
      if (PyExprToString func) ∈ IgnoredProcedures then ([], translation_ctx)
      else
        (handleFunctionCall translation_ctx (.Call sr func args kwords), translation_ctx)
    | .Expr _ (.Constant _ (.ConString _ _) _) =>
      -- TODO: Check that it's a doc string
      ([], translation_ctx) -- Doc string
    | .Expr _ _ =>
      panic! s!"Can't handle Expr statements that aren't calls: {repr s}"
    | .Assign _ lhs (.Call sr func args kwords) _ =>
      let fname := PyExprGetRoot func
      assert! lhs.val.size == 1
      let lhs := lhs.val[0]!
      let vartype := match translation_ctx.class_infos.find? (λ i => i.name == fname) with
        | .some _ => (PyExprGetRoot lhs, fname)
        | _ => (AnyTy_var (PyExprGetRoot lhs))
      let call_stmts := handleAssignFunctionCall translation_ctx lhs (.Call sr func args kwords)
      match lhs with
      | .Name _ val _ =>
          let lhs := val.val
          if isVar_inContext translation_ctx lhs then
            (call_stmts, {translation_ctx with variableTypes := translation_ctx.variableTypes.insert vartype.fst vartype.snd})
          else
            ([.init lhs AnyTy AnyNoneExpr] ++ call_stmts,
            {translation_ctx with variableTypes := translation_ctx.variableTypes.insert vartype.fst vartype.snd})
      | .Subscript _ _ _ _ => (call_stmts, translation_ctx)
      | .Attribute _ val att _ =>
          (call_stmts,
          {translation_ctx with classinstance_attributetype := translation_ctx.classinstance_attributetype.insert (translation_ctx.currentclassname, att.val) (getFunctionReturnType translation_ctx func)})
      | _ => panic! s!"Invalid LHS"
    | .Assign _ lhs rhs _ =>
      let res := PyExprToCore translation_ctx rhs
      assert! lhs.val.size == 1
      let lhs := lhs.val[0]!
      match lhs with
      | .Name _ val _ =>
          let lhs := val.val
          if isVar_inContext translation_ctx lhs then
             (res.stmts ++ [(.set lhs res.expr)],
             {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs "Any"})
          else
            (res.stmts ++ [(.init lhs AnyTy res.expr)],
            {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs "Any"})
      | .Subscript sr val slice _ =>
          let dictvar := FVar (PyExprToString val)
          let key := PyExprToCore translation_ctx slice
          let dictset := Core.Statement.call [PyExprToString val] "Dict_set" [dictvar, key.expr, res.expr]
          let dictset := addExceptionHandle translation_ctx dictset sr
          (res.stmts ++ key.stmts ++ dictset, translation_ctx)
      | .Attribute _ val att _ =>
          let classvar := FVar (PyExprToString val)
          let attr : Core.Expression.Expr := .strConst () att.val
          (res.stmts ++ [.call [PyExprToString val, "exceptvar"] "ClassInstance_init_InstanceAttribute" [classvar, attr, res.expr]], translation_ctx)
      | _ => panic! s!"Invalid LHS"
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.Call sr func args kwords))} _ =>
      let call_stmts := handleAssignFunctionCall translation_ctx lhs (.Call sr func args kwords)
      match lhs with
      | .Name _ val _ =>
          let lhs := val.val
          if isVar_inContext translation_ctx lhs then
            (call_stmts,
            {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs "Any"})
          else
            ([.init lhs AnyTy AnyNoneExpr] ++ call_stmts,
            {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs (PyExprToString ty)})
      | .Subscript _ _ _ _ => (call_stmts, translation_ctx)
      | _ => panic! s!"Invalid LHS"
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.ListComp _ _ gen))} _ => ([], translation_ctx)
    --  (handleComprehension lhs gen.val, some (PyExprToString lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty {ann := _, val := (.some e)} _ =>
      let lhs := PyExprToString lhs
      let res := (PyExprToCore {translation_ctx with expectedType := PyExprToMonoTy ty} e)
      if isVar_inContext translation_ctx lhs then
        (res.stmts ++ [(.set lhs res.expr)],
        {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs (PyExprToString ty)})
      else
        (res.stmts ++ [(.init lhs AnyTy res.expr)],
        {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs (PyExprToString ty)})
    | .Try sr body handlers _orelse finalbody =>
        let tryblockindex := s!"_{sr.start}_{sr.stop}"
        let tryblockname := "tryblock" ++ tryblockindex
        let finalblockname := "finalblock" ++ tryblockindex
        let ErrorTypes := getErrorTypes_fromexceptHandlers handlers.val.toList
        let curTryblock : TryBlockInfo := {ErrorTypes, TryBlockIndex:= tryblockindex}
        let except_handlers_blocks := handlers.val.toList.map (exceptHandlersToCoreBlock translation_ctx tryblockindex)
        let finalblockbody := finalbody.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst)
        let finalblock :=.block finalblockname finalblockbody
        let new_translation_ctx := {translation_ctx with currentTryBlock:= some curTryblock}
        let tryblockbody := ArrPyStmtToCore new_translation_ctx body.val
        let tryblock := .block tryblockname tryblockbody.fst
        let stmts : List Core.Statement := [tryblock] ++ except_handlers_blocks ++ [finalblock]
        (stmts,
        {translation_ctx with variableTypes := tryblockbody.snd.variableTypes})
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Core statement"
    | .If _ test then_b else_b =>
      let guard_ctx := {translation_ctx with expectedType := some (.tcons "bool" [])}
      let guard := PyExprToCore guard_ctx test
      let thenblock := ArrPyStmtToCore translation_ctx then_b.val
      let elseblock := ArrPyStmtToCore translation_ctx else_b.val
      (guard.stmts ++ [.ite (Any_toBool guard.expr) thenblock.fst elseblock.fst],
      {translation_ctx with variableTypes := Std.HashMap.union thenblock.snd.variableTypes elseblock.snd.variableTypes})
    | .Return _ v =>
      match v.val with
      | .some v =>
          let ret := (PyExprToCore translation_ctx v)
          (ret.stmts ++ [(.set "ret" ret.expr), (.goto "end")], translation_ctx) -- TODO: need to thread return value name here. For now, assume "ret"
      | .none => ([(.goto "end")], translation_ctx)
    | .For _ tgt itr body _ _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToCore default itr).expr) (.intConst () 0))
      match tgt with
      | .Name _ n _ =>
        let assign_tgt := [(.init n.val AnyTy AnyNoneExpr)]
        ([(.ite guard (assign_tgt ++ (ArrPyStmtToCore translation_ctx body.val).fst) [])], translation_ctx)
      | _ => panic! s!"tgt must be single name: {repr tgt}"
      -- TODO: missing havoc
    | .While _ test body _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToCore default test).expr) (.intConst () 0))
      ([(.ite guard (ArrPyStmtToCore translation_ctx body.val).fst [])], translation_ctx)
      -- TODO: missing havoc
    | .Assert pos a _ =>
      let res := PyExprToCore translation_ctx a
      let assertname := s!"py_assertion_line_{pos.start}_col_{pos.stop}"
      let assert_expr := Any_toBool res.expr
      (res.stmts ++ [(.assert assertname assert_expr)], translation_ctx)
    | .AugAssign _ lhs op rhs =>
      match op with
      | .Add _ =>
        match lhs with
        | .Name _ n _ =>
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := (.strConst () "DUMMY_FLOAT")
          (rhs.stmts ++ [(.set n.val new_lhs)], translation_ctx)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | .FloorDiv _ =>
        match lhs with
        | .Name _ n _ =>
          let lhs := PyExprToCore translation_ctx lhs
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs.expr) rhs.expr
          (rhs.stmts ++ [(.set n.val new_lhs)], translation_ctx)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | _ => panic! s!"Unsupported AugAssign op: {repr op}"
    | .Pass _ => ([], translation_ctx)
    | .Raise _ _ _ => ([.set "exceptvar" UndefinedError], translation_ctx)
    | _ => panic! s!"Unsupported {repr s}"


partial def ArrPyStmtToCore (translation_ctx: TranslationContext) (a : Array (Python.stmt SourceRange)) : (List Core.Statement × TranslationContext) :=
  a.foldl (fun (stmts, ctx) stmt =>
    let (newStmts, newCtx) := PyStmtToCore ctx stmt
    (stmts ++ newStmts, newCtx)
  ) ([], translation_ctx)

end --mutual


def translateFunctions (a : Array (Python.stmt SourceRange)) (translation_ctx: TranslationContext) : List Core.Decl :=
  a.toList.filterMap (λ s => match s with
    | .FunctionDef _ name _args body _ _ret _ _ =>

      let varDecls : List Core.Statement := []
      let proc : Core.Procedure := {
        header := {
               name := name.val,
               typeArgs := [],
               inputs := [],
               outputs := [("exceptvar", (.tcons "Error" []))]},
        spec := default,
        body := varDecls ++ (ArrPyStmtToCore translation_ctx body.val).fst ++ [.block "end" []]
      }
      some (.proc proc)
    | _ => none)

def isSubstring (needle : String) (haystack : String) : Bool :=
  let needleLen := needle.length
  let haystackLen := haystack.length
  if needleLen > haystackLen then false
  else
    (List.range (haystackLen - needleLen + 1)).any fun i =>
      String.Pos.Raw.extract haystack ⟨i⟩  ⟨i + needleLen⟩ == needle

def IsOrType (ty_str: String) : Bool := isSubstring "Or" ty_str

def pyTyStrToLMonoTy (ty_str: String) : Lambda.LMonoTy :=
  match ty_str with
  | "str" => mty[string]
  | "int" => mty[int]
  | "bool" => mty[bool]
  | "datetime" => (.tcons "Datetime" [])
  | _ =>
    if IsOrType ty_str then (.tcons "Any" []) else
      panic! s!"Unsupported type: {ty_str}"


def arg_typecheck_assertion (var: String) (ty_str: String) (default: Option (Python.expr SourceRange)): Core.Expression.Expr :=
  let constraint := match ty_str.toLower with
  | "str" => .app () (.op () "Any..isfrom_string" none) (.fvar () var none)
  | "int" => .app () (.op () "Any..isfrom_int" none) (.fvar () var none)
  | "bool" => .app () (.op () "Any..isfrom_bool" none) (.fvar () var none)
  | "datetime" => .app () (.op () "Any..isfrom_Datetime" none) (.fvar () var none)
  | "none" => .app () (.op () "Any..isfrom_None" none) (.fvar () var none)
  | _ => if ty_str.startsWith "Dict" then .app () (.op () "Any..isfrom_Dict" none) (.fvar () var none)
      else if ty_str.startsWith "List" then .app () (.op () "Any..isfrom_ListAny" none) (.fvar () var none)
      else .eq () (.app () (.op () "Any..classname" none) (.fvar () var none)) (.strConst () ty_str)
  match default with
    |.some (.Constant _ (.ConNone _) _ ) =>
      .app () (.app () (.op () "Bool.Or" none) constraint) (.app () (.op () "Any..isfrom_none" none) (.fvar () var none))
    | _ => constraint

def arg_typecheck_or_expr (var: String) (ty_strs: List String) : Core.Expression.Expr :=
  match ty_strs with
  | [] => panic! "ty_strs cannot be empty"
  | [ty] => arg_typecheck_assertion var ty none
  | ty::tys => .app () (.app () (.op () "Bool.Or" none) (arg_typecheck_assertion var ty none)) (arg_typecheck_or_expr var tys)

def getArg_typecheck_assertions (var: String) (ty: String) (default: Option (Python.expr SourceRange)): Core.Statement :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    .assert assertionname (arg_typecheck_or_expr var typelist)
  else .assert assertionname (arg_typecheck_assertion var ty default)

def getArgs_typecheck_assertions (args: List (String × String × Option (Python.expr SourceRange))) : List Core.Statement :=
  match args with
  | [] => []
  | (var, typ, default)::t => (getArg_typecheck_assertions var typ default) :: (getArgs_typecheck_assertions t)

def getArg_typecheck_precond (var: String) (ty: String) (default: Option (Python.expr SourceRange)): (Core.CoreLabel × Core.Procedure.Check) :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    (assertionname, {expr:=arg_typecheck_or_expr var typelist})
  else (assertionname, {expr:=arg_typecheck_assertion var ty default})

def getArgs_typecheck_preconds (args: List (String × String × Option (Python.expr SourceRange))) : ListMap Core.CoreLabel Core.Procedure.Check :=
  match args with
  | [] => []
  | (var, typ, default)::t => if (typ == "Any"  || typ == "kwargs") then (getArgs_typecheck_preconds t) else
            (getArg_typecheck_precond var typ default) :: (getArgs_typecheck_preconds t)

def pythonFuncToCore (name : String) (args: List (String × String × Option (Python.expr SourceRange))) (body: Array (Python.stmt SourceRange))
      (ret : Option (Python.expr SourceRange)) (spec : Core.Procedure.Spec) (translation_ctx : TranslationContext) : Core.Procedure × TranslationContext:=
  let constructor := name.endsWith "___init__"
  let args := if constructor then args.tail else args
  let inputs : List (Lambda.Identifier Core.Visibility × Lambda.LMonoTy) :=
      args.map (λ p => if p.snd.fst == "kwargs" then (p.fst, (.tcons "kwargs" [])) else (p.fst, (.tcons "Any" [])))
  let arg_typecheck := getArgs_typecheck_preconds args
  let stmts := (ArrPyStmtToCore translation_ctx body).fst
  let newctx := (ArrPyStmtToCore translation_ctx body).snd
  let body := [.set "exceptvar" (.op () "NoError" none)] ++ stmts
  let body := if constructor then
      [.init "self" AnyTy (emptyClassInstance translation_ctx.currentclassname)] ++ body ++ [.set "ret" (FVar "self")]
    else body
  let body := body ++ [.block "end" []]
  let ret_typecheck : ListMap Core.CoreLabel Core.Procedure.Check :=
    if constructor then
      let class_ty_name := name.dropRight ("___init__".length)
      [("ret_typeconstraint",
        {expr:= .eq () (.app () (.op () "Any..classname" none) (FVar "ret")) (strToCoreExpr class_ty_name)} )]
    else
      match ret with
      | some ret =>
       [("ret_typeconstraint",
        {expr:= arg_typecheck_assertion "ret" (PyExprToString ret) none})]
      | _ => []
  let newspec := {spec with preconditions:= arg_typecheck ++ spec.preconditions
                            postconditions:= ret_typecheck ++ spec.postconditions}
  let outputs : Lambda.LMonoTySignature := [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]
  /-
  let outputs : Lambda.LMonoTySignature := if not constructor then
    [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]
  else
    let class_ty_name := name.dropRight ("___init__".length)
    [("ret", (.tcons s!"{class_ty_name}" [])), ("exceptvar", (.tcons "Error" []))]-/
  let outproc := {
    header := {name,
               typeArgs := [],
               inputs,
               outputs},
    spec:=newspec,
    body
  }
  let newctx:= {translation_ctx with classinstance_attributetype:= newctx.classinstance_attributetype}
  (outproc, newctx)

def unpackPyArguments (args: Python.arguments SourceRange) : List (String × String × Option (Python.expr SourceRange)) :=
-- Python AST:
-- arguments = (arg* posonlyargs, arg* args, arg? vararg, arg* kwonlyargs,
--                  expr* kw_defaults, arg? kwarg, expr* defaults)
  match args with -- TODO: Error if any other types of args
    | .mk_arguments _ _ args _ _ _ kwargs defaults =>
      let argscount := args.val.size
      let defaultscount := defaults.val.size;
      let listdefaults := (List.range (argscount - defaultscount)).map (λ _ => none)
                        ++ defaults.val.toList.map (λ x => some x)
      let argsinfo := args.val.toList.zip listdefaults
      let argtypes :=
        argsinfo.map (λ a: Python.arg SourceRange × Option (Python.expr SourceRange) =>
        match a.fst with
          | .mk_arg _ name oty _ =>
            match oty.val with
              | .some ty => (name.val, PyExprToString ty, a.snd)
              | _ => (name.val, "Any", a.snd))
      match kwargs.val with
      | .none => argtypes
      | _ => argtypes ++ [("kw", "kwargs", none)]



def PyFuncDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × TranslationContext :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ =>
    let args := unpackPyArguments args
    let retty := match ret.val with
    | none => "UnknownType"
    | some ty => PyExprToString ty
    let funcdecl := {name := name.val, args, ret := retty}
    ([.proc (pythonFuncToCore name.val args body.val ret.val default translation_ctx).fst],
      {translation_ctx with func_infos:= translation_ctx.func_infos ++ [funcdecl]})
  | _ => panic! s!"Expected function def: {repr s}"

def PyClassDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × TranslationContext :=
  match s with
  | .ClassDef _ c_name _ _ body _ _ =>
    let member_fn_defs := body.val.toList.filterMap (λ s => match s with
      | .FunctionDef _ name args body _ ret _ _ => some (name, args, body, ret)
      | _ => none)
    let funcinfos : List PythonFunctionDecl := member_fn_defs.map (λ f =>
      let name := c_name.val++"_" ++ f.fst.val
      let args := unpackPyArguments f.snd.fst
      let args := if name.endsWith "___init__" then args.drop 1 else args
      let ret := f.snd.snd.snd.val
      let ret := match ret with
        | none => "UnknownType"
        | some ty => PyExprToString ty
      {name := name, args, ret := ret})
    let translation_ctx := {translation_ctx with func_infos:= translation_ctx.func_infos ++ funcinfos,
                                                  currentclassname := c_name.val}
    let getattributetype := match member_fn_defs.find? (λ f => f.fst.val.endsWith "init__") with
      | some f =>
          let name := c_name.val++"_" ++ f.fst.val
          let args := unpackPyArguments f.snd.fst
          let body := f.snd.snd.fst.val
          let ret := f.snd.snd.snd.val
          (pythonFuncToCore name args body ret default translation_ctx).snd
      | none => panic! s!"require a constructor {c_name.val}"
    let translation_ctx := {translation_ctx with classinstance_attributetype:= getattributetype.classinstance_attributetype}
    let funcdecls : List Core.Decl := member_fn_defs.map (λ f =>
      let name := c_name.val++"_" ++ f.fst.val
      let args := unpackPyArguments f.snd.fst
      let body := f.snd.snd.fst.val
      let ret := f.snd.snd.snd.val
      .proc (pythonFuncToCore name args body ret default translation_ctx).fst)
    let classdecl:=  {name := c_name.val}
    (funcdecls,
      {translation_ctx with class_infos := translation_ctx.class_infos ++ [classdecl], currentclassname:= ""})
  | _ => panic! s!"Expected function def: {repr s}"

mutual
partial def PythonDefToCore (pydef: Python.stmt SourceRange) (translation_ctx: TranslationContext): List Core.Decl × TranslationContext :=
  match pydef with
  | .FunctionDef _ _ _ _ _ _ _ _ => PyFuncDefToCore pydef translation_ctx
  | .ClassDef _ _ _ _ _ _ _ => PyClassDefToCore pydef translation_ctx
  | _ => ([], translation_ctx)

partial def PythonDefsToCore (a : Array (Python.stmt SourceRange)) (translation_ctx: TranslationContext)  : (List Core.Decl × TranslationContext) :=
  a.foldl (fun (decls, ctx) pydef =>
    let (newdecls, newCtx) := PythonDefToCore pydef ctx
    (decls ++ newdecls, newCtx))
  ([], translation_ctx)

end

def pythonToCore (pgm: Strata.Program): Core.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_and_class_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | .ClassDef _ _ _ _ _ _ _ => true
  | _ => false)
  let (decls, translation_ctx) := PythonDefsToCore func_and_class_defs default

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | .ClassDef _ _ _ _ _ _ _ => false
  | _ => true)

  let globals := [(.var "__name__" AnyTy (strToAny "__main__"))]
  let mainfunction := Core.Decl.proc (pythonFuncToCore "__main__" [] non_func_blocks none default translation_ctx).fst
  {decls := globals ++ decls ++  [mainfunction]}

def get_proc_body (pname: String) (decls: List Core.Decl) : List Core.Statement:=
  match decls.find? (λ d => d.name.name == pname) with
  | none => []
  | .some proc => match proc.getProc? with
                    | .none => panic!"Expect a procedure"
                    | .some proc  => proc.body



mutual
partial def get_dependence_proc_from_stmt (st: Core.Statement) (p: Core.Program) (acc: List String): List String  := match st with
  | .cmd cmd =>
    match cmd with
    | .call _ pname _ _ =>
        if  pname ∈ acc then acc else
        get_dependence_proc_from_stmts (get_proc_body pname p.decls) p (acc ++ [pname])
    | _ => acc
  | .goto _ _ => acc
  | .block _ bss _ => get_dependence_proc_from_stmts bss p acc
  | .ite _ tbss ebss _ =>
      let thenb := get_dependence_proc_from_stmts tbss p acc
      get_dependence_proc_from_stmts ebss p thenb
  | .loop _ _ _ bss  _ => get_dependence_proc_from_stmts bss p acc


partial def get_dependence_proc_from_stmts (st: List Core.Statement) (p: Core.Program) (acc: List String): List String  := match st with
  | [] => acc
  | h :: t =>
    let proc_h := get_dependence_proc_from_stmt h p acc
    get_dependence_proc_from_stmts t p proc_h

end

def exitFailure {α} (message : String) : IO α := do
  IO.eprintln (message  ++ "\n\nRun strata --help for additional help.")
  IO.Process.exit 1

def readPythonStrata (path : String) : IO Strata.Program := do
  let bytes ← Strata.Util.readBinInputSource path
  if ! Ion.isIonFile bytes then
    exitFailure s!"pyAnalyze expected Ion file"
  match Strata.Program.fileFromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok p => pure p
  | .error msg => exitFailure msg


def getCoreProgram (path : String) : IO Core.Program := do
  let pgm ← readPythonStrata path
  let bpgm := Strata.pythonToCore pgm
  let preludePgm := Core.Typeprelude
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls}
  let mainprocbody := match bpgm.decls.getLast!.getProc? with
  | .some proc => proc.body
  | _ => panic! "Expect a proc"
  let depend_proc := get_dependence_proc_from_stmts mainprocbody newPgm []
  let declfilter:= newPgm.decls.filter (λ d => d.getProc?.isNone || d.name.name ∈ depend_proc)
  IO.print s!"{depend_proc}"
  let newPgm : Core.Program := { decls := bpgm.decls}
  return newPgm


def verifyCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls}
  let mainprocbody := match bpgm.decls.getLast!.getProc? with
  | .some proc => proc.body
  | _ => panic! "Expect a proc"
  let depend_proc := get_dependence_proc_from_stmts mainprocbody newPgm []
  let declfilter:= newPgm.decls.filter (λ d => d.getProc?.isNone || d.name.name ∈ depend_proc)
  let newPgm : Core.Program := { decls := declfilter}
  let verboseMode := VerboseMode.ofBool false
  let vcResults ← IO.FS.withTempDir (fun tempDir =>
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify "cvc5" newPgm tempDir
              { Options.default with stopOnFirstError := false, verbose := verboseMode, removeIrrelevantAxioms := true }
                                      (moreFns := Strata.Python.ReFactory)))
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  IO.println s

def verifyInliningCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls}
  let newPgm :=  runInlineCall newPgm
  let filterdecls := newPgm.decls.filter (λ d => ! d.name.name ∈ Strata.PyOps)
  let newPgm: Core.Program := { decls := filterdecls}
  IO.print newPgm
  let verboseMode := VerboseMode.ofBool false
  let vcResults ← IO.FS.withTempDir (fun tempDir =>
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify "cvc5" newPgm tempDir
              { Options.default with stopOnFirstError := false, verbose := verboseMode, removeIrrelevantAxioms := true }
                                      (moreFns := Strata.Python.ReFactory)))
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  IO.println s

def typecheckCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls.take 12 }
  let options := { Options.default with stopOnFirstError := false, verbose:= VerboseMode.ofBool true, removeIrrelevantAxioms := false}
  let peval := Core.typeCheck options newPgm
  match peval with
  | .ok pval => IO.println s!"{pval}"
  | _ => IO.println s!"partial evaluation failed"

def partialEvalCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  let options := { Options.default with stopOnFirstError := false, verbose:= VerboseMode.ofBool true, removeIrrelevantAxioms := false}
  let peval := Core.typeCheckAndPartialEval options newPgm
  match peval with
  | .ok pval => IO.println s!"{pval[0]!.fst}"
  | _ => IO.println s!"partial evaluation failed"

def partialEvalInliningCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  let newPgm :=  runInlineCall newPgm
  let options := { Options.default with stopOnFirstError := false, verbose:= VerboseMode.ofBool false, removeIrrelevantAxioms := false}
  let peval := Core.typeCheckAndPartialEval options newPgm
  match peval with
  | .ok pval =>
      for p in pval do
        IO.println s!"Branch"
        IO.println s!"{p.fst}"
  | _ => IO.println s!"partial evaluation failed"

end Strata
