import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Python.PythonDialect
import StrataTest.Internal.FunctionSignatures

namespace Strata
open Lambda.LTy.Syntax
-- Some hard-coded things we'll need to fix later:

def clientType : Boogie.Expression.Ty := .forAll [] (.tcons "Client" [])
def dummyClient : Boogie.Expression.Expr := .fvar "DUMMY_CLIENT" none

def dictStrAnyType : Boogie.Expression.Ty := .forAll [] (.tcons "DictStrAny" [])
def dummyDictStrAny : Boogie.Expression.Expr := .fvar "DUMMY_DICT_STR_ANY" none

def strType : Boogie.Expression.Ty := .forAll [] (.tcons "string" [])
def dummyStr : Boogie.Expression.Expr := .fvar "DUMMY_STR" none


-- This information should come from our prelude. For now, we use the fact that
-- these functions are exactly the ones
-- represented as `Call(Attribute(Name(...)))` in the AST (instead of `Call(Name(...))`).
def callCanThrow (stmt: Python.stmt) : Bool :=
  match stmt with
  | .Expr (.Call (.Attribute _ _ _) _ _) => true
  | .Assign _ (.Call (.Attribute _ _ _) _ _) _ => true
  | _ => false

-------------------------------------------------------------------------------


def toPyCommands (a : Array Operation) : Array Python.Command :=
  a.map (λ op => match Python.Command.ofAst op with
    | .error e => panic! s!"Failed to translate to Python.Command: {e}"
    | .ok cmd => cmd)

def unwrapModule (c : Python.Command) : Array Python.stmt :=
  match c with
  | Python.Command.Module body _ => body
  | _ => panic! "Expected module"

def strToBoogieExpr (s: String) : Boogie.Expression.Expr :=
  .const s mty[string]

def intToBoogieExpr (i: Int) : Boogie.Expression.Expr :=
  .const s!"{i}" mty[int]

def PyIntToInt (i : Python.int) : Int :=
  match i with
  | .IntPos n => n
  | .IntNeg n => -n

def PyConstToBoogie (c: Python.constant) : Boogie.Expression.Expr :=
  match c with
  | .ConString s => .const s mty[string]
  | .ConPos i => .const s!"{i}" mty[int]
  | .ConNeg i => .const s!"-{i}" mty[int]
  | _ => panic! s!"Unhandled Constant: {repr c}"

def PyAliasToBoogieExpr (a : Python.alias) : Boogie.Expression.Expr :=
  match a with
  | .mk_alias n as_n =>
  assert! as_n.isNone
  .const n mty[string]

partial def PyExprToBoogie (e : Python.expr) : Boogie.Expression.Expr :=
  match e with
  | .Call _ _ _ => panic! s!"Call should be handled at stmt level: {repr e}"
  | .Constant c _ => PyConstToBoogie c
  | .Name n _ =>
    match n with
    | "AssertionError" | "Exception" => .const n mty[string]
    | _ => .fvar n none
  | .JoinedStr ss => PyExprToBoogie ss[0]! -- TODO: need to actually join strings
  | _ => panic! s!"Unhandled Expr: {repr e}"

def PyExprToString (e : Python.expr) : String :=
  match e with
  | .Name n _ => n
  | .Attribute v attr _ => s!"{PyExprToString v}_{attr}"
  | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyKWordsToBoogie (kw : Python.keyword) : (String × Boogie.Expression.Expr) :=
  match kw with
  | .mk_keyword name expr =>
    match name with
    | some n => (n, PyExprToBoogie expr)
    | none => panic! "Keyword arg should have a name"

-- TODO: we should be checking that args are right
open Strata.Python.Internal in
def argsAndKWordsToCanonicalList (fname: String) (args : Array Python.expr) (kwords: Array Python.keyword) : List Boogie.Expression.Expr :=
  -- TODO: we need a more general solution for other functions
  if fname == "print" then
    args.toList.map PyExprToBoogie
  else
    let required_order := getFuncSigOrder fname
    assert! args.size <= required_order.length
    let remaining := required_order.drop args.size
    let kws_and_exprs := kwords.toList.map PyKWordsToBoogie
    let ordered_remaining_args := remaining.map (λ n => match kws_and_exprs.find? (λ p => p.fst == n) with
      | .some p =>
        let type_str := getFuncSigType fname n
        if type_str.endsWith "OrNone" then
          -- Optional param. Need to wrap e.g., string into StrOrNone
          match type_str with
          | "StrOrNone" => .app (.op "StrOrNone_mk_str" none) p.snd
          | "BytesOrStrOrNone" => .app (.op "BytesOrStrOrNone_mk_str" none) p.snd
          | _ => panic! "Unsupported type_str: "++ type_str
        else
          p.snd
      | .none => TypeStrToBoogieExpr (getFuncSigType fname n))
    args.toList.map PyExprToBoogie ++ ordered_remaining_args

def handleCallThrow (jmp_target : String) : Boogie.Statement :=
  let cond := .eq (.app (.op "ExceptOrNone_tag" none) (.fvar "maybe_except" none)) (.op "EN_STR_TAG" none)
  .ite cond {ss := [.goto jmp_target]} {ss := []}

-- TODO: handle rest of names
def PyListStrToBoogie (names : Array Python.alias) : Boogie.Expression.Expr :=
  -- ListStr_cons names[0]! (ListStr_nil)
  .app (.app (.op "ListStr_cons" mty[string → (ListStr → ListStr)]) (PyAliasToBoogieExpr names[0]!))
       (.op "ListStr_nil" mty[ListStr])


mutual

partial def exceptHandlersToBoogie (jmp_targets: List String) (h : Python.excepthandler) : List Boogie.Statement :=
  assert! jmp_targets.length >= 2
  match h with
  | .ExceptHandler ex_ty _ body =>
    let set_ex_ty_matches := match ex_ty with
    | .some ex_ty =>
      let inherits_from : Boogie.BoogieIdent := (.unres, "inheritsFrom")
      let get_ex_tag : Boogie.BoogieIdent := (.unres, "ExceptOrNone_code_val")
      let exception_ty : Boogie.Expression.Expr := .app (.op get_ex_tag none) (.fvar "maybe_except" none)
      let rhs_curried : Boogie.Expression.Expr := .app (.op inherits_from none) exception_ty
      let rhs : Boogie.Expression.Expr := .app rhs_curried ((PyExprToBoogie ex_ty))
      let call := .set "exception_ty_matches" rhs
      [call]
    | .none =>
      [.set "exception_ty_matches" (.const "false" mty[bool])]
    let cond := .fvar "exception_ty_matches" none
    let body_if_matches := body.toList.flatMap (PyStmtToBoogie jmp_targets) ++ [.goto jmp_targets[1]!]
    set_ex_ty_matches ++ [.ite cond {ss := body_if_matches} {ss := []}]


partial def PyStmtToBoogie (jmp_targets: List String) (s : Python.stmt) : List Boogie.Statement :=
  assert! jmp_targets.length > 0
  let non_throw := match s with
    | .Import names =>
      [.call [] "import" [PyListStrToBoogie names]]
    | .ImportFrom s names i =>
      let n := match s with
      | some s => [strToBoogieExpr s]
      | none => []
      let i := match i with
      | some i => [intToBoogieExpr (PyIntToInt i)]
      | none => []
      [.call [] "importFrom" (n ++ [PyListStrToBoogie names] ++ i)] | .Expr (.Call func args kwords) =>
      let fname := PyExprToString func
      [.call [] fname (argsAndKWordsToCanonicalList fname args kwords)]
    | .Expr _ =>
      dbg_trace "Can't handle Expr statements that aren't calls"
      assert! false
      [.assert "expr" (.const "true" mty[bool])]
    | .Assign lhs (.Call func args kwords) _ =>
      assert! lhs.size == 1
      let fname := PyExprToString func
      [.call [PyExprToString lhs[0]!, "maybe_except"] fname (argsAndKWordsToCanonicalList fname args kwords)]
    | .Assign lhs rhs _ =>
      assert! lhs.size == 1
      [.set (PyExprToString lhs[0]!) (PyExprToBoogie rhs)]
    | .AnnAssign lhs _ (.some (.Call func args kwords)) _ =>
      let fname := PyExprToString func
      [.call [PyExprToString lhs, "maybe_except"] fname (argsAndKWordsToCanonicalList fname args kwords)]
    | .AnnAssign lhs _ (.some e) _ =>
      [.set (PyExprToString lhs) (PyExprToBoogie e)]
    | .Try body handlers _orelse _finalbody =>
        let new_target := s!"excepthandlers_{jmp_targets[0]!}"
        let entry_except_handlers := [.block new_target {ss := []}]
        let new_jmp_stack := new_target :: jmp_targets
        let except_handlers := handlers.toList.flatMap (exceptHandlersToBoogie new_jmp_stack)
        body.toList.flatMap (PyStmtToBoogie new_jmp_stack) ++ entry_except_handlers ++ except_handlers
    | _ =>
      panic! s!"Unsupported {repr s}"
  if callCanThrow s then
    non_throw ++ [handleCallThrow jmp_targets[0]!]
  else
    non_throw

end --mutual

def ArrPyStmtToBoogie (a : Array Python.stmt) : List Boogie.Statement :=
  a.toList.flatMap (PyStmtToBoogie ["end"])

def pythonToBoogie (pgm: Strata.Program): Boogie.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!

  let varDecls : List Boogie.Statement := [(.init "s3_client" clientType dummyClient),
                                           (.havoc "s3_client"),
                                           (.init "invalid_client" clientType dummyClient),
                                           (.havoc "invalid_client"),
                                           (.init "exception_ty_matches" t[bool] (.const "true" mty[bool])),
                                           (.havoc "exception_ty_matches"),
                                           (.init "result" dictStrAnyType dummyDictStrAny),
                                           (.havoc "result"),
                                           (.init "object_content" strType dummyStr),
                                           (.havoc "object_content"),
                                           (.init "valid_bucket_name" strType dummyStr),
                                           (.havoc "valid_bucket_name"),
                                           (.init "valid_object_key" strType dummyStr),
                                           (.havoc "valid_object_key"),
                                           (.init "invalid_bucket_name" t[int] (.const "0" mty[int])),
                                           (.havoc "invalid_bucket_name"),
                                           (.init "invalid_object_key" t[int] (.const "0" mty[int])),
                                           (.havoc "invalid_object_key"),
                                           (.init "bucket_name" strType dummyStr),
                                           (.havoc "bucket_name"),
                                           (.init "object_key" strType dummyStr),
                                           (.havoc "object_key"),]
  let blocks := ArrPyStmtToBoogie insideMod
  let body := varDecls ++ blocks ++ [.block "end" {ss := []}]
  let mainProc : Boogie.Procedure := {
    header := {name := "simple1_btg_main",
               typeArgs := [],
               inputs := [],
               outputs := [("maybe_except", (.tcons "ExceptOrNone" []))]},
    spec := default,
    body := body
  }
  {decls := [.proc mainProc]}

end Strata
