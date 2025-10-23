import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Python.PythonDialect

namespace Strata

-- Some hard-coded things we'll need to fix later:

def clientType : Boogie.Expression.Ty := .forAll [] (.tcons "Client" [])
def dummyClient : Boogie.Expression.Expr := .fvar "DUMMY_CLIENT" none

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
  .const s none

def intToBoogieExpr (i: Int) : Boogie.Expression.Expr :=
  .const s!"{i}" none

def PyIntToInt (i : Python.int) : Int :=
  match i with
  | .IntPos n => n
  | .IntNeg n => -n

def PyConstToBoogie (c: Python.constant) : Boogie.Expression.Expr :=
  match c with
  | .ConString s => .const s none
  | _ => panic! s!"Unhandled Constant: {repr c}"

def PyAliasToBoogieExpr (a : Python.alias) : Boogie.Expression.Expr :=
  match a with
  | .mk_alias n as_n =>
  assert! as_n.isNone
  .const n none

partial def PyExprToBoogie (e : Python.expr) : Boogie.Expression.Expr :=
  match e with
  | .Call _ _ _ => panic! s!"Call should be handled at stmt level: {repr e}"
  | .Constant c _ => PyConstToBoogie c
  | .Name n _ => .const n none
  | .JoinedStr ss => PyExprToBoogie ss[0]! -- TODO: need to actually join strings
  | _ => panic! s!"Unhandled Expr: {repr e}"

def PyExprToString (e : Python.expr) : String :=
  match e with
  | .Name n _ => n
  | .Attribute v attr _ => s!"{PyExprToString v}.{attr}"
  | _ => panic! s!"Unhandled Expr: {repr e}"

def handleCallThrow (jmp_target : String) : Boogie.Statement :=
  let cond := .eq (.app (.fvar "ExceptOrNone_tag" none) (.fvar "maybe_except" none)) (.fvar "EN_STR_TAG" none)
  .ite cond {ss := [.goto jmp_target]} {ss := []}

mutual

partial def exceptHandlersToBoogie (jmp_targets: List String) (h : Python.excepthandler) : List Boogie.Statement :=
  assert! jmp_targets.length >= 2
  match h with
  | .ExceptHandler ex_ty _ body =>
    let set_ex_ty_matches := match ex_ty with
    | .some ex_ty =>
      .call ["exception_ty_matches"] "checkExceptionTyMatches" [PyExprToBoogie ex_ty]
    | .none =>
      .call ["exception_ty_matches"] "checkExceptionTyMatches" []
    let cond := .fvar "exception_ty_matches" none
    let body_if_matches := body.toList.flatMap (PyStmtToBoogie jmp_targets) ++ [.goto jmp_targets[1]!]
    [set_ex_ty_matches, .ite cond {ss := body_if_matches} {ss := []}]


partial def PyStmtToBoogie (jmp_targets: List String) (s : Python.stmt) : List Boogie.Statement :=
  assert! jmp_targets.length > 0
  let non_throw := match s with
    | .Import names =>
      [.call [] "import" (names.toList.map PyAliasToBoogieExpr)]
    | .ImportFrom s names i =>
      let n := match s with
      | some s => [strToBoogieExpr s]
      | none => []
      let i := match i with
      | some i => [intToBoogieExpr (PyIntToInt i)]
      | none => []
      [.call [] "importFrom" (n ++ (names.toList.map PyAliasToBoogieExpr) ++ i)]
    | .Expr (.Call func args _) =>
      [.call [] (PyExprToString func) (args.toList.map PyExprToBoogie)]
    | .Expr _ =>
      dbg_trace "Can't handle Expr statements that aren't calls"
      assert! false
      [.assert "expr" (.const "true" none)]
    | .Assign lhs (.Call func args _) _ =>
      assert! lhs.size == 1
      [.call [PyExprToString lhs[0]!] (PyExprToString func) (args.toList.map PyExprToBoogie)]
    | .Assign lhs rhs _ =>
      assert! lhs.size == 1
      [.set (PyExprToString lhs[0]!) (PyExprToBoogie rhs)]
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

  -- let stmts := unwrapSeq insideMod
  let varDecls : List Boogie.Statement := [(.init "s3_client" clientType dummyClient),
                                           (.havoc "s3_client"),
                                           (.init "invalid_client" clientType dummyClient),
                                           (.havoc "invalid_client"),
                                           (.init "exception_ty_matches" clientType dummyClient),
                                           (.havoc "exception_ty_matches")]
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
