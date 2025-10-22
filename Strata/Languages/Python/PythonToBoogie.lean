import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.DDMTransform.Parse

import Strata.Languages.Boogie.Boogie

namespace Strata


-- def translate_expr (e : C_Simp.Expression.Expr) : Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent :=
--   match e with
--   | .const c ty => .const c ty
--   | .op o ty => .op (.unres, o) ty
--   | .bvar n => .bvar n
--   | .fvar n ty => .fvar (.unres, n) ty
--   | .mdata i e => .mdata i (translate_expr e)
--   | .abs ty e => .abs ty (translate_expr e)
--   | .quant k ty tr e => .quant k ty (translate_expr tr) (translate_expr e)
--   | .app fn e => .app (translate_expr fn) (translate_expr e)
--   | .ite c t e => .ite (translate_expr c) (translate_expr t) (translate_expr e)
--   | .eq e1 e2 => .eq (translate_expr e1) (translate_expr e2)

-- def translate_opt_expr (e : Option C_Simp.Expression.Expr) : Option (Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent) :=
--   match e with
--   | some e => translate_expr e
--   | none => none

-- def translate_cmd (c: C_Simp.Command) : Boogie.Command :=
--   match c with
--   | .init name ty e _md => .cmd (.init (.unres, name) ty (translate_expr e) {})
--   | .set name e _md => .cmd (.set (.unres, name) (translate_expr e) {})
--   | .havoc name _md => .cmd (.havoc (.unres, name) {})
--   | .assert label b _md => .cmd (.assert label (translate_expr b) {})
--   | .assume label b _md =>  .cmd (.assume label (translate_expr b) {})

-- partial def translate_stmt (s: Imperative.Stmt C_Simp.Expression C_Simp.Command) : Boogie.Statement :=
--   match s with
--   | .cmd c => .cmd (translate_cmd c)
--   | .block l b _md => .block l {ss := b.ss.map translate_stmt} {}
--   | .ite cond thenb elseb _md => .ite (translate_expr cond) {ss := thenb.ss.map translate_stmt} {ss := elseb.ss.map translate_stmt} {}
--   | .loop guard measure invariant body _md => .loop (translate_expr guard) (translate_opt_expr measure) (translate_opt_expr invariant) {ss := body.ss.map translate_stmt} {}
--   | .goto label _md => .goto label {}


-- mutual
-- partial def pyArgToBoogieArg (c: Arg) : Boogie.Statement :=
--   match c with
--   | .op o =>
--     match o.name with
--     | {dialect := "Python", name:= "FunctionDef"} => .op {name := {dialect := "Boogie", name:= "Procedure"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "mk_arguments"} => .op {name := {dialect := "Boogie", name:= "mk_arguments"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "mk_arg"} => .op {name := {dialect := "Boogie", name:= "mk_arg"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Name"} => .op {name := {dialect := "Boogie", name:= "Ident"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Load"} => .op {name := {dialect := "Boogie", name:= "Load"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Pass"} => .op {name := {dialect := "Boogie", name:= "Pass"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Constant"} =>
--       match o.args with
--       | #[arg] => pyArgToBoogieArg arg
--       | _ => panic! "Expected 1 arg for Constant"
--     | {dialect := "Python", name:= "ConNone"} => .op {name := {dialect := "Boogie", name:= "ConNone"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Store"} => .op {name := {dialect := "Boogie", name:= "Store"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "BinOp"} => .op {name := {dialect := "Boogie", name:= "BinOp"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Add"} => .op {name := {dialect := "Boogie", name:= "Add"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "IntPos"} => .num 1
--     | {dialect := "Python", name:= "Return"} => .op {name := {dialect := "Boogie", name:= "Return"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "ConPos"} => .op {name := {dialect := "Boogie", name:= "ConPos"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "AnnAssign"} => .op {name := {dialect := "Boogie", name:= "AnnAssign"}, args := o.args.map pyArgToBoogieArg}
--     | {dialect := "Python", name:= "Assert"} => .op {name := {dialect := "Boogie", name:= "assert"}, args := o.args.map pyArgToBoogieArg}
--     | _ => panic! s!"Unimplemented: {o.name}"
--   | .cat cat => panic! "Unsupported: cat"
--   | .expr e => panic! "Unsupported: expr"
--   | .type e => panic! "Unsupported: type"
--   | .ident i => panic! "Unsupported: ident"
--   | .num _ | .decimal _ | .strlit _ => c
--   | .option l => .option (l.map pyArgToBoogieArg)
--   | .seq l => .seq (l.map pyArgToBoogieArg)
--   | .commaSepList l => panic! "Unsupported: commaSepList"


-- partial def pyCmdToBoogieCmd (c: Operation) : Operation :=
--   match c.name with
--   | {dialect := "Python", name:= "Module"} =>
--     {c with args := c.args.map pyArgToBoogieArg}
--   | _ => c
-- end


-- Some hard-coded things we'll need to fix later:

def clientType : Boogie.Expression.Ty := .forAll [] (.tcons "Client" [])
def dummyClient : Boogie.Expression.Expr := .fvar "DUMMY_CLIENT" none

-- This information should come from our prelude. For now, we use the fact that
-- these functions are exactly the ones
-- represented as `Call(Attribute(Name(...)))` in the AST (instead of `Call(Name(...))`).
def callCanThrow (op: Operation) : Bool :=
  match op.name with
  | {dialect := "Python", name:= "Call"} =>
    match op.args[0]! with
    | .op op =>
      match op.name with
      | {dialect := "Python", name:= "Attribute"} => true
      | _ => false
    | _ => false
  | _ => false


-------------------------------------------------------------------------------

partial def collectCalls (a : Arg) : List Operation :=
  match a with
  | .op op =>
    let nested := op.args.toList.flatMap collectCalls
    match op.name with
    | {dialect := "Python", name:= "Call"} => op :: nested
    | _ => nested
  | .seq args => args.toList.flatMap collectCalls
  | _ => []

-- def baseDialects : Strata.Elab.LoadedDialects := .builtin
-- def defaultDialects : Strata.Elab.LoadedDialects := baseDialects.addDialect! Strata.Boogie

partial def argToExpr(arg: Arg) : Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent :=
  match arg with
  | .strlit s => .const s none
  | .op op => match op.name with
    | {dialect := "Python", name:= "Name"} =>
      match op.args with
      | #[.strlit name, _] => .fvar (.unres, name) none
      | _ => panic! "Invalid Name"
    | {dialect := "Python", name:= "Constant"} =>
      match op.args with
      | #[.op inner, .option _] => argToExpr (.op inner)
      | _ => panic! "Invalid Constant"
    | {dialect := "Python", name:= "ConString"} =>
      match op.args with
      | #[.strlit s] => .const s none
      | _ => panic! "Invalid ConString"
    | {dialect := "Python", name:= "mk_keyword"} => .const "keyword" none
    | {dialect := "Python", name:= "mk_alias"} =>
      let args := op.args
      assert! args.size == 2 -- List of strlit, none
      assert! args[1]! == Strata.Arg.option none
      argToExpr args[0]!
    | _ => panic! s!"Unsupported expr: {op.name}"
  | .option _ => .const "none" none
  | _ => panic! "Unsupported arg in expr"

partial def extractCallArgs(args: Array Arg) : List (Lambda.LExpr Lambda.LMonoTy Boogie.BoogieIdent) :=
  let results := args.toList.map fun arg =>
    match arg with
    | .op op => match op.name with
      | {dialect := "Python", name:= "mk_keyword"} => []
      | _ => [argToExpr arg]
    | .seq innerArgs => innerArgs.toList.filterMap fun inner =>
        match inner with
        | Arg.op op => match op.name with
          | {dialect := "Python", name:= "mk_keyword"} => none
          | _ => some (argToExpr inner)
        | _ => none
    | _ => []
  results.foldl (· ++ ·) []

def unwrapModule (ops: Array Operation): Array Arg :=
  match ops with
  | #[op] =>
    match op.name with
    | {dialect := "Python", name:= "Module"} => op.args
    | _ => panic! "Expected top-level module"
  | _ => panic! "Expected unique top-level module"

partial def pyOpToBoogie(op: Operation) : List Boogie.Statement :=
  match op.name with
  | {dialect := "Python", name:= "ImportFrom"} =>
    let callArgs := extractCallArgs op.args
    [.call [] "importFrom" callArgs]
  | {dialect := "Python", name:= "Import"} =>
    let callArgs := extractCallArgs op.args
    [.call [] "import" callArgs]
  | {dialect := "Python", name:= "Expr"} =>
    match op.args with
    | #[.op callOp] => pyOpToBoogie callOp
    | _ => []
  | {dialect := "Python", name:= "Call"} =>
    if op.args.size >= 1 then
      match op.args[0]! with
      | .op nameOp => match nameOp.name with
        | {dialect := "Python", name:= "Name"} =>
          match nameOp.args with
          | #[.strlit fname, _] =>
            let callArgs := extractCallArgs (op.args.extract 1 op.args.size)
            [.call [] fname callArgs]
          | _ => []
        | _ => []
      | _ => []
    else []
  | {dialect := "Python", name:= "Assign"} =>
    if op.args.size >= 2 then
      match op.args[0]!, op.args[1]! with
      | .seq targetSeq, .op valueOp =>
        if targetSeq.size >= 1 then
          match targetSeq[0]! with
          | .op targetOp => match targetOp.name with
            | {dialect := "Python", name:= "Name"} =>
              match targetOp.args with
              | #[.strlit varName, _] =>
                match valueOp.name with
                | {dialect := "Python", name:= "Call"} =>
                  if valueOp.args.size >= 1 then
                    match valueOp.args[0]! with
                    | .op callTarget => match callTarget.name with
                      | {dialect := "Python", name:= "Attribute"} =>
                        if callTarget.args.size >= 3 then
                          match callTarget.args[0]!, callTarget.args[1]!, callTarget.args[2]! with
                          | .op objOp, .strlit methodName, _ =>
                            match objOp.name with
                            | {dialect := "Python", name:= "Name"} =>
                              match objOp.args with
                              | #[.strlit objName, _] =>
                                let args := extractCallArgs (valueOp.args.extract 1 valueOp.args.size)
                                [.call [varName] s!"{objName}_{methodName}" args]
                              | _ => []
                            | _ => []
                          | _, _, _ => []
                        else []
                      | _ => []
                    | _ => []
                  else []
                | _ => []
              | _ => []
            | _ => []
          | _ => []
        else []
      | _, _ => []
    else []
  | {dialect := "Python", name:= "Try"} =>
    if op.args.size >= 1 then
      match op.args[0]! with
      | .seq bodyStmts => bodyStmts.toList.flatMap fun arg =>
          match arg with
          | .op o => pyOpToBoogie o
          | _ => []
      | .op bodyOp => pyOpToBoogie bodyOp
      | _ => []
    else []
  | _ => []

partial def pyStmtToBoogie(arg: Arg) : List Boogie.Statement :=
  match arg with
  | .op op => pyOpToBoogie op
  | .seq args => args.toList.flatMap pyStmtToBoogie
  | _ => []

def unwrapSeq (args: Array Arg): List Arg :=
  args.toList.flatMap fun arg =>
    match arg with
    | .seq stmts => stmts.toList
    | _ => [arg]

def handleCallThrow : Boogie.Statement :=
  let cond := .eq (.app (.fvar "ExceptOrNone_tag" none) (.fvar "maybe_except" none)) (.fvar "EN_STR_TAG" none)
  .ite cond {ss := [.goto "end"]} {ss := []}

partial def translateStmtsWithSplits (stmts: List Arg) (startIdx: Nat := 0) : List Boogie.Statement :=
  match stmts.findIdx? (fun arg => (collectCalls arg).any callCanThrow) with
  | none => 
    let blockStmts := stmts.flatMap pyStmtToBoogie
    if blockStmts.isEmpty then [] else [.block s!"anon{startIdx}" {ss := blockStmts}]
  | some idx =>
    let (beforeCall, afterCall) := (stmts.take (idx + 1), stmts.drop (idx + 1))
    let blockStmts := beforeCall.flatMap pyStmtToBoogie ++ [handleCallThrow]
    [.block s!"anon{startIdx}" {ss := blockStmts}] ++ translateStmtsWithSplits afterCall (startIdx + 2)

def pythonToBoogie (pgm: Strata.Program): Boogie.Program :=
  let insideMod := unwrapModule pgm.commands
  let stmts := unwrapSeq insideMod
  let varDecls : List Boogie.Statement := [(.init "s3_client" clientType dummyClient), (.havoc "s3_client"), (.init "invalid_client" clientType dummyClient), (.havoc "invalid_client")]
  let blocks := translateStmtsWithSplits stmts
  let body := varDecls ++ blocks ++ [.block "end" {ss := []}]
  let mainProc : Boogie.Procedure := {
    header := {name := "simple1_btg_main", typeArgs := [], inputs := [], outputs := [("maybe_except", (.tcons "ExceptOrNone" []))]},
    spec := default,
    body := body
  }
  {decls := [.proc mainProc]}


end Strata
