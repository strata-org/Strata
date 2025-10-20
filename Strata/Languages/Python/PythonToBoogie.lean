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


-- def baseDialects : Strata.Elab.LoadedDialects := .builtin
-- def defaultDialects : Strata.Elab.LoadedDialects := baseDialects.addDialect! Strata.Boogie

partial def pyOpToBoogie(op: Operation) : Option Boogie.Statement :=
  match op.name with
  | {dialect := "Python", name:= "mk_arguments"} => none
  | {dialect := "Python", name:= "Assert"} => some (.assert "assert_0" (.const "false" none))
  | _ => panic! "Unsupported"


partial def pyStmtToStmt(arg: Arg) : Option Boogie.Statement :=
  match arg with
  | .op op => pyOpToBoogie op
  | .cat _ => dbg_trace "cat"; none
  | .expr _ => dbg_trace "expr"; none
  | .type _ => dbg_trace "type"; none
  | .ident _ => dbg_trace "ident"; none
  | .num _ => dbg_trace "num"; none
  | .decimal _ => dbg_trace "decimal"; none
  | .strlit _ => dbg_trace "strlit"; none
  | .option _ => dbg_trace "option"; none
  | .seq args =>
    match args with
    | #[] => none
    | _ =>
      let stmts := (args.toList.map pyStmtToStmt).filterMap id
      some (.block "block" {ss := stmts})
  | .commaSepList _ => dbg_trace "commaseplist"; none


def pyBodyToStmts(args: Array Arg) : List Boogie.Statement :=
  dbg_trace s!"num args in body: {args.size}"
  (args.toList.map pyStmtToStmt).filterMap id

def pyFuncDefToBoogie(arg: Arg) : Boogie.Procedure :=
  match arg with
  | .op op => match op.name with
    | {dialect := "Python", name:= "FunctionDef"} =>
      {header := {name := "test", typeArgs := [], inputs := [], outputs := []}, spec:= default, body := pyBodyToStmts op.args}
    | _ => panic! "Should be function def"
  | _ => panic! "Should be function def"


partial def getFuncs (remaining :List Arg): List Arg :=
  match remaining with
  | [] => []
  | h :: tail =>
    let h' := match h with
    | .op op => match op.name with
      | {dialect := "Python", name:= "FunctionDef"} => [h]
      | _ => []
    | .seq args => getFuncs args.toList ++ getFuncs tail
    | _ => []
    h' ++ getFuncs tail

def unwrapModule (ops: Array Operation): Array Arg :=
  match ops with
  | #[op] =>
    match op.name with
    | {dialect := "Python", name:= "Module"} => op.args
    | _ => panic! "Expected top-level module"
  | _ => panic! "Expected unique top-level module"

def pythonToBoogie (pgm: Strata.Program): Boogie.Program :=
  -- pgm
  let insideMod := (unwrapModule pgm.commands)
  let funcs := (getFuncs insideMod.toList).map pyFuncDefToBoogie
  {decls := funcs.map (λ p => .proc p)}
  -- {pgm with dialect := "Boogie", dialects:= defaultDialects.dialects, commands := pgm.commands.map pyCmdToBoogieCmd}


end Strata
