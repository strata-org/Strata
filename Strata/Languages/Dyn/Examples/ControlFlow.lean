/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def ControlFlowPgm :=
#strata
program Dyn;

def test_control_flow (dummy : Any) -> Any
{
  var result : Any;
  result = int_to_Any(0);
  if (bool_to_Any(True)) {
    result = int_to_Any(1);
  } else {
    result = int_to_Any(2);
  }
  return result;
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_control_flow")).push
            (Arg.op
              { name := { dialect := "Dyn", name := "mkParams" },
                args :=
                  (Array.mkEmpty 1).push
                    (Arg.commaSepList
                      ((Array.mkEmpty 1).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "mkParam" },
                            args :=
                              ((Array.mkEmpty 2).push (Arg.ident "dummy")).push
                                (Arg.type
                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) }))) })).push
        (Arg.op
          { name := { dialect := "Dyn", name := "block" },
            args :=
              (Array.mkEmpty 1).push
                (Arg.seq
                  (((((Array.mkEmpty 4).push
                                (Arg.op
                                  { name := { dialect := "Dyn", name := "var_decl" },
                                    args :=
                                      ((Array.mkEmpty 2).push (Arg.ident "result")).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                            (Array.mkEmpty 0))) })).push
                            (Arg.op
                              { name := { dialect := "Dyn", name := "assign" },
                                args :=
                                  (((Array.mkEmpty 3).push
                                            (Arg.type
                                              (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                (Array.mkEmpty 0)))).push
                                        (Arg.ident "result")).push
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 0))))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "if_stmt" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "bool_to_Any" }).app
                                            (Arg.expr (Expr.fn { dialect := "Dyn", name := "btrue" }))))).push
                                    (Arg.op
                                      { name := { dialect := "Dyn", name := "block" },
                                        args :=
                                          (Array.mkEmpty 1).push
                                            (Arg.seq
                                              ((Array.mkEmpty 1).push
                                                (Arg.op
                                                  { name := { dialect := "Dyn", name := "assign" },
                                                    args :=
                                                      (((Array.mkEmpty 3).push
                                                                (Arg.type
                                                                  (TypeExpr.ident { dialect := "Dyn", name := "Any" }
                                                                    (Array.mkEmpty 0)))).push
                                                            (Arg.ident "result")).push
                                                        (Arg.expr
                                                          ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                                            (Arg.expr
                                                              ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                                                (Arg.num 1))))) }))) })).push
                                (Arg.op
                                  { name := { dialect := "Dyn", name := "else_block" },
                                    args :=
                                      (Array.mkEmpty 1).push
                                        (Arg.op
                                          { name := { dialect := "Dyn", name := "block" },
                                            args :=
                                              (Array.mkEmpty 1).push
                                                (Arg.seq
                                                  ((Array.mkEmpty 1).push
                                                    (Arg.op
                                                      { name := { dialect := "Dyn", name := "assign" },
                                                        args :=
                                                          (((Array.mkEmpty 3).push
                                                                    (Arg.type
                                                                      (TypeExpr.ident
                                                                        { dialect := "Dyn", name := "Any" }
                                                                        (Array.mkEmpty 0)))).push
                                                                (Arg.ident "result")).push
                                                            (Arg.expr
                                                              ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                                                (Arg.expr
                                                                  ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                                                    (Arg.num 2))))) }))) }) }) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr (Expr.bvar 0)) }))) }) }]
-/
#guard_msgs in
#eval ControlFlowPgm.commands

end Dyn
end Strata
