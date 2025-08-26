/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def ArithmeticPgm :=
#strata
program Dyn;

def test_arithmetic (dummy : Any) -> Any
{
  var sum : Any;
  sum = int_to_Any(1) + int_to_Any(2);
  return sum;
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_arithmetic")).push
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
                  ((((Array.mkEmpty 3).push
                            (Arg.op
                              { name := { dialect := "Dyn", name := "var_decl" },
                                args :=
                                  ((Array.mkEmpty 2).push (Arg.ident "sum")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "sum")).push
                                (Arg.expr
                                  (((Expr.fn { dialect := "Dyn", name := "add" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                            (Arg.expr
                                              ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 1)))))).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "to_int" }).app
                                            (Arg.num 2))))))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr (Expr.bvar 0)) }))) }) }]
-/
#guard_msgs in
#eval ArithmeticPgm.commands

end Dyn
end Strata
