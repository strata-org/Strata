/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def TypeIntrospectionPgm :=
#strata
program Dyn;

def test_type_ops (dummy : Any) -> Any
{
  var result : int;
  result = 0;
  return bool_to_Any((str_to_Any(typeof(result)) == str_to_Any("string")));
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_type_ops")).push
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
                                  ((Array.mkEmpty 2).push (Arg.ident "result")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "int" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "int" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "result")).push
                                (Arg.expr ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 0))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr
                              ((Expr.fn { dialect := "Dyn", name := "bool_to_Any" }).app
                                (Arg.expr
                                  (((Expr.fn { dialect := "Dyn", name := "eq" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "str_to_Any" }).app
                                            (Arg.expr
                                              (((Expr.fn { dialect := "Dyn", name := "typeof" }).app
                                                    (Arg.type
                                                      (TypeExpr.ident { dialect := "Dyn", name := "int" }
                                                        (Array.mkEmpty 0)))).app
                                                (Arg.expr (Expr.bvar 0))))))).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "str_to_Any" }).app
                                        (Arg.expr
                                          ((Expr.fn { dialect := "Dyn", name := "strLit" }).app
                                            (Arg.strlit "string"))))))))) }))) }) }]
-/
#guard_msgs in
#eval TypeIntrospectionPgm.commands

end Dyn
end Strata
