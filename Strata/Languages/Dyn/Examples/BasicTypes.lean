/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def BasicTypesPgm :=
#strata
program Dyn;

def test_basic_types (dummy : Any) -> Any
{
  var y : Any;
  y = int_to_Any(42);
  return y;
}

#end

/--
info: #[{ name := { dialect := "Dyn", name := "function_def" },
    args :=
      ((((Array.mkEmpty 4).push (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                (Arg.ident "test_basic_types")).push
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
                                  ((Array.mkEmpty 2).push (Arg.ident "y")).push
                                    (Arg.type
                                      (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0))) })).push
                        (Arg.op
                          { name := { dialect := "Dyn", name := "assign" },
                            args :=
                              (((Array.mkEmpty 3).push
                                        (Arg.type
                                          (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                                    (Arg.ident "y")).push
                                (Arg.expr
                                  ((Expr.fn { dialect := "Dyn", name := "int_to_Any" }).app
                                    (Arg.expr
                                      ((Expr.fn { dialect := "Dyn", name := "to_int" }).app (Arg.num 42))))) })).push
                    (Arg.op
                      { name := { dialect := "Dyn", name := "return_stmt" },
                        args :=
                          ((Array.mkEmpty 2).push
                                (Arg.type (TypeExpr.ident { dialect := "Dyn", name := "Any" } (Array.mkEmpty 0)))).push
                            (Arg.expr (Expr.bvar 0)) }))) }) }]
-/
#guard_msgs in
#eval BasicTypesPgm.commands

end Dyn
end Strata
