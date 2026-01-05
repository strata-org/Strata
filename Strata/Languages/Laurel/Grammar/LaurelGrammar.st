dialect Laurel;

category StmtExpr;
op literalBool (b: Bool): StmtExpr => b;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";\n";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";\n";
op block (stmts : Seq StmtExpr) : StmtExpr => @[prec(1000)] "{\n" stmts "}\n";

category Procedure;
op procedure (name : Ident, body : StmtExpr) : Procedure => "procedure " name "() " body:0;

op program (staticProcedures: Seq Procedure): Command => staticProcedures;
