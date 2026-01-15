dialect Simple;

category Expr;
op num (value : Num) : Simple.Expr => value;
op add (left : Simple.Expr, right : Simple.Expr) : Simple.Expr => left "+" right;
op neg (inner : Simple.Expr) : Simple.Expr => "-" inner;

category Stmt;
op print (msg : Str) : Simple.Stmt => "print" msg;
op assign (name : Ident, value : Simple.Expr) : Simple.Stmt => name ":=" value;
op block (stmts : Seq Simple.Stmt) : Simple.Stmt => "{" stmts "}";
op ifStmt (cond : Bool, thenBranch : Simple.Stmt, elseBranch : Option Simple.Stmt) : Simple.Stmt => 
  "if" cond "then" thenBranch elseBranch;
op data (bytes : ByteArray) : Simple.Stmt => "data" bytes;
op decimal (value : Decimal) : Simple.Stmt => "decimal" value;
