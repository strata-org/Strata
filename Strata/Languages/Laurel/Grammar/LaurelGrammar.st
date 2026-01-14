dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";

category StmtExpr;
op literalBool (b: Bool): StmtExpr => b;
op int(n : Num) : StmtExpr => n;

// Variable declarations
category OptionalType;
op optionalType(varType: LaurelType): OptionalType => ":" varType;

category OptionalAssignment;
op optionalAssignment(value: StmtExpr): OptionalAssignment => ":=" value:0;

op varDecl (name: Ident, varType: Option OptionalType, assignment: Option OptionalAssignment): StmtExpr
  => @[prec(0)] "var " name varType assignment ";";

// Identifiers/Variables
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => target ":=" value ";";

// Binary operators
op add (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60)] lhs "+" rhs;
op eq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "==" rhs;
op neq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "!=" rhs;
op gt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs ">" rhs;
op lt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "<" rhs;
op le (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "<=" rhs;
op ge (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs ">=" rhs;

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr => callee "(" args ")";

// If-else
category OptionalElse;
op optionalElse(stmts : StmtExpr) : OptionalElse => "else" stmts;

op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: Option OptionalElse): StmtExpr =>
  @[prec(20)] "if (" cond ") " thenBranch:0 elseBranch:0;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";";
op return (value : StmtExpr) : StmtExpr => "return " value ";";
op block (stmts : Seq StmtExpr) : StmtExpr => @[prec(1000)] "{" stmts "}";

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ":" paramType;

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "returns" "(" parameters ")";

category Procedure;
op procedure (name : Ident, parameters: CommaSepBy Parameter,
  returnParameters: Option ReturnParameters,
  body : StmtExpr) : Procedure =>
  "procedure " name "(" parameters ")" returnParameters body:0;

op program (staticProcedures: Seq Procedure): Command => staticProcedures;