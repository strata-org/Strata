dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";
op stringType : LaurelType => "string";
op compositeType (name: Ident): LaurelType => name;

category StmtExpr;
op literalBool (b: Bool): StmtExpr => b;
op int(n : Num) : StmtExpr => n;
op string (s: Str): StmtExpr => s;

// Variable declarations
category OptionalType;
op optionalType(varType: LaurelType): OptionalType => ":" varType;

category OptionalAssignment;
op optionalAssignment(value: StmtExpr): OptionalAssignment => ":=" value:0;

op varDecl (name: Ident, varType: Option OptionalType, assignment: Option OptionalAssignment): StmtExpr
  => @[prec(0)] "var " name varType assignment ";";

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr => callee "(" args ")";

// Field access
op fieldAccess (obj: StmtExpr, field: Ident): StmtExpr => @[prec(90)] obj "#" field;

// Identifiers/Variables - must come after fieldAccess so c.value parses as fieldAccess not identifier
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10)] target ":=" value ";";

// Binary operators
op add (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs " + " rhs;
op eq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " == " rhs;
op neq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " != " rhs;
op gt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " > " rhs;
op lt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " < " rhs;
op le (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " <= " rhs;
op ge (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40), leftassoc] lhs " >= " rhs;

// Logical operators
op and (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(30), leftassoc] lhs " && " rhs;
op or (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(25), leftassoc] lhs " || " rhs;

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

// Composite types
category Field;
op mutableField (name: Ident, fieldType: LaurelType): Field => "var " name ":" fieldType;
op immutableField (name: Ident, fieldType: LaurelType): Field => name ":" fieldType;

category Composite;
op composite (name: Ident, fields: Seq Field): Composite => "composite " name "{" fields "}";

// Procedures
category OptionalReturnType;
op optionalReturnType(returnType: LaurelType): OptionalReturnType => ":" returnType;

category OptionalRequires;
op optionalRequires(cond: StmtExpr): OptionalRequires => "requires" cond:0;

category OptionalEnsures;
op optionalEnsures(cond: StmtExpr): OptionalEnsures => "ensures" cond:0;

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "returns" "(" parameters ")";

category Procedure;
op procedure (name : Ident, parameters: CommaSepBy Parameter,
  returnType: Option OptionalReturnType,
  returnParameters: Option ReturnParameters,
  requires: Option OptionalRequires,
  ensures: Option OptionalEnsures,
  body : StmtExpr) : Procedure =>
  "procedure " name "(" parameters ")" returnType returnParameters requires ensures body:0;

category TopLevel;
op topLevelComposite(composite: Composite): TopLevel => composite;
op topLevelProcedure(procedure: Procedure): TopLevel => procedure;

op program (items: Seq TopLevel): Command => items;