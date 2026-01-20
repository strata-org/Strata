dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";
op compositeType (name: Ident): LaurelType => name;

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

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr => callee "(" args ")";

// Field access
op fieldAccess (obj: StmtExpr, field: Ident): StmtExpr => @[prec(90)] obj "#" field;

// Identifiers/Variables - must come after fieldAccess so c.value parses as fieldAccess not identifier
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10)] target ":=" value ";";

// Binary operators
op add (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs "+" rhs;
op sub (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs "-" rhs;
op mul (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs "*" rhs;
op div (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs "/" rhs;
op mod (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs "%" rhs;
op eq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "==" rhs;
op neq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "!=" rhs;
op gt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs ">" rhs;
op lt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "<" rhs;
op le (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs "<=" rhs;
op ge (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs ">=" rhs;
op and (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(30), leftassoc] lhs " && " rhs;
op or (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(20), leftassoc] lhs " || " rhs;

// Unary operators
op not (inner: StmtExpr): StmtExpr => @[prec(80)] "!" inner;
op neg (inner: StmtExpr): StmtExpr => @[prec(80)] "-" inner;

// If-else
category OptionalElse;
op optionalElse(stmts : StmtExpr) : OptionalElse => "else" stmts;

op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: Option OptionalElse): StmtExpr =>
  @[prec(20)] "if (" cond ") " thenBranch:0 elseBranch:0;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";";
op return (value : StmtExpr) : StmtExpr => "return " value ";";
op block (stmts : Seq StmtExpr) : StmtExpr => @[prec(1000)] "{" stmts "}";

// While loops
category InvariantClause;
op invariantClause (cond: StmtExpr): InvariantClause => "invariant" cond:0;

op while (cond: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "while" "(" cond ")" invariants body;

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

category RequiresClause;
op requiresClause(cond: StmtExpr): RequiresClause => "requires" cond:0;

category EnsuresClause;
op ensuresClause(cond: StmtExpr): EnsuresClause => "ensures" cond:0;

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "returns" "(" parameters ")";

category Procedure;
op procedure (name : Ident, parameters: CommaSepBy Parameter,
  returnType: Option OptionalReturnType,
  returnParameters: Option ReturnParameters,
  requires: Seq RequiresClause,
  ensures: Seq EnsuresClause,
  body : StmtExpr) : Procedure =>
  "procedure " name "(" parameters ")" returnType returnParameters requires ensures body:0;

// Constrained types
category ConstrainedType;
op constrainedType (name: Ident, valueName: Ident, base: LaurelType,
                    constraint: StmtExpr, witness: StmtExpr): ConstrainedType
  => "constrained" name "=" valueName ":" base "where" constraint:0 "witness" witness:0;

category TopLevel;
op topLevelComposite(composite: Composite): TopLevel => composite;
op topLevelProcedure(procedure: Procedure): TopLevel => procedure;
op topLevelConstrainedType(ct: ConstrainedType): TopLevel => ct;

op program (items: Seq TopLevel): Command => items;