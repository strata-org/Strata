dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";
op stringType : LaurelType => "string";
op arrayType (elemType: LaurelType): LaurelType => "Array" "<" elemType ">";
op compositeType (name: Ident): LaurelType => name;

category StmtExpr;
op literalBool (b: Bool): StmtExpr => b;
op int(n : Num) : StmtExpr => n;
op string (s: Str): StmtExpr => s;

// Variable declarations
category OptionalType;
op optionalType(varType: LaurelType): OptionalType => ": " varType;

category OptionalAssignment;
op optionalAssignment(value: StmtExpr): OptionalAssignment => " := " value:0;

op varDecl (name: Ident, varType: Option OptionalType, assignment: Option OptionalAssignment): StmtExpr
  => @[prec(0)] "var " name varType assignment ";";

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr => @[prec(95)] callee:85 "(" args ")";

// Field access
op fieldAccess (obj: StmtExpr, field: Ident): StmtExpr => @[prec(90)] obj "#" field;

// Array indexing
op arrayIndex (arr: StmtExpr, idx: StmtExpr): StmtExpr => @[prec(90)] arr "[" idx "]";

// Identifiers/Variables - must come after fieldAccess so c.value parses as fieldAccess not identifier
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10)] target " := " value ";";

// Binary operators
op add (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs " + " rhs;
op sub (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs " - " rhs;
op mul (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs " * " rhs;
op div (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs " / " rhs;
op mod (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs " % " rhs;
op divT (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs " /t " rhs;
op modT (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(70), leftassoc] lhs " %t " rhs;
op eq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " == " rhs;
op neq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " != " rhs;
op gt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " > " rhs;
op lt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " < " rhs;
op le (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " <= " rhs;
op ge (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " >= " rhs;
op and (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(30), leftassoc] lhs " && " rhs;
op or (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(20), leftassoc] lhs " || " rhs;
op implies (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(15), rightassoc] lhs " ==> " rhs;

// Unary operators
op not (inner: StmtExpr): StmtExpr => @[prec(80)] "!" inner;
op neg (inner: StmtExpr): StmtExpr => @[prec(80)] "-" inner;

// Quantifiers
op forallExpr (name: Ident, ty: LaurelType, body: StmtExpr): StmtExpr
  => "forall(" name ": " ty ") => " body:0;
op existsExpr (name: Ident, ty: LaurelType, body: StmtExpr): StmtExpr
  => "exists(" name ": " ty ") => " body:0;

// If-else
category OptionalElse;
op optionalElse(stmts : StmtExpr) : OptionalElse => "else " stmts:0;

op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: Option OptionalElse): StmtExpr =>
  @[prec(20)] "if (" cond ") " thenBranch:0 " " elseBranch:0;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";";
op return (value : StmtExpr) : StmtExpr => "return " value ";";
op block (stmts : NewlineSepBy StmtExpr) : StmtExpr => @[prec(1000)] "{" indent(2, "\n" stmts) "\n}";

// While loops
category InvariantClause;
op invariantClause (cond: StmtExpr): InvariantClause => "\n  invariant " cond:0;

op while (cond: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "while" "(" cond ")" invariants body:0;

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ": " paramType;

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
op requiresClause(cond: StmtExpr): RequiresClause => "requires " cond:0;

category EnsuresClause;
op ensuresClause(cond: StmtExpr): EnsuresClause => "ensures " cond:0;

category ModifiesClause;
op modifiesClause(refs: CommaSepBy StmtExpr): ModifiesClause => "modifies" refs;

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "returns" "(" parameters ")";

category OptionalBody;
op optionalBody(body: StmtExpr): OptionalBody => body:0;

category Procedure;
op procedure (name : Ident, parameters: CommaSepBy Parameter,
  returnType: Option OptionalReturnType,
  returnParameters: Option ReturnParameters,
  requires: NewlineSepBy RequiresClause,
  ensures: NewlineSepBy EnsuresClause,
  modifies: Seq ModifiesClause,
  body : Option OptionalBody) : Procedure =>
  "procedure " name "(" parameters ")" returnType returnParameters indent(2, "\n" requires "\n" ensures) modifies "\n" body;

// Constrained types
category ConstrainedType;
op constrainedType (name: Ident, valueName: Ident, base: LaurelType,
                    constraint: StmtExpr, witness: StmtExpr): ConstrainedType
  => "constrained " name " = " valueName ": " base " where " constraint:0 " witness " witness:0;

category TopLevel;
op topLevelComposite(composite: Composite): TopLevel => composite "\n";
op topLevelProcedure(procedure: Procedure): TopLevel => procedure "\n";
op topLevelConstrainedType(ct: ConstrainedType): TopLevel => ct "\n";

op program (items: Seq TopLevel): Command => items;

