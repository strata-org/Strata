// Changes in this file are not automatically tracked by the build system.
// Modify LaurelGrammar.lean (e.g. update its comment) to trigger a rebuild after changing this file.
dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";
op realType : LaurelType => "real";
op float64Type : LaurelType => "float64";
op stringType : LaurelType => "string";
op bvType (width: Num): LaurelType => "bv" width;
// Core type passthrough: parsed as Ident, translated to HighType.TCore
op coreType (name: Ident): LaurelType => "Core " name;
op mapType (keyType: LaurelType, valueType: LaurelType): LaurelType => "Map " keyType " " valueType;
op compositeType (name: Ident): LaurelType => name;

category StmtExpr;
op literalBool (b: Bool): StmtExpr => b;
op int(n : Num) : StmtExpr => n;
op real(d : Decimal) : StmtExpr => d;
op string (s: Str): StmtExpr => s;
op bvLiteral(value: Num, width: Num): StmtExpr => value "bv" width;
op hole: StmtExpr => "<?>";
op nondetHole: StmtExpr => "<??>";

// Variable declarations
category TypeAnnotation;
op typeAnnotation(varType: LaurelType): TypeAnnotation => ": " varType;

category Initializer;
op initializer(value: StmtExpr): Initializer => " := " value:0;

op varDecl (name: Ident, varType: Option TypeAnnotation, assignment: Option Initializer): StmtExpr
  => @[prec(0)] "var " name varType assignment;

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr =>
  @[prec(95)] callee:89 "(" args ")";

// Instantiation
op new(name: Ident): StmtExpr => "new " name;

// Field access. prec coupled to `call` (also 95, via its `callee:89`): keep them
// equal or `a#b(x)` parsing shifts. prec 95 > postfix `++`/`--` (90) is what lets
// `c#n++` parse paren-free as `(c#n)++`.
op fieldAccess (obj: StmtExpr, field: Ident): StmtExpr => @[prec(95), leftassoc] obj "#" field;

// Identifiers/Variables - must come after fieldAccess so c.value parses as fieldAccess not identifier
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10)] target " := " value;

// Multi-target assignment: assign var x: int, y, var z: int := call()
// Uses the 'assign' keyword to avoid ambiguity with other comma-separated constructs.
category AssignTarget;
op assignTargetDecl (name: Ident, targetType: LaurelType): AssignTarget => "var " name ": " targetType;
op assignTargetVar (name: Ident): AssignTarget => name;
op assignTargetField (obj: Ident, field: Ident): AssignTarget => obj "#" field;

op multiAssign (targets: CommaSepBy AssignTarget, value: StmtExpr): StmtExpr
  => @[prec(0)] "assign " targets " := " value:0;

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
op and (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(30), leftassoc] lhs " & " rhs;
op or (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(20), leftassoc] lhs " | " rhs;
op andThen (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(30), leftassoc] lhs " && " rhs;
op orElse (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(20), leftassoc] lhs " || " rhs;
op implies (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(15), rightassoc] lhs " ==> " rhs;
// String concatenation. Uses `^` (OCaml-style) so that `++` is reserved for the
// Java-style increment operator below.
op strConcat (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60), leftassoc] lhs " ^ " rhs;

// Unary operators
op not (inner: StmtExpr): StmtExpr => @[prec(80)] "!" inner;
op neg (inner: StmtExpr): StmtExpr => @[prec(80)] "-" inner;

// Refer to the pre-state value of an expression (for use in postconditions, modifies clauses).
op old (inner: StmtExpr): StmtExpr => "old(" inner ")";

// Java-style increment / decrement.
// Prefix forms (leading parsers): yield the new value.
op preIncr (target: StmtExpr): StmtExpr => @[prec(80)] "++" target;
op preDecr (target: StmtExpr): StmtExpr => @[prec(80)] "--" target;
// Postfix forms (trailing parsers): yield the old value.
op postIncr (target: StmtExpr): StmtExpr => @[prec(90)] target "++";
op postDecr (target: StmtExpr): StmtExpr => @[prec(90)] target "--";

// Quantifiers
category Trigger;
op trigger(trigger: StmtExpr): Trigger => "{" trigger "}";

op forallExpr (name: Ident, ty: LaurelType, trigger: Option Trigger, body: StmtExpr): StmtExpr
  => "forall(" name ": " ty ")" trigger " => " body:0;
op existsExpr (name: Ident, ty: LaurelType, trigger: Option Trigger, body: StmtExpr): StmtExpr
  => "exists(" name ": " ty ")" trigger " => " body:0;

// Error messages (used in assert, requires, ensures)
category ErrorSummary;
op errorSummary(msg: Str): ErrorSummary => " summary " msg;

// If-else
category ElseBranch;
op elseBranch(stmts : StmtExpr) : ElseBranch => @[prec(0)] " else " stmts;

op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: Option ElseBranch): StmtExpr =>
  @[prec(20)] "if " cond " then " thenBranch:0 elseBranch:0;

op assert (cond : StmtExpr, errorMessage: Option ErrorSummary) : StmtExpr => @[prec(0)] "assert " cond:0 errorMessage:0;
op assume (cond : StmtExpr) : StmtExpr => @[prec(0)] "assume " cond:0;
op return (value : Option StmtExpr) : StmtExpr => @[prec(0)] "return " value:0;
op block (stmts : SemicolonSepBy StmtExpr) : StmtExpr => @[prec(1000)] "{\n  " indent(2, stmts) "\n}";
op labelledBlock (stmts : SemicolonSepBy StmtExpr, label : Ident) : StmtExpr => @[prec(1000)] "{\n  " indent(2, stmts) "\n}" label;
op exit (label : Ident) : StmtExpr => @[prec(0)] "exit " label;

// While loops
category InvariantClause;
op invariantClause (cond: StmtExpr): InvariantClause => "\n  invariant " cond:0;

op while (cond: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "while" "(" cond ")" invariants " " body:0;

op forLoop (init: StmtExpr, cond: StmtExpr, step: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "for" "(" init ";" cond ";" step ")" invariants " " body:0;

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ": " paramType;

// Composite types
category Field;
op mutableField (name: Ident, fieldType: LaurelType): Field => " var " name ": " fieldType;
op immutableField (name: Ident, fieldType: LaurelType): Field => " " name ": " fieldType;

// Type checking and casting
op isType (target: StmtExpr, typeName: Ident): StmtExpr => @[prec(40)] target " is " typeName;
op asType (target: StmtExpr, typeName: Ident): StmtExpr => @[prec(40)] target " as " typeName;

// Composite types with optional extends
category Extends;
op extends(parents: CommaSepBy Ident): Extends => " extends " parents;

category Composite;

// Datatype definitions
category DatatypeConstructorArg;
op datatypeConstructorArg (name: Ident, argType: LaurelType): DatatypeConstructorArg => name ": " argType;

category DatatypeConstructor;
op datatypeConstructor (name: Ident, args: CommaSepBy DatatypeConstructorArg): DatatypeConstructor => name "(" args ")";
op datatypeConstructorNoArgs (name: Ident): DatatypeConstructor => name;

category DatatypeConstructorList;
op datatypeConstructorList (constructors: CommaSepBy DatatypeConstructor): DatatypeConstructorList => constructors;

category Datatype;
op datatype (name: Ident, constructors: DatatypeConstructorList): Datatype => "datatype " name " { " constructors " }";

// Procedures
category ReturnType;
op returnType(returnType: LaurelType): ReturnType => ": " returnType;

category InvokeOnClause;
op invokeOnClause(trigger: StmtExpr): InvokeOnClause => "\n  invokeOn " trigger:0;

category RequiresClause;
op requiresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): RequiresClause => "\n  requires " cond:0 errorMessage;

category EnsuresClause;
op ensuresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): EnsuresClause => "\n  ensures " cond:0 errorMessage;

category ModifiesClause;
op modifiesClause(refs: CommaSepBy StmtExpr): ModifiesClause => "\n  modifies " refs;
op modifiesWildcard: ModifiesClause => "\n  modifies *";

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "\n  returns " "(" parameters ")";

category OpaqueSpec;
op opaqueSpec(ensures: Seq EnsuresClause, modifies: Seq ModifiesClause): OpaqueSpec =>
  "\n  opaque" ensures modifies;

category Body;
op body(body: StmtExpr): Body => "\n" body:0;
op externalBody: Body => "external";

category Procedure;
op procedure (name : Ident, parameters: CommaSepBy Parameter,
  returnType: Option ReturnType,
  returnParameters: Option ReturnParameters,
  requires: Seq RequiresClause,
  invokeOn: Option InvokeOnClause,
  opaqueSpec: Option OpaqueSpec,
  body : Option Body) : Procedure =>
  "procedure " name "(" parameters ")" returnType returnParameters requires invokeOn opaqueSpec body ";";

op function (name : Ident, parameters: CommaSepBy Parameter,
  returnType: Option ReturnType,
  returnParameters: Option ReturnParameters,
  requires: Seq RequiresClause,
  invokeOn: Option InvokeOnClause,
  opaqueSpec: Option OpaqueSpec,
  body : Option Body) : Procedure =>
  "function " name "(" parameters ")" returnType returnParameters requires invokeOn opaqueSpec body ";";

op composite (name: Ident, extending: Option Extends, fields: Seq Field, procedures: Seq Procedure): Composite => "composite " name extending " {" fields procedures " }";

category ConstrainedType;
op constrainedType (name: Ident, valueName: Ident, base: LaurelType,
                    constraint: StmtExpr, witness: StmtExpr): ConstrainedType
  => "constrained " name " = " valueName ": " base " where " constraint:0 " witness " witness:0;

op compositeCommand(composite: Composite): Command => composite;
op procedureCommand(procedure: Procedure): Command => procedure;
op datatypeCommand(datatype: Datatype): Command => datatype;
op constrainedTypeCommand(ct: ConstrainedType): Command => ct;

