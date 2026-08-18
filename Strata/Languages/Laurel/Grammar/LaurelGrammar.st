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
// Core type passthrough: parsed as Ident, translated to HighType.UserDefined
op coreType (name: Ident): LaurelType => "Core " name;
op mapType (keyType: LaurelType, valueType: LaurelType): LaurelType => "Map " keyType " " valueType;
// Generic type application, e.g. `Option<int>` or `Result<int, E>`.
op appliedType (base: Ident, args: CommaSepBy LaurelType): LaurelType => base "<" args ">";
op compositeType (name: Ident): LaurelType => name;
// Parenthesized type. LaurelType has no precedence tuning, so the pretty-printer
// wraps a non-atomic type (notably `appliedType`) in parens in type-argument
// slots (`var o: (Option<int>)`); without this production that output would not
// re-parse and applied types would never round-trip. Mirrors `StmtExpr`'s
// `parenthesis`; the concrete-to-abstract translator unwraps it to the inner type.
op parenType (inner: LaurelType): LaurelType => "(" inner ")";

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
op typeAnnotation(varType: LaurelType): TypeAnnotation => ": " varType:0;

category Initializer;
op initializer(value: StmtExpr): Initializer => " := " value:0;

op varDecl (name: Ident, varType: Option TypeAnnotation, assignment: Option Initializer): StmtExpr
  => @[prec(0)] "var " name varType assignment;

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr =>
  @[prec(95)] callee:89 "(" args ")";

// Instantiation. Optional `<...>` carries explicit type arguments for a generic
// composite, e.g. `new Box<int>`. Mirrors `appliedType` (the `<args>` clause in
// type position); `prec(80)` + the immediate `<` (no surrounding spaces, unlike
// the `lt` operator `" < "`) disambiguates from a less-than comparison.
category NewTypeArgs;
op newTypeArgs (args: CommaSepBy LaurelType): NewTypeArgs => @[prec(80)] "<" args ">";
op new(name: Ident, typeArgs: Option NewTypeArgs): StmtExpr => "new " name typeArgs:0;

// Field access. prec coupled to `call` (also 95, via its `callee:89`): keep them
// equal or `a#b(x)` parsing shifts. prec 95 > postfix `++`/`--` (90) is what lets
// `c#n++` parse paren-free as `(c#n)++`.
op fieldAccess (obj: StmtExpr, field: Ident): StmtExpr => @[prec(95), leftassoc] obj "#" field;

// Identifiers/Variables - must come after fieldAccess so c.value parses as fieldAccess not identifier
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10)] target " := " value;

// Compound assignment (`x op= e`). Same precedence as `assign`; rightassoc so
// `a += b += c` groups as `a += (b += c)`. Lvalue-ness of `target` is enforced in
// the concrete-to-abstract translator, not the grammar.
op addAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " += " value;
op subAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " -= " value;
op mulAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " *= " value;
op divAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " /= " value;
op modAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " %= " value;
op strConcatAssign (target: StmtExpr, value: StmtExpr): StmtExpr => @[prec(10), rightassoc] target " ^= " value;

// Multi-target assignment: assign var x: int, y, var z := call()
// Uses the 'assign' keyword to avoid ambiguity with other comma-separated constructs.
// The declared target's annotation is optional, like varDecl's.
category AssignTarget;
op assignTargetDecl (name: Ident, targetType: Option TypeAnnotation): AssignTarget => @[prec(0)] "var " name targetType;
op assignTargetVar (name: Ident): AssignTarget => name;
// A chained field-write target `w#b#val`. `obj` is a dedicated `FieldPath`
// category — a left-recursive identifier/field chain — NOT the full `StmtExpr`
// category. Using `StmtExpr` for `obj` made it compete with `multiAssign`'s VALUE
// (also a StmtExpr), so `assign t := f()` mis-parsed (`f()` was tried as a field
// object → "expected '#'"). A separate category cannot collide with the value.
category FieldPath;
op fieldPathRoot (name: Ident): FieldPath => name;
op fieldPathStep (obj: FieldPath, field: Ident): FieldPath => @[leftassoc] obj "#" field;
op assignTargetField (obj: FieldPath, field: Ident): AssignTarget => obj "#" field;

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
op elseBranch(stmts : StmtExpr) : ElseBranch => @[prec(0)] "\nelse " stmts;

op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: Option ElseBranch): StmtExpr =>
  @[prec(20)] "if " cond indent(2, "\nthen " thenBranch:0 elseBranch:0);

op assert (cond : StmtExpr, errorMessage: Option ErrorSummary) : StmtExpr => @[prec(0)] "assert " cond:0 errorMessage:0;
op assume (cond : StmtExpr) : StmtExpr => @[prec(0)] "assume " cond:0;
op throw (value : StmtExpr) : StmtExpr => @[prec(0)] "throw " value:0;
op return (value : Option StmtExpr) : StmtExpr => @[prec(0)] "return " value:0;
op block (stmts : SemicolonSepBy StmtExpr) : StmtExpr => @[prec(1000)] "{\n  " indent(2, stmts) "\n}";
op labelledBlock (stmts : SemicolonSepBy StmtExpr, label : Ident) : StmtExpr => @[prec(1000)] "{\n  " indent(2, stmts) "\n}" label;
op exit (label : Ident) : StmtExpr => @[prec(0)] "exit " label;

// Exception handling: try / catch (with optional `when` guard) / finally.
category CatchGuard;
op catchGuard (predicate: StmtExpr): CatchGuard => " when " predicate:0;

category CatchClause;
op catchClause (binding: Ident, guard: Option CatchGuard, body: StmtExpr): CatchClause
  => "\n  catch " binding guard " " body:0;

category FinallyClause;
op finallyClause (body: StmtExpr): FinallyClause => "\n  finally " body:0;

op tryCatch (body: StmtExpr, catches: Seq CatchClause, finallyClause: Option FinallyClause): StmtExpr
  => @[prec(0)] "try " body:0 catches finallyClause;

// While loops
category InvariantClause;
op invariantClause (cond: StmtExpr): InvariantClause => "\n  invariant " cond:0;

op while (cond: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "while" "(" cond ")" invariants " " body:0;

op forLoop (init: StmtExpr, cond: StmtExpr, step: StmtExpr, invariants: Seq InvariantClause, body: StmtExpr): StmtExpr
  => "for" "(" init ";" cond ";" step ")" invariants " " body:0;

op doWhile (body: StmtExpr, cond: StmtExpr, invariants: Seq InvariantClause): StmtExpr
  => "do " body:0 " while" "(" cond ")" invariants;

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ": " paramType;

// Composite types
category Field;
op mutableField (name: Ident, fieldType: LaurelType): Field => " var " name ": " fieldType;
op immutableField (name: Ident, fieldType: LaurelType): Field => " " name ": " fieldType;

// Type checking and casting
op isType (target: StmtExpr, targetType: LaurelType): StmtExpr => @[prec(40)] target " is " targetType;
op asType (target: StmtExpr, targetType: LaurelType): StmtExpr => @[prec(40)] target " as " targetType;

// Composite types with optional extends. Parents are LaurelTypes (not bare Idents) so a
// generic composite can extend a generic parent instantiation (`extends Base<T>`). The
// parent list terminates cleanly at the following `{` (no trailing LaurelType operator),
// so there is no parse ambiguity with the fields block.
category Extends;
op extends(parents: CommaSepBy LaurelType): Extends => " extends " parents;

category Composite;

// Type parameters (`<T, U>`) — declared here so both datatype (below) and
// procedure/function/composite (further below) can reference it.
category TypeParams;
op typeParams (params: CommaSepBy Ident): TypeParams => "<" params ">";

// Datatype definitions
category DatatypeConstructorArg;
op datatypeConstructorArg (name: Ident, argType: LaurelType): DatatypeConstructorArg => name ": " argType;

category DatatypeConstructor;
op datatypeConstructor (name: Ident, args: CommaSepBy DatatypeConstructorArg): DatatypeConstructor => name "(" args ")";
op datatypeConstructorNoArgs (name: Ident): DatatypeConstructor => name;

category DatatypeConstructorList;
op datatypeConstructorList (constructors: CommaSepBy DatatypeConstructor): DatatypeConstructorList => constructors;

category Datatype;
op datatype (name: Ident, typeParams: Option TypeParams, constructors: DatatypeConstructorList): Datatype => "datatype " name typeParams " { " constructors " }";

// Procedures
category ReturnType;
op returnType(returnType: LaurelType): ReturnType => ": " returnType;

category InvokeOnClause;
op invokeOnClause(trigger: StmtExpr): InvokeOnClause => "\n  invokeOn " trigger:0;

category EntryClause;
op entryClause: EntryClause => "\n  entry";

// `requires`/`ensures` lower to both an assertion and an assumption by default.
// `free` keeps only the assumption (assumed but never checked); `checked` keeps
// only the assertion (checked but never exposed as an assumption).
category RequiresClause;
op requiresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): RequiresClause => "\n  requires " cond:0 errorMessage;
op freeRequiresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): RequiresClause => "\n  free requires " cond:0 errorMessage;
op checkedRequiresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): RequiresClause => "\n  checked requires " cond:0 errorMessage;

category EnsuresClause;
op ensuresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): EnsuresClause => "\n  ensures " cond:0 errorMessage;
op freeEnsuresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): EnsuresClause => "\n  free ensures " cond:0 errorMessage;
op checkedEnsuresClause(cond: StmtExpr, errorMessage: Option ErrorSummary): EnsuresClause => "\n  checked ensures " cond:0 errorMessage;

category ModifiesClause;
op modifiesClause(refs: CommaSepBy StmtExpr): ModifiesClause => "\n  modifies " refs:0;
op modifiesWildcard: ModifiesClause => "\n  modifies *";
// Internal (pass-generated) form: a frame that applies only when its guard holds.
// `EliminateExceptions` emits these when consuming `throwsOn` blocks; users write
// plain `modifies`, which is a single unguarded frame.
op modifiesWhenClause(refs: CommaSepBy StmtExpr, guard: StmtExpr): ModifiesClause => "\n  modifies " refs:0 " when " guard:0;

category ReturnParameters;
op returnParameters(parameters: CommaSepBy Parameter): ReturnParameters => "\n  returns " "(" parameters ")";

// Exceptional contract. The `throws` type is part of the signature (see the
// `procedure` op); the `throwsOn` behavior cases below are part of the
// `opaqueSpec`, alongside the normal-path `ensures`/`modifies`.
// The clause always names the thrown value, scoping that name over every
// `throwsOn` block's `ensures` (but not over their guards, which are evaluated on
// entry). There is deliberately no unbound form: a procedure that says nothing
// about its exception today would otherwise have to change its signature the
// moment it wants to, and one spelling means one thing to learn.
category ThrowsClause;
op throwsClause(binding: Ident, throwsType: LaurelType): ThrowsClause =>
  " throws (" binding ": " throwsType ")";

// The clauses inside a `throwsOn` block: the throwing-path counterparts of
// `ensures` and `modifies`, scoped to that block's guard.
category ThrowsOnSpecClause;
op throwsOnEnsures(cond: StmtExpr, errorMessage: Option ErrorSummary): ThrowsOnSpecClause =>
  "\n    ensures " cond:0 errorMessage;
op throwsOnModifies(refs: CommaSepBy StmtExpr): ThrowsOnSpecClause =>
  "\n    modifies " refs:0;

// An exceptional behavior case: `guard` is a pre-state condition that *forces*
// this throw (`guard ==> throws`), and the clauses inside describe that
// throwing path. Repeatable, one block per case. A throwing path matching no
// guard may modify nothing; see the exhaustiveness check in `ModifiesClauses`.
category ThrowsOnClause;
op throwsOnClause(guard: StmtExpr, clauses: Seq ThrowsOnSpecClause): ThrowsOnClause =>
  "\n  throwsOn " guard:0 " {" clauses "\n  }";

// The opaque specification: the caller-visible contract, holding the
// normal-path clauses and the exceptional behavior cases.
category OpaqueSpec;
op opaqueSpec(ensures: Seq EnsuresClause,
  modifies: Seq ModifiesClause,
  throwsOn: Seq ThrowsOnClause): OpaqueSpec =>
  "\n  opaque" ensures modifies throwsOn;

category Body;
op body(body: StmtExpr): Body => "\n" body:0;
op externalBody: Body => "external";

category Procedure;
op procedure (name : Ident, typeParams: Option TypeParams, parameters: CommaSepBy Parameter,
  returnType: Option ReturnType,
  returnParameters: Option ReturnParameters,
  throws: Option ThrowsClause,
  requires: Seq RequiresClause,
  invokeOn: Option InvokeOnClause,
  entry: Option EntryClause,
  opaqueSpec: Option OpaqueSpec,
  body : Option Body) : Procedure =>
  "procedure " name typeParams "(" parameters ")" returnType returnParameters throws requires invokeOn entry opaqueSpec body ";";

op composite (name: Ident, typeParams: Option TypeParams, extending: Option Extends, fields: Seq Field, procedures: Seq Procedure): Composite => "composite " name typeParams extending " {" fields procedures " }";

category ConstrainedType;
op constrainedType (name: Ident, valueName: Ident, base: LaurelType,
                    constraint: StmtExpr, witness: StmtExpr): ConstrainedType
  => "constrained " name " = " valueName ": " base " where " constraint:0 " witness " witness:0;

op globalVarCommand (name: Ident, varType: LaurelType, init: Option Initializer): Command => @[prec(0)] "var " name ": " varType init;
// Type alias `type Name = Target`. No trailing `;` — top-level decls don't share a
// separator (each renders its own terminator; the next leading keyword delimits, like
// composite/datatype/constrained).
category TypeAliasDecl;
op typeAlias (name: Ident, typeParams: Option TypeParams, target: LaurelType): TypeAliasDecl => "type " name typeParams " = " target:0;

op compositeCommand(composite: Composite): Command => composite;
op procedureCommand(procedure: Procedure): Command => procedure;
op datatypeCommand(datatype: Datatype): Command => datatype;
op constrainedTypeCommand(ct: ConstrainedType): Command => ct;
op typeAliasCommand(alias: TypeAliasDecl): Command => alias;

