// FineGrainLaurel Dialect: FGCBV (Fine-Grain Call-By-Value) with explicit polarity
// This dialect extends Laurel with separate Value and Producer categories,
// making polarity a representation-level invariant rather than a runtime predicate.
//
// Changes in this file are not automatically tracked by the build system.
// Modify FineGrainLaurel.lean (e.g. update its comment) to trigger a rebuild after changing this file.

dialect FineGrainLaurel;
// Note: Not importing Laurel for now - FineGrainLaurel is self-contained

// Import Laurel types for reuse
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";
op realType : LaurelType => "real";
op float64Type : LaurelType => "float64";
op stringType : LaurelType => "string";
op coreType (name: Ident): LaurelType => "Core " name;
op mapType (keyType: LaurelType, valueType: LaurelType): LaurelType => "Map " keyType " " valueType;
op compositeType (name: Ident): LaurelType => name;

// ===========================================================================
// FGCBV Core: Separate Value and Producer categories
// ===========================================================================

// Value category: inert terms (no effects, can be duplicated/discarded)
category Value;

// Producer category: effectful terms (must be sequenced, single-use)
category Producer;

// ===========================================================================
// Value Operators (Inert Terms)
// ===========================================================================

// Literals
op valLiteralInt (n: Num): Value => n;
op valLiteralBool (b: Bool): Value => b;
op valLiteralReal (d: Decimal): Value => d;
op valLiteralString (s: Str): Value => s;

// Variables
op valVar (name: Ident): Value => name;

// Pure binary operations (no effects)
op valAdd (lhs: Value, rhs: Value): Value => @[prec(60), leftassoc] lhs " + " rhs;
op valSub (lhs: Value, rhs: Value): Value => @[prec(60), leftassoc] lhs " - " rhs;
op valMul (lhs: Value, rhs: Value): Value => @[prec(70), leftassoc] lhs " * " rhs;
op valDiv (lhs: Value, rhs: Value): Value => @[prec(70), leftassoc] lhs " / " rhs;
op valMod (lhs: Value, rhs: Value): Value => @[prec(70), leftassoc] lhs " % " rhs;

// Pure comparison operations
op valEq (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " == " rhs;
op valNeq (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " != " rhs;
op valLt (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " < " rhs;
op valLe (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " <= " rhs;
op valGt (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " > " rhs;
op valGe (lhs: Value, rhs: Value): Value => @[prec(40)] lhs " >= " rhs;

// Pure logical operations
op valAnd (lhs: Value, rhs: Value): Value => @[prec(30), leftassoc] lhs " & " rhs;
op valOr (lhs: Value, rhs: Value): Value => @[prec(20), leftassoc] lhs " | " rhs;
op valNot (inner: Value): Value => @[prec(80)] "!" inner;

// Pure unary operations
op valNeg (inner: Value): Value => @[prec(80)] "-" inner;

// Field access (pure)
op valFieldAccess (obj: Value, field: Ident): Value => @[prec(90)] obj "#" field;

// Parenthesis (for grouping)
op valParens (inner: Value): Value => "(" inner ")";

// ===========================================================================
// Producer Operators (Effectful Terms)
// ===========================================================================

// Return a value (terminal producer)
op prodReturnValue (value: Value): Producer => @[prec(0)] "return " value:0;

// Call a procedure (effectful)
op prodCall (callee: Ident, args: CommaSepBy Value): Producer => callee "(" args ")";

// Let-binding for producers (sequence effects)
// let x: ty = prod in body
op prodLetProd (var: Ident, ty: LaurelType, prod: Producer, body: Producer): Producer =>
  @[prec(0)] "let " var ": " ty " = " prod:0 " in " body:0;

// Let-binding for values (introduce binding for a value)
// let x: ty = value in body
op prodLetValue (var: Ident, ty: LaurelType, value: Value, body: Producer): Producer =>
  @[prec(0)] "let " var ": " ty " = " value:0 " in " body:0;

// Assignment (mutation)
op prodAssign (target: Value, value: Value, body: Producer): Producer =>
  @[prec(0)] target " := " value:0 ";" body:0;

// Variable declaration with initialization
op prodVarDecl (name: Ident, ty: LaurelType, init: Value, body: Producer): Producer =>
  @[prec(0)] "var " name ": " ty " := " init:0 ";" body:0;

// Conditional (if-then-else)
op prodIfThenElse (cond: Value, thenBranch: Producer, elseBranch: Producer): Producer =>
  @[prec(0)] "if " cond " then " thenBranch:0 " else " elseBranch:0;

// Assert (specification)
op prodAssert (cond: Value, body: Producer): Producer =>
  @[prec(0)] "assert " cond:0 ";" body:0;

// Assume (specification)
op prodAssume (cond: Value, body: Producer): Producer =>
  @[prec(0)] "assume " cond:0 ";" body:0;

// While loop
category Invariant;
op invariant (cond: Value): Invariant => "invariant " cond:0;

op prodWhile (cond: Value, invariants: Seq Invariant, body: Producer, after: Producer): Producer =>
  @[prec(0)] "while (" cond ")" invariants " " body:0 after:0;

// Instantiation (heap allocation)
op prodNew (name: Ident, resultVar: Ident, ty: LaurelType, body: Producer): Producer =>
  @[prec(0)] "let " resultVar ": " ty " = new " name " in " body:0;

// Call with error handling
op prodCallWithError (callee: Ident, args: CommaSepBy Value,
                      resultVar: Ident, errorVar: Ident,
                      resultTy: LaurelType, errorTy: LaurelType,
                      body: Producer): Producer =>
  @[prec(0)] "let [" resultVar ": " resultTy ", " errorVar ": " errorTy "] = " callee "(" args ") in " body:0;

// Sequence (statement sequencing)
op prodSeq (first: Producer, second: Producer): Producer =>
  @[prec(5)] first:5 ";" second:5;

// Block with multiple producers
op prodBlock (stmts: SemicolonSepBy Producer): Producer =>
  @[prec(1000)] "{" stmts "}";

// Exit a labelled block (break/continue control flow)
op prodExit (label: Str): Producer => "exit " label;

// Labeled block (target of prodExit — models break/continue)
op prodLabeledBlock (label: Str, body: Producer): Producer =>
  @[prec(0)] "block " label " {" body:0 "}";

// ===========================================================================
// Top-level Declarations (reuse Laurel structure)
// ===========================================================================

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ":" paramType;

category ReturnParameters;
op returnParameters (parameters: CommaSepBy Parameter): ReturnParameters => "returns" "(" parameters ")";

category ErrorSummary;
op errorSummary (msg: Str): ErrorSummary => "summary" msg;

category RequiresClause;
op requiresClause (cond: Value, errorMessage: Option ErrorSummary): RequiresClause => "requires" cond:0 errorMessage;

category EnsuresClause;
op ensuresClause (cond: Value, errorMessage: Option ErrorSummary): EnsuresClause => "ensures" cond:0 errorMessage;

category ModifiesClause;
op modifiesClause (refs: CommaSepBy Value): ModifiesClause => "modifies" refs;

category ProcedureBody;
op procedureBody (body: Producer): ProcedureBody => body:0;
op externalBody: ProcedureBody => "external";

category Procedure;
op procedure (name: Ident, parameters: CommaSepBy Parameter,
  returnParameters: Option ReturnParameters,
  requires: Seq RequiresClause,
  ensures: Seq EnsuresClause,
  modifies: Seq ModifiesClause,
  body: Option ProcedureBody): Procedure =>
  "procedure " name "(" parameters ")" returnParameters requires ensures modifies body ";";

category Field;
op mutableField (name: Ident, fieldType: LaurelType): Field => "var " name ":" fieldType;
op immutableField (name: Ident, fieldType: LaurelType): Field => name ":" fieldType;

category Extends;
op extends (parents: CommaSepBy Ident): Extends => "extends " parents;

category Composite;
op composite (name: Ident, extending: Option Extends, fields: Seq Field, procedures: Seq Procedure): Composite =>
  "composite " name extending "{" fields procedures "}";

// ===========================================================================
// Value-Level Coercion Operators (Subtyping: infallible, value→value)
// ===========================================================================

// Upcasts: inject concrete types into Any (pure injections into the sum type)
op valFromInt (inner: Value): Value => "from_int(" inner ")";
op valFromStr (inner: Value): Value => "from_str(" inner ")";
op valFromBool (inner: Value): Value => "from_bool(" inner ")";
op valFromFloat (inner: Value): Value => "from_float(" inner ")";
op valFromComposite (inner: Value): Value => "from_Composite(" inner ")";
op valFromListAny (inner: Value): Value => "from_ListAny(" inner ")";
op valFromDictStrAny (inner: Value): Value => "from_DictStrAny(" inner ")";
op valFromNone: Value => "from_None()";

// ===========================================================================
// Top-level Declarations
// ===========================================================================

// Top-level commands
op compositeCommand (composite: Composite): Command => composite;
op procedureCommand (procedure: Procedure): Command => procedure;
