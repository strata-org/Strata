/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.AST.Lemmas
import all Strata.DDM.Ion
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.Integration.Lean

namespace Strata

open _root_.Ion (SymbolTable Ion SymbolId)

def testRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (toF : α → ByteArray) (init : α) : Bool :=
  let bs := toF init
  match FromIon.deserialize (α := α) bs with
  | .error msg => @panic _ ⟨false⟩ msg
  | .ok res  => res == init

def testDialectRoundTrip (d : Dialect) : Bool :=
  testRoundTrip Dialect.toIon d

/-- Test that a `Program` can round-trip through Ion
serialization without losing data. -/
private def testProgramRoundTrip (p : Program) : Bool :=
  let bs := p.toIon
  match Program.fromIon p.dialects p.dialect bs with
  | .error msg => @panic _ ⟨false⟩ msg
  | .ok res  => res == p

-- Load the actual Bool dialect from Examples
#load_dialect "../../Examples/dialects/Bool.dialect.st"

#guard testDialectRoundTrip Bool

-- Test we can serialize/deserialize dialect
#guard testDialectRoundTrip initDialect
#guard testDialectRoundTrip StrataDDL

-- Ion roundtrip test dialect covering SepFormat variants, expressions, and bindings
#dialect
dialect TestIon;

type mytype;
type Pair(a : Type, b : Type);
fn lit (n : Num) : mytype => n;
// Arrow type in fn parameter (PreType.arrow in dialect)
fn apply (f : mytype -> mytype, x : mytype) : mytype => f "(" x ")";
op eval (tp : Type, e : tp) : Command => "eval " e " : " tp ";\n";
op evalDec (d : Decimal) : Command => "dec " d ";\n";
op evalStr (s : Str) : Command => "str " s ";\n";
op evalBytes (b : ByteArray) : Command => "bytes " b ";\n";
op evalIdent (name : Ident) : Command => "ident " name ";\n";
// Bool metadata (MetadataArg.bool, MetadataArgType.bool)
metadata myFlag (flag : Bool);
@[myFlag(true)]
op flaggedTrue (e : mytype) : Command => "flagT " e ";\n";
// Option metadata (MetadataArg.option some/none)
metadata myOpt (id : Ident, extra : Option Ident);
@[myOpt(name, none)]
op optNone (name : Ident) : Command => "optN " name ";\n";
@[myOpt(name, some name)]
op optSome (name : Ident) : Command => "optS " name ";\n";

// Binding and scope support (for ExprF.bvar coverage)
category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

op evalScoped (b : Bindings, tp : Type, @[scope(b)] e : tp) : Command
  => "evalScoped " b " " e " : " tp ";\n";

// Lambda function (PreType.funMacro in dialect)
fn lambda (tp : Type, b : Bindings, @[scope(b)] res : tp) : fnOf(b, tp)
  => "fun " b " => " res;

// Scoped type reference (TypeExprF.bvar in programs)
op checkBoundType (b : Bindings, @[scope(b)] tp : Type) : Command
  => "checkBound " b " " tp ";\n";

// Top-level variable declaration (ExprF.fvar when referenced)
@[declare(name, tp)]
op declareVar (name : Ident, tp : Type) : Command => "declare " name " : " tp ";\n";

// Type variable support (PreType.tvar, TypeExprF.tvar)
category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope(typeArgs)] r : Type) : Command =>
  "function " name typeArgs b ":" r ";\n";

category Item;
op item (n : Num) : Item => n;
op testSeq (items : Seq Item) : Command => "seq(" items ")";
op testComma (items : CommaSepBy Item) : Command => "comma(" items ")";
op testSemicolon (items : SemicolonSepBy Item) : Command => "semi(" items ")";
op testSpace (items : SpaceSepBy Item) : Command => "space(" items ")";
op testPrefix (items : SpacePrefixSepBy Item) : Command => "prefix(" items ")";
op testOpt (item : Option Item) : Command => "opt(" item ")";
// Indent syntax (SyntaxDefAtom.indent)
op block (body : Seq Item) : Command => "block" indent(2, body) "end";
// TypeP argument (ArgF.cat coverage)
op checkTypeP (tp : TypeP) : Command => "checkTypeP " tp ";\n";
#end

namespace TestIon
#strata_gen TestIon
end TestIon

def testIonPgm := #strata
program TestIon;
eval 1 : mytype;
dec 1e0;
str "hello";
bytes b"abc";
ident foo;
evalScoped (x : mytype) x : mytype;
function f<a>(x: a): a;
eval f(1) : mytype;
opt(1)
opt()
seq(1 2 3)
comma(1, 2, 3)
semi(1; 2; 3)
space(1 2 3)
prefix(1 2 3)
block 1 2 3 end
eval fun (x: mytype) => x : mytype -> mytype;
#end

-- ExprF.fvar: `eval g` references a declared variable
abbrev testIonFvarPgm := #strata
program TestIon;
declare g : mytype;
eval g : mytype;
#end

-- `eval g` (command 1) references a declared variable via ExprF.fvar
#guard
  let cmd := testIonFvarPgm.program.commands[1]
  match cmd.args[1]? with
  | some (ArgF.expr (.fvar _ _)) => true
  | _ => false

#guard testProgramRoundTrip testIonFvarPgm

-- ArgF.cat: `checkTypeP Type` passes a category as an argument
abbrev testIonCatPgm := #strata
program TestIon;
checkTypeP Type;
#end

-- `checkTypeP Type` (command 0) passes a category via ArgF.cat
#guard
  let cmd := testIonCatPgm.program.commands[0]
  match cmd.args[0]? with
  | some (ArgF.cat _) => true
  | _ => false

#guard testProgramRoundTrip testIonCatPgm

-- TypeExprF.bvar: `checkBound` references a scoped type variable
abbrev testIonBvarPgm := #strata
program TestIon;
checkBound (T : Type) T;
#end

-- `checkBound` (command 0) references a scoped type variable via TypeExprF.bvar
#guard
  let cmd := testIonBvarPgm.program.commands[0]
  match cmd.args[1]? with
  | some (ArgF.type (.bvar _ _)) => true
  | _ => false

#guard testProgramRoundTrip testIonBvarPgm

-- Verify the lambda function uses PreType.funMacro in the dialect
#guard
  TestIon.declarations.any fun d =>
    match d with
    | .function f => f.name == "lambda" && match f.result with
      | .funMacro _ _ _ => true
      | _ => false
    | _ => false

#guard testDialectRoundTrip TestIon
#guard testProgramRoundTrip testIonPgm

-- Dialect for testing FunctionTemplate Ion serialization
#dialect
dialect TestIonDatatypes;

type bool;
type mydt;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding))
  : Constructor => name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => c;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor)
  : ConstructorList => cl ", " c;

metadata declareDatatype (name : Ident, typeParams : Ident,
  constructors : Ident, testerTemplate : FunctionTemplate,
  accessorTemplate : FunctionTemplate);

category DatatypeDecl;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.datatype, .literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.field], [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                     typeParams : Option Bindings,
                     @[scopeTVar(typeParams)] constructors : ConstructorList)
  : DatatypeDecl =>
  "datatype " name typeParams " { " constructors " }";

@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command =>
  datatypes ";\n";
#end

namespace TestIonDatatypes
#strata_gen TestIonDatatypes
end TestIonDatatypes

-- Program with self-referencing datatype (TypeExprF.fvar)
-- and parameterized datatype (TypeExprF.bvar via type parameter reference)
def testIonDatatypesPgm := #strata
program TestIonDatatypes;
datatype MyList { MyNil(), MyCons(head: mydt, tail: MyList) };
datatype Box(a: Type) { MkBox(val: a) };
#end

#guard testDialectRoundTrip TestIonDatatypes
#guard testProgramRoundTrip testIonDatatypesPgm

-- Verify that a malformed `decimal` sexp reports "decimal" in the error message.
#guard
  let tbl := SymbolTable.ofLocals #["decimal"]
  let decimalSym : Ion SymbolId := .symbol (tbl.symbolId "decimal")
  -- 4-element sexp: one too many arguments for `decimal`
  let badSexp : Ion SymbolId := .sexp #[decimalSym, .null, .null, .null]
  let ctx : FromIonContext := ⟨tbl⟩
  match ArgF.fromIon (α := TypeRef) badSexp ctx with
  | .error msg => msg.startsWith "decimal"
  | .ok _ => false

-- Issue #1238: SyntaxDefAtom.fromIon coverage for the indent branch.

-- Helper: wraps a single atom sexp into a minimal dialect Ion value.
private def indentTestDialect (atom : Ion String) : Ion String :=
  .list #[
    .sexp #[.symbol "dialect", .string "TestIndentBounds"],
    .struct #[
      ("type",   .symbol "op"),
      ("name",   .string "testOp"),
      ("result", .symbol "TestIndentBounds.Command"),
      ("syntax", .struct #[
        ("atoms", .list #[atom]),
        ("prec", .int 0)
      ])
    ]
  ]

-- Malformed: (indent) with no second argument should error, not crash.
/-- info: error: Error decoding indent expects at least 2 arguments -/
#guard_msgs in
#eval do
  let bs := Ion.internAndSerialize [indentTestDialect (.sexp #[.symbol "indent"])]
  match FromIon.deserialize (α := Dialect) bs with
  | .error msg => IO.println s!"error: {msg}"
  | .ok _      => IO.println "unexpected ok"

-- Successful empty tail: (indent 0) → .indent 0 #[]
/-- info: ok -/
#guard_msgs in
#eval do
  let bs := Ion.internAndSerialize [indentTestDialect (.sexp #[.symbol "indent", .int 0])]
  match FromIon.deserialize (α := Dialect) bs with
  | .error msg => IO.println s!"error: {msg}"
  | .ok _      => IO.println "ok"

-- Successful with inner atoms: (indent 2 "x") → .indent 2 #[.str "x"]
/-- info: ok -/
#guard_msgs in
#eval do
  let bs := Ion.internAndSerialize [indentTestDialect (.sexp #[.symbol "indent", .int 2, .string "x"])]
  match FromIon.deserialize (α := Dialect) bs with
  | .error msg => IO.println s!"error: {msg}"
  | .ok _      => IO.println "ok"

-- Wrong type at args[1]: (indent "notnum") should produce asNat error.
/-- info: error: Error decoding Expected SyntaxDef indent value to be a nat instead of { app := Ion.IonF.string "notnum" }. -/
#guard_msgs in
#eval do
  let bs := Ion.internAndSerialize [indentTestDialect (.sexp #[.symbol "indent", .string "notnum"])]
  match FromIon.deserialize (α := Dialect) bs with
  | .error msg => IO.println s!"error: {msg}"
  | .ok _      => IO.println "unexpected ok"

-- SourceRange round-trip: null encodes as (0, 0)
#guard
  let bs := Ion.serialize #[Ion.SymbolTable.system.localSymbolTableValue, Ion.null (Sym := Ion.SymbolId)]
  match FromIon.deserialize (α := SourceRange) bs with
  | .error _ => false
  | .ok r => r == { start := ⟨0⟩, stop := ⟨0⟩ }

-- SourceRange round-trip: sexp with start/stop
#guard
  let bs := Ion.serialize #[Ion.SymbolTable.system.localSymbolTableValue,
    Ion.sexp (Sym := Ion.SymbolId) #[.int 10, .int 42]]
  match FromIon.deserialize (α := SourceRange) bs with
  | .error _ => false
  | .ok r => r == { start := ⟨10⟩, stop := ⟨42⟩ }

-- Test that SourceRange.fromIon error message says "Source range" (not "Source rang")
#guard
  let bs := Ion.serialize #[Ion.SymbolTable.system.localSymbolTableValue, Ion.string (Sym := Ion.SymbolId) "bad"]
  match FromIon.deserialize (α := SourceRange) bs with
  | .error msg => "Error decoding Source range".isPrefixOf msg
  | .ok _ => false
