/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Integration.Lean
public import Strata.Languages.Python.Specs.Decls

import Strata.DDM.AST
import Strata.DDM.Util.ByteArray
import Strata.DDM.Format
import Strata.DDM.BuiltinDialects.Init
public import Strata.DDM.Integration.Lean.OfAstM
import Strata.DDM.Ion

public section

namespace Strata.Python

/-- Converts a Python identifier to an annotated string for DDM serialization. -/
private def PythonIdent.toDDM (d : PythonIdent) : Ann String SourceRange :=
  ⟨.none, toString d⟩

namespace Specs
namespace DDM

#dialect
dialect PythonSpecs;

category Int;
op natInt (x : Num) : Int => x;
op negInt (x : Num) : Int => "-" x;

category SpecType;
category DictFieldDecl;

op typeIdentNoArgs (x : Str) : SpecType => "ident" "(" x ")";
op typeIdent (x : Str, y : CommaSepBy SpecType) : SpecType =>
  "ident" "(" x ", " y ")";
op typeClassNoArgs (x : Ident) : SpecType => "class" "(" x ")";
op typeClass (x : Ident, y : CommaSepBy SpecType) : SpecType =>
  "class" "(" x ", " y ")";
op typeIntLiteral (x : Int) : SpecType => x;
op typeStringLiteral (x : Str) : SpecType => x;
op typeUnion (args : CommaSepBy SpecType) : SpecType =>
  "union" "(" args ")";
op typeTypedDict (fields : NewlineSepBy DictFieldDecl): SpecType =>
  "dict" "(\n" indent(2, fields) ")";

op mkDictFieldDecl(name : Ident, fieldType : SpecType, isRequired : Bool) : DictFieldDecl =>
  name " : " fieldType " [required=" isRequired "]";

category ClassFieldDecl;
op mkClassFieldDecl(name : Ident, fieldType : SpecType, constValue : Option Str) : ClassFieldDecl =>
  name " : " fieldType constValue "\n";

category ClassVarDecl;
op mkClassVarDecl(name : Ident, value : Ident) : ClassVarDecl =>
  name " = " value "\n";

category SpecDefault;
op noneDefault() : SpecDefault => "None";

category ArgDecl;
op mkArgDecl (name : Ident, argType : SpecType, argDefault : Option SpecDefault) : ArgDecl =>
  name " : " argType " [" "default" ": " argDefault "]\n";

category KwargsDecl;
op mkKwargsDecl(name : Ident, kwargsType : SpecType) : KwargsDecl =>
  "kwargs" ": " name " : " kwargsType "\n";

category SpecExprDecl;
op placeholderExpr() : SpecExprDecl => "placeholder";
op varExpr(name : Ident) : SpecExprDecl => name;
op getIndexExpr(subject : SpecExprDecl, field : Ident) : SpecExprDecl =>
  @[prec(50)] subject "[" field "]";
op isInstanceOfExpr(subject : SpecExprDecl, typeName : Str) : SpecExprDecl =>
  "isinstance" "(" subject ", " typeName ")";
op lenExpr(subject : SpecExprDecl) : SpecExprDecl =>
  "len" "(" subject ")";
op intExpr(value : Int) : SpecExprDecl => value;
op intGeExpr(subject : SpecExprDecl, bound : SpecExprDecl) : SpecExprDecl =>
  @[prec(15)] subject " >=_int " bound;
op intLeExpr(subject : SpecExprDecl, bound : SpecExprDecl) : SpecExprDecl =>
  @[prec(15)] subject " <=_int " bound;
op floatExpr(value : Str) : SpecExprDecl => value;
op floatGeExpr(subject : SpecExprDecl, bound : SpecExprDecl) : SpecExprDecl =>
  @[prec(15)] subject " >=_float " bound;
op floatLeExpr(subject : SpecExprDecl, bound : SpecExprDecl) : SpecExprDecl =>
  @[prec(15)] subject " <=_float " bound;
op enumMemberExpr(subject : SpecExprDecl, values : Seq Str) : SpecExprDecl =>
  "enum" "(" subject ", [" values "]" ")";
op regexMatchExpr(subject : SpecExprDecl, pattern : Str) : SpecExprDecl =>
  "regex" "(" subject ", " pattern ")";
op containsKeyExpr(container : SpecExprDecl, key : Ident) : SpecExprDecl =>
  @[prec(15)] key " in " container;
op impliesExpr(condition : SpecExprDecl, body : SpecExprDecl) : SpecExprDecl =>
  @[prec(10), rightassoc] condition " => " body;
op notExpr(e : SpecExprDecl) : SpecExprDecl =>
  "not" "(" e ")";
op forallListExpr(list : SpecExprDecl, varName : Ident, body : SpecExprDecl) : SpecExprDecl =>
  "forall" "(" list ", " varName ", " body ")";
op forallDictExpr(dict : SpecExprDecl, keyVar : Ident,
    valVar : Ident, body : SpecExprDecl) : SpecExprDecl =>
  "forallDict" "(" dict ", " keyVar ", " valVar ", " body ")";

category MessagePart;
op strMessagePart(s : Str) : MessagePart => s;
op exprMessagePart(e : SpecExprDecl) : MessagePart => "{" e "}";

category Assertion;
op mkAssertion(formula : SpecExprDecl, message : Seq MessagePart) : Assertion =>
  "ensure" "(" formula ", " message ")\n";

category PostconditionEntry;
op mkPostconditionEntry(expr : SpecExprDecl) : PostconditionEntry =>
  expr "\n";

category FunDecl;
op mkFunDecl (name : Str,
              args : Seq ArgDecl,
              kwonly : Seq ArgDecl,
              kwargs : Option KwargsDecl,
              returnType : SpecType,
              isOverload : Bool,
              preconditions : Seq Assertion,
              postconditions : Seq PostconditionEntry)
    : FunDecl =>
  "function " name "{\n"
  indent(2,
    "args" ": " "[\n"
    indent(2, args)
    "]\n"
    "kwonly" ": " "[\n"
    indent(2, kwonly)
    "]\n"
    kwargs
    "return" ": " returnType "\n"
    "overload" ": " isOverload "\n"
    "preconditions" ": " "[\n"
    indent(2, preconditions)
    "]\n"
    "postconditions" ": " "[\n"
    indent(2, postconditions)
    "]\n")
  "}\n";

category ClassDecl;
op mkClassDecl(name : Str, bases : Seq Str,
    fields : Seq ClassFieldDecl,
    classVars : Seq ClassVarDecl,
    subclasses : Seq ClassDecl,
    methods : Seq FunDecl) : ClassDecl =>
  "class " name " {\n"
  indent(2,
    "bases" ": " "[" bases "]\n"
    "fields" ": " "[\n"
    indent(2, fields)
    "]\n"
    "classVars" ": " "[\n"
    indent(2, classVars)
    "]\n"
    "subclasses" ": " "[\n"
    indent(2, subclasses)
    "]\n"
    methods)
  "}\n";

op externTypeDecl (name : Str, source : Str) : Command =>
  "extern " name " from " source ";\n";
op classDef (decl : ClassDecl) : Command => decl;
op functionDecl (decl : FunDecl) : Command => decl;
op typeDef (name : Str, definition : SpecType) : Command =>
  "type " name " = " definition "\n";
#end

#strata_gen PythonSpecs

abbrev Signature := Command

end DDM

/-- Converts a Lean `Int` to the DDM representation which separates natural and negative cases. -/
def toDDMInt {α} (ann : α) (i : Int) : DDM.Int α :=
  match i with
  | .ofNat n => .natInt ann ⟨ann, n⟩
  | .negSucc n => .negInt ann ⟨ann, (n+1)⟩

def DDM.Int.ofDDM {α} : DDM.Int α → _root_.Int
| .natInt _ ⟨_, n⟩ => .ofNat n
| .negInt _ ⟨_, 0⟩ => 0
| .negInt _ ⟨_, n+1⟩ => .negSucc n

mutual

private def SpecAtomType.toDDM (d : SpecAtomType)
    (loc : SourceRange := .none) : DDM.SpecType SourceRange :=
  match d with
  | .ident nm args =>
    if args.isEmpty then
      .typeIdentNoArgs loc nm.toDDM
    else
      .typeIdent loc nm.toDDM ⟨.none, args.map (·.toDDM)⟩
  | .pyClass name args =>
    if args.isEmpty then
      .typeClassNoArgs loc ⟨.none, name⟩
    else
      .typeClass loc ⟨.none, name⟩ ⟨.none, args.map (·.toDDM)⟩
  | .intLiteral i => .typeIntLiteral loc (toDDMInt .none i)
  | .stringLiteral v => .typeStringLiteral loc ⟨.none, v⟩
  | .typedDict fields types fieldRequired =>
    assert! fields.size = types.size
    let argc := types.size
    let a := Array.ofFn fun (⟨i, ilt⟩ : Fin argc) =>
      .mkDictFieldDecl .none ⟨.none, fields[i]!⟩ types[i].toDDM ⟨.none, fieldRequired[i]!⟩
    .typeTypedDict loc ⟨.none, a⟩
termination_by sizeOf d

private def SpecType.toDDM (d : SpecType) : DDM.SpecType SourceRange :=
  assert! d.atoms.size > 0
  if p : d.atoms.size = 1 then
    d.atoms[0].toDDM (loc := d.loc)
  else
    .typeUnion d.loc ⟨.none, d.atoms.map (·.toDDM)⟩
termination_by sizeOf d
decreasing_by
  all_goals {
    cases d
    decreasing_tactic
  }

end

private def SpecDefault.toDDM : Specs.SpecDefault → DDM.SpecDefault SourceRange
  | .none => .noneDefault .none

private def Arg.toDDM (d : Arg) : DDM.ArgDecl SourceRange :=
  .mkArgDecl .none ⟨.none, d.name⟩ d.type.toDDM ⟨.none, d.default.map (·.toDDM)⟩

private def SpecExpr.toDDM (e : SpecExpr) : DDM.SpecExprDecl SourceRange :=
  match e with
  | .placeholder => .placeholderExpr .none
  | .var name => .varExpr .none ⟨.none, name⟩
  | .getIndex subj field => .getIndexExpr .none subj.toDDM ⟨.none, field⟩
  | .isInstanceOf subj tn => .isInstanceOfExpr .none subj.toDDM ⟨.none, tn⟩
  | .len subj => .lenExpr .none subj.toDDM
  | .intLit v => .intExpr .none (toDDMInt .none v)
  | .intGe subj bound => .intGeExpr .none subj.toDDM bound.toDDM
  | .intLe subj bound => .intLeExpr .none subj.toDDM bound.toDDM
  | .floatLit v => .floatExpr .none ⟨.none, v⟩
  | .floatGe subj bound => .floatGeExpr .none subj.toDDM bound.toDDM
  | .floatLe subj bound => .floatLeExpr .none subj.toDDM bound.toDDM
  | .enumMember subj values =>
    .enumMemberExpr .none subj.toDDM
      ⟨.none, values.map (⟨.none, ·⟩)⟩
  | .regexMatch subj pattern =>
    .regexMatchExpr .none subj.toDDM ⟨.none, pattern⟩
  | .containsKey container key =>
    .containsKeyExpr .none container.toDDM ⟨.none, key⟩
  | .implies cond body =>
    .impliesExpr .none cond.toDDM body.toDDM
  | .not e => .notExpr .none e.toDDM
  | .forallList list varName body =>
    .forallListExpr .none list.toDDM ⟨.none, varName⟩ body.toDDM
  | .forallDict dict keyVar valVar body =>
    .forallDictExpr .none dict.toDDM ⟨.none, keyVar⟩ ⟨.none, valVar⟩ body.toDDM

private def MessagePart.toDDM (p : MessagePart) : DDM.MessagePart SourceRange :=
  match p with
  | .str s => .strMessagePart .none ⟨.none, s⟩
  | .expr e => .exprMessagePart .none e.toDDM

private def Assertion.toDDM (a : Assertion) : DDM.Assertion SourceRange :=
  .mkAssertion .none a.formula.toDDM ⟨.none, a.message.map (·.toDDM)⟩

private def FunctionDecl.toDDM (d : FunctionDecl) : DDM.FunDecl SourceRange :=
  .mkFunDecl
    d.loc
    (name := .mk d.nameLoc d.name)
    (args := ⟨.none, d.args.args.map (·.toDDM)⟩)
    (kwonly := ⟨.none, d.args.kwonly.map (·.toDDM)⟩)
    (kwargs := ⟨.none, match d.args.kwargs with
      | none => none
      | some (name, tp) =>
        some (.mkKwargsDecl .none ⟨.none, name⟩ tp.toDDM)⟩)
    (returnType := d.returnType.toDDM)
    (isOverload := ⟨.none, d.isOverload⟩)
    (preconditions := ⟨.none, d.preconditions.map (·.toDDM)⟩)
    (postconditions := ⟨.none,
      d.postconditions.map fun e =>
        .mkPostconditionEntry .none e.toDDM⟩)

private def ClassVariable.toDDM (cv : ClassVariable) : DDM.ClassVarDecl SourceRange :=
  .mkClassVarDecl .none ⟨.none, cv.name⟩ ⟨.none, cv.value⟩

private partial def ClassDef.toDDMDecl (d : ClassDef) : DDM.ClassDecl SourceRange :=
  .mkClassDecl d.loc (.mk .none d.name)
    ⟨.none, d.bases.map (·.toDDM)⟩
    ⟨.none, d.fields.map fun f =>
      .mkClassFieldDecl .none ⟨.none, f.name⟩ f.type.toDDM
        ⟨.none, f.constValue.map (⟨.none, ·⟩)⟩⟩
    ⟨.none, d.classVars.map (·.toDDM)⟩
    ⟨.none, d.subclasses.map (·.toDDMDecl)⟩
    ⟨.none, d.methods.map (·.toDDM)⟩

private def Signature.toDDM (sig : Signature) : DDM.Signature SourceRange :=
  match sig with
  | .externTypeDecl name source =>
    .externTypeDecl .none ⟨.none, name⟩ source.toDDM
  | .classDef d =>
    .classDef d.loc d.toDDMDecl
  | .functionDecl d =>
    .functionDecl d.loc d.toDDM
  | .typeDef d =>
    .typeDef d.loc (.mk d.nameLoc d.name) d.definition.toDDM

private def DDM.SpecType.fromDDM (d : DDM.SpecType SourceRange) : Specs.SpecType :=
  match d with
  | .typeClassNoArgs loc ⟨_, cl⟩ =>
    .ofAtom loc <| .pyClass cl #[]
  | .typeClass loc ⟨_, cl⟩ ⟨_, args⟩ =>
    let a := args.map (·.fromDDM)
    .ofAtom loc <| .pyClass cl a
  | .typeIdentNoArgs loc ⟨_, ident⟩ =>
    if let some pyIdent := PythonIdent.ofString ident then
      .ident loc pyIdent #[]
    else
      panic! "Bad identifier"
  | .typeIdent loc ⟨_, ident⟩ ⟨_, args⟩ =>
    let a := args.map (·.fromDDM)
    if let some pyIdent := PythonIdent.ofString ident then
      .ident loc pyIdent a
    else
      panic! "Bad identifier"
  | .typeIntLiteral loc i => .ofAtom loc <| .intLiteral i.ofDDM
  | .typeStringLiteral loc ⟨_, s⟩ => .ofAtom loc <| .stringLiteral s
  | .typeTypedDict loc ⟨_, fields⟩ =>
    let names := fields.map fun (.mkDictFieldDecl _ ⟨_, name⟩ _ _) => name
    let types := fields.attach.map fun ⟨.mkDictFieldDecl _ _ tp _, mem⟩ => tp.fromDDM
    let required := fields.map fun (.mkDictFieldDecl _ _ _ ⟨_, r⟩) => r
    .ofAtom loc <| .typedDict names types required
  | .typeUnion loc ⟨_, args⟩ =>
    if p : args.size > 0 then
      args.attach.foldl (init := args[0].fromDDM) (start := 1)
        fun a ⟨b, mem⟩ => SpecType.union loc a b.fromDDM
    else
      panic! "Expected non-empty union"
termination_by sizeOf d
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · rename_i _ ann nm req
    have szp : 1 + sizeOf ann + sizeOf nm + sizeOf tp + sizeOf req < sizeOf fields :=
       Array.sizeOf_lt_of_mem mem
    decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

private def DDM.SpecDefault.fromDDM : DDM.SpecDefault SourceRange → Specs.SpecDefault
  | .noneDefault _ => .none

private def DDM.ArgDecl.fromDDM (d : DDM.ArgDecl SourceRange) : Specs.Arg :=
  let .mkArgDecl _ ⟨_, name⟩ type ⟨_, default⟩ := d
  {
    name := name
    type := type.fromDDM
    default := default.map (·.fromDDM)
  }

private def DDM.SpecExprDecl.fromDDM (d : DDM.SpecExprDecl SourceRange) : Specs.SpecExpr :=
  match d with
  | .placeholderExpr _ => .placeholder
  | .varExpr _ ⟨_, name⟩ => .var name
  | .getIndexExpr _ subj ⟨_, field⟩ => .getIndex subj.fromDDM field
  | .isInstanceOfExpr _ subj ⟨_, tn⟩ => .isInstanceOf subj.fromDDM tn
  | .lenExpr _ subj => .len subj.fromDDM
  | .intExpr _ i => .intLit i.ofDDM
  | .intGeExpr _ subj bound => .intGe subj.fromDDM bound.fromDDM
  | .intLeExpr _ subj bound => .intLe subj.fromDDM bound.fromDDM
  | .floatExpr _ ⟨_, v⟩ => .floatLit v
  | .floatGeExpr _ subj bound => .floatGe subj.fromDDM bound.fromDDM
  | .floatLeExpr _ subj bound => .floatLe subj.fromDDM bound.fromDDM
  | .enumMemberExpr _ subj ⟨_, values⟩ => .enumMember subj.fromDDM (values.map (·.2))
  | .regexMatchExpr _ subj ⟨_, pattern⟩ => .regexMatch subj.fromDDM pattern
  | .containsKeyExpr _ container ⟨_, key⟩ => .containsKey container.fromDDM key
  | .impliesExpr _ cond body => .implies cond.fromDDM body.fromDDM
  | .notExpr _ e => .not e.fromDDM
  | .forallListExpr _ list ⟨_, varName⟩ body =>
    .forallList list.fromDDM varName body.fromDDM
  | .forallDictExpr _ dict ⟨_, keyVar⟩ ⟨_, valVar⟩ body =>
    .forallDict dict.fromDDM keyVar valVar body.fromDDM

private def DDM.MessagePart.fromDDM (d : DDM.MessagePart SourceRange) : Specs.MessagePart :=
  match d with
  | .strMessagePart _ ⟨_, s⟩ => .str s
  | .exprMessagePart _ e => .expr e.fromDDM

private def DDM.Assertion.fromDDM (d : DDM.Assertion SourceRange) : Specs.Assertion :=
  let .mkAssertion _ formula ⟨_, message⟩ := d
  { message := message.map (·.fromDDM), formula := formula.fromDDM }

private def DDM.FunDecl.fromDDM (d : DDM.FunDecl SourceRange) : Specs.FunctionDecl :=
  let .mkFunDecl loc ⟨nameLoc, name⟩ ⟨_, args⟩ ⟨_, kwonly⟩
                 ⟨_, kwargs⟩ returnType ⟨_, isOverload⟩
                 ⟨_, preconditions⟩ ⟨_, postconditions⟩ := d
  let kwargsOpt : Option (String × Specs.SpecType) :=
    match kwargs with
    | some (.mkKwargsDecl _ ⟨_, kn⟩ tp) => some (kn, tp.fromDDM)
    | none => none
  {
    loc := loc
    nameLoc := nameLoc
    name := name
    args := {
      args := args.map (·.fromDDM)
      kwonly := kwonly.map (·.fromDDM)
      kwargs := kwargsOpt
    }
    returnType := returnType.fromDDM
    isOverload := isOverload
    preconditions := preconditions.map (·.fromDDM)
    postconditions := postconditions.map fun
      | .mkPostconditionEntry _ e => e.fromDDM
  }

private def DDM.ClassDecl.fromDDM (d : DDM.ClassDecl SourceRange) : Specs.ClassDef :=
  let .mkClassDecl ann ⟨_, name⟩ ⟨_, bases⟩ ⟨_, fields⟩
    ⟨_, classVars⟩ ⟨_, subclasses⟩ ⟨_, methods⟩ := d
  {
    loc := ann
    name := name
    bases := bases.map fun ⟨_, s⟩ =>
      match PythonIdent.ofString s with
      | some id => id
      | none => panic! s!"Bad base class identifier: '{s}'"
    fields := fields.map fun (.mkClassFieldDecl _ ⟨_, n⟩ tp ⟨_, cv⟩) =>
      { name := n, type := tp.fromDDM, constValue := cv.map (·.2) : ClassField }
    classVars := classVars.map fun (.mkClassVarDecl _ ⟨_, n⟩ ⟨_, v⟩) =>
      { name := n, value := v : ClassVariable }
    subclasses := subclasses.map (·.fromDDM)
    methods := methods.map (·.fromDDM)
  }

private def DDM.Command.fromDDM (cmd : DDM.Command SourceRange) : Specs.Signature :=
  match cmd with
  | .externTypeDecl _ ⟨_, name⟩ ⟨_, ddmDefinition⟩ =>
    if let some definition := PythonIdent.ofString ddmDefinition then
      .externTypeDecl name definition
    else
      panic! "Extern type decl definition has bad format."
  | .classDef _ decl =>
    .classDef decl.fromDDM
  | .functionDecl _ d => .functionDecl d.fromDDM
  | .typeDef loc ⟨nameLoc, name⟩ definition =>
    let d : TypeDef := {
      loc := loc
      nameLoc := nameLoc
      name := name
      definition := definition.fromDDM
    }
    .typeDef d

/-- Reads Python spec signatures from a DDM Ion file. -/
def readDDM (path : System.FilePath) : EIO String (Array Signature) := do
  let contents ←
        match ← IO.FS.readBinFile path |>.toBaseIO with
        | .ok r => pure r
        | .error msg => throw s!"Error reading {path}: {msg}"
  match Program.fromIon DDM.PythonSpecs_map DDM.PythonSpecs.name contents with
  | .ok pgm =>
    let r :=
          pgm.commands.mapM fun cmd => do
            let pySig ← DDM.Command.ofAst cmd
            return pySig.fromDDM
    match r with
    | .ok r => pure r
    | .error msg => throw msg
  | .error msg => throw msg

/-- Converts Python spec signatures to a DDM program for serialization. -/
def toDDMProgram (sigs : Array Signature) : Strata.Program := {
    dialects := DDM.PythonSpecs_map
    dialect := DDM.PythonSpecs.name
    commands := sigs.map fun s => s.toDDM.toAst
  }

/-- Writes Python spec signatures to a DDM Ion file. -/
def writeDDM (path : System.FilePath) (sigs : Array Signature) : IO Unit := do
  let pgm := toDDMProgram sigs
  IO.FS.writeBinFile path <| pgm.toIon

end Strata.Python.Specs
end
