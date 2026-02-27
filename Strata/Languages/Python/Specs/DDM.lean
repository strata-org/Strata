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
namespace Strata.Python.Specs
namespace DDM

#dialect
dialect PythonSpecs;

category Int;
op natInt (x : Num) : Int => x;
op negSuccInt (x : Num) : Int => "-" x;

category SpecType;
category DictFieldDecl;

op typeIdentNoArgs (x : Str) : SpecType => "ident" "(" x ")";
op typeIdent (x : Str, y : CommaSepBy SpecType) : SpecType => "ident" "(" x ", " y ")";
op typeClassNoArgs (x : Ident) : SpecType => "class" "(" x ")";
op typeClass (x : Ident, y : CommaSepBy SpecType) : SpecType => "class" "(" x ", " y ")";
op typeIntLiteral (x : Int) : SpecType => x;
op typeStringLiteral (x : Str) : SpecType => x;
op typeUnion (args : CommaSepBy SpecType) : SpecType => "union" "(" args ")";
op typeTypedDict (fields : CommaSepBy DictFieldDecl): SpecType =>
  "dict" "(" fields ")";

op mkDictFieldDecl(name : Ident, fieldType : SpecType, isRequired : Bool) : DictFieldDecl =>
  name " : " fieldType " [required=" isRequired "]";

category ClassFieldDecl;
op mkClassFieldDecl(name : Ident, fieldType : SpecType) : ClassFieldDecl =>
  name " : " fieldType "\n";

category ClassVarDecl;
op mkClassVarDecl(name : Ident, value : Ident) : ClassVarDecl =>
  name " = " value "\n";


category ArgDecl;
op mkArgDecl (name : Ident, argType : SpecType, hasDefault : Bool) : ArgDecl =>
  name " : " argType " [" "hasDefault" ": " hasDefault "]\n";

category KwargsDecl;
op mkKwargsDecl(name : Ident, kwargsType : SpecType) : KwargsDecl =>
  "kwargs " name " : " kwargsType "\n";

category SpecExprDecl;
op placeholderExpr() : SpecExprDecl =>
  "placeholder" "\n";
op varExpr(name : Ident) : SpecExprDecl =>
  name "\n";
op getIndexExpr(subject : SpecExprDecl, field : Ident) : SpecExprDecl =>
  subject "[" field "]" "\n";
op isInstanceOfExpr(subject : SpecExprDecl, typeName : Str) : SpecExprDecl =>
  "isinstance(" subject ", " typeName ")" "\n";
op lenGeExpr(subject : SpecExprDecl, bound : Num) : SpecExprDecl =>
  "len_ge(" subject ", " bound ")" "\n";
op lenLeExpr(subject : SpecExprDecl, bound : Num) : SpecExprDecl =>
  "len_le(" subject ", " bound ")" "\n";
op valueGeExpr(subject : SpecExprDecl, bound : Int) : SpecExprDecl =>
  "value_ge(" subject ", " bound ")" "\n";
op valueLeExpr(subject : SpecExprDecl, bound : Int) : SpecExprDecl =>
  "value_le(" subject ", " bound ")" "\n";
op enumMemberExpr(subject : SpecExprDecl, values : Seq Str) : SpecExprDecl =>
  "enum(" subject ", [" values "])" "\n";

category Assertion;
op mkAssertion(formula : SpecExprDecl, message : Str) : Assertion =>
  formula " " message "\n";

category FunDecl;
op mkFunDecl (name : Str,
              args : Seq ArgDecl,
              kwonly : Seq ArgDecl,
              kwargs : Seq KwargsDecl,
              returnType : SpecType,
              isOverload : Bool,
              preconditions : Seq Assertion,
              postconditions : Seq SpecExprDecl) : FunDecl =>
  "function " name "{\n"
  indent(2,
    "args" ": " "[\n"
    indent(2, args)
    "]\n"
    "kwonly" ": " "[\n"
    indent(2, kwonly)
    "]\n"
    "kwargs" ": " "[\n"
    indent(2, kwargs)
    "]\n"
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
op mkClassDecl(name : Str, bases : Seq Str, fields : Seq ClassFieldDecl,
               classVars : Seq ClassVarDecl, subclasses : Seq ClassDecl,
               methods : Seq FunDecl) : ClassDecl =>
  "class " name " {\n"
  indent(2,
    "bases" ": " "[" bases "]\n"
    "fields" ": " "[" fields "]\n"
    "classVars" ": " "[" classVars "]\n"
    "subclasses" ": " "[" subclasses "]\n"
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

/-- Converts a Python identifier to an annotated string for DDM serialization. -/
private def PythonIdent.toDDM (d : PythonIdent) : Ann String SourceRange :=
  ⟨.none, toString d⟩

/-- Converts a Lean `Int` to the DDM representation which separates natural and negative cases. -/
private def toDDMInt {α} (ann : α) (i : Int) : DDM.Int α :=
  match i with
  | .ofNat n => .natInt ann ⟨ann, n⟩
  | .negSucc n => .negSuccInt ann ⟨ann, n⟩

private def DDM.Int.ofDDM : DDM.Int α → _root_.Int
| .natInt _ ⟨_, n⟩ => .ofNat n
| .negSuccInt _ ⟨_, n⟩ => .negSucc n

mutual

private def SpecAtomType.toDDM (d : SpecAtomType) (loc : SourceRange := .none) : DDM.SpecType SourceRange :=
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

private def Arg.toDDM (d : Arg) : DDM.ArgDecl SourceRange :=
  .mkArgDecl .none ⟨.none, d.name⟩ d.type.toDDM ⟨.none, d.hasDefault⟩

private def SpecExpr.toDDM (e : SpecExpr) : DDM.SpecExprDecl SourceRange :=
  match e with
  | .placeholder => .placeholderExpr .none
  | .var name => .varExpr .none ⟨.none, name⟩
  | .getIndex subj field => .getIndexExpr .none subj.toDDM ⟨.none, field⟩
  | .isInstanceOf subj tn => .isInstanceOfExpr .none subj.toDDM ⟨.none, tn⟩
  | .lenGe subj bound => .lenGeExpr .none subj.toDDM ⟨.none, bound⟩
  | .lenLe subj bound => .lenLeExpr .none subj.toDDM ⟨.none, bound⟩
  | .valueGe subj bound => .valueGeExpr .none subj.toDDM (toDDMInt .none bound)
  | .valueLe subj bound => .valueLeExpr .none subj.toDDM (toDDMInt .none bound)
  | .enumMember subj values => .enumMemberExpr .none subj.toDDM ⟨.none, values.map (⟨.none, ·⟩)⟩

private def Assertion.toDDM (a : Assertion) : DDM.Assertion SourceRange :=
  .mkAssertion .none a.formula.toDDM ⟨.none, a.message⟩

private def FunctionDecl.toDDM (d : FunctionDecl) : DDM.FunDecl SourceRange :=
  .mkFunDecl
    d.loc
    (name := .mk d.nameLoc d.name)
    (args := ⟨.none, d.args.args.map (·.toDDM)⟩)
    (kwonly := ⟨.none, d.args.kwonly.map (·.toDDM)⟩)
    (kwargs := ⟨.none, match d.args.kwargs with
      | none => #[]
      | some (name, tp) => #[.mkKwargsDecl .none ⟨.none, name⟩ tp.toDDM]⟩)
    (returnType := d.returnType.toDDM)
    (isOverload := ⟨.none, d.isOverload⟩)
    (preconditions := ⟨.none, d.preconditions.map (·.toDDM)⟩)
    (postconditions := ⟨.none, d.postconditions.map (·.toDDM)⟩)

private def ClassVariable.toDDM (cv : ClassVariable) : DDM.ClassVarDecl SourceRange :=
  .mkClassVarDecl .none ⟨.none, cv.name⟩ ⟨.none, cv.value⟩

private partial def ClassDef.toDDMDecl (d : ClassDef) : DDM.ClassDecl SourceRange :=
  .mkClassDecl d.loc (.mk .none d.name)
    ⟨.none, d.bases.map (·.toDDM)⟩
    ⟨.none, d.fields.map fun f =>
      .mkClassFieldDecl .none ⟨.none, f.name⟩ f.type.toDDM⟩
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

private def DDM.ArgDecl.fromDDM (d : DDM.ArgDecl SourceRange) : Specs.Arg :=
  let .mkArgDecl _ ⟨_, name⟩ type ⟨_, hasDefault⟩ := d
  {
    name := name
    type := type.fromDDM
    hasDefault := hasDefault
  }

private def DDM.SpecExprDecl.fromDDM (d : DDM.SpecExprDecl SourceRange) : Specs.SpecExpr :=
  match d with
  | .placeholderExpr _ => .placeholder
  | .varExpr _ ⟨_, name⟩ => .var name
  | .getIndexExpr _ subj ⟨_, field⟩ => .getIndex subj.fromDDM field
  | .isInstanceOfExpr _ subj ⟨_, tn⟩ => .isInstanceOf subj.fromDDM tn
  | .lenGeExpr _ subj ⟨_, bound⟩ => .lenGe subj.fromDDM bound
  | .lenLeExpr _ subj ⟨_, bound⟩ => .lenLe subj.fromDDM bound
  | .valueGeExpr _ subj bound => .valueGe subj.fromDDM bound.ofDDM
  | .valueLeExpr _ subj bound => .valueLe subj.fromDDM bound.ofDDM
  | .enumMemberExpr _ subj ⟨_, values⟩ => .enumMember subj.fromDDM (values.map (·.2))

private def DDM.Assertion.fromDDM (d : DDM.Assertion SourceRange) : Specs.Assertion :=
  let .mkAssertion _ formula ⟨_, message⟩ := d
  { message := message, formula := formula.fromDDM }

private def DDM.FunDecl.fromDDM (d : DDM.FunDecl SourceRange) : Specs.FunctionDecl :=
  let .mkFunDecl loc ⟨nameLoc, name⟩ ⟨_, args⟩ ⟨_, kwonly⟩ ⟨_, kwargs⟩
                 returnType ⟨_, isOverload⟩ ⟨_, preconditions⟩
                 ⟨_, postconditions⟩ := d
  let kwargsOpt : Option (String × Specs.SpecType) :=
    if h : kwargs.size > 0 then
      let .mkKwargsDecl _ ⟨_, kn⟩ tp := kwargs[0]
      some (kn, tp.fromDDM)
    else none
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
    postconditions := postconditions.map (·.fromDDM)
  }

private partial def DDM.ClassDecl.fromDDM (d : DDM.ClassDecl SourceRange) : Specs.ClassDef :=
  let .mkClassDecl ann ⟨_, name⟩ ⟨_, bases⟩ ⟨_, fields⟩ ⟨_, classVars⟩ ⟨_, subclasses⟩ ⟨_, methods⟩ := d
  {
    loc := ann
    name := name
    bases := bases.filterMap fun ⟨_, s⟩ => PythonIdent.ofString s
    fields := fields.map fun (.mkClassFieldDecl _ ⟨_, n⟩ tp) =>
      { name := n, type := tp.fromDDM : ClassField }
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
